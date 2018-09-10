section {*LR1\_Property\_Satisfaction\_\_compute\_latest\_production*}
theory
  LR1_Property_Satisfaction__compute_latest_production

imports
  PRJ_12_04_06_06_12__ENTRY

begin

declare [[ hypsubst_thin = false ]]
datatype DT_revert_position =
  elim "nat"
  | gen "nat" "nat"
declare [[ hypsubst_thin = true ]]

definition Pident_line :: "
  ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "Pident_line S \<equiv>
  PSplitItem_prods S = []
  \<and> PSplitItem_elim S = []"

definition Pident_lines :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> nat set"
  where
    "Pident_lines S \<equiv>
  {n. n < length S \<and> Pident_line (S ! n)}"

definition first_empty_rhs :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label list
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label"
  where
    "first_empty_rhs w \<equiv>
  THE p.
      \<exists>i.
        w ! i = p
        \<and> prod_rhs p = []
        \<and> (\<forall>j < i. prod_rhs (w ! j) \<noteq> [])"

definition get_prod_at_DT_revert_position :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> DT_revert_position
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label"
  where
    "get_prod_at_DT_revert_position S rp \<equiv>
  case rp of
  elim n \<Rightarrow> first_empty_rhs (hd (PSplitItem_elim_prods (S ! n)))
  | gen n m \<Rightarrow> hd (filterB [PSplitItem_prods (S ! n) ! m])"

definition valid_DT_revert_position :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> DT_revert_position
  \<Rightarrow> bool"
  where
    "valid_DT_revert_position S rp \<equiv>
  case rp of
  elim n \<Rightarrow>
    n < length S
    \<and> PSplitItem_elim (S ! n) \<noteq> []
  | gen n m \<Rightarrow>
    n < length S
    \<and> m < length (PSplitItem_prods (S ! n))
    \<and> setA [PSplitItem_prods (S ! n) ! m] = {}"

definition before_ident_line :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "before_ident_line S n \<equiv>
  \<forall>i < n. \<not> Pident_line (S ! i)"

definition get_line :: "
  DT_revert_position
  \<Rightarrow> nat"
  where
    "get_line rp \<equiv>
  case rp of
  elim n \<Rightarrow> n
  | gen n m \<Rightarrow> n"

definition is_DT_revert_position :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> DT_revert_position
  \<Rightarrow> bool"
  where
    "is_DT_revert_position S rp \<equiv>
  valid_DT_revert_position S rp
  \<and> before_ident_line S (get_line rp)
  \<and> (case rp of
    elim n \<Rightarrow> True
    | gen n m \<Rightarrow> (
        let
          prod = get_prod_at_DT_revert_position S rp
        in
          (prod_rhs prod = [] \<and> Suc m < length (PSplitItem_prods (S ! n)))
          \<or> (Suc n \<in> Pident_lines S \<and> Suc m = length (PSplitItem_prods (S ! n)))))"

definition get_pos :: "
  DT_revert_position
  \<Rightarrow> nat"
  where
    "get_pos rp \<equiv>
  case rp of
  elim n \<Rightarrow> 0
  | gen n m \<Rightarrow> Suc m"

definition leq :: "
  DT_revert_position
  \<Rightarrow> DT_revert_position
  \<Rightarrow> bool"
  where
    "leq rp1 rp2 \<equiv>
  get_line rp1 < get_line rp2
  \<or> (get_line rp1 = get_line rp2
     \<and> get_pos rp1 \<le> get_pos rp2)"

definition get_DT_revert_position :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> DT_revert_position option"
  where
    "get_DT_revert_position S \<equiv>
  if \<exists>rp. is_DT_revert_position S rp
  then Some (THE rp.
                is_DT_revert_position S rp
                \<and> (\<forall>rp'. is_DT_revert_position S rp' \<longrightarrow> leq rp rp'))
  else None"

definition get_revert_prod :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label option"
  where
    "get_revert_prod S \<equiv>
  case get_DT_revert_position S of
  None \<Rightarrow> None
  | Some rp \<Rightarrow> Some (get_prod_at_DT_revert_position S rp)"

lemma get_DT_revert_position_eq: "
  is_DT_revert_position S rp
  \<Longrightarrow> (THE rp. is_DT_revert_position S rp \<and> (\<forall>rp'. is_DT_revert_position S rp' \<longrightarrow> leq rp rp')) = p
  \<Longrightarrow> get_DT_revert_position S = Some p"
  apply(simp add: get_DT_revert_position_def)
  apply(force)
  done

lemma leq_leq_eq: "
  leq x y
  \<Longrightarrow> leq y x
  \<Longrightarrow> x=y"
  apply(simp add: leq_def)
  apply(case_tac x)
   apply(rename_tac nat)(*strict*)
   apply(case_tac y)
    apply(rename_tac nat nata)(*strict*)
    apply(simp add: leq_def get_line_def get_pos_def)
    apply(clarsimp)
   apply(rename_tac nat nat1 nat2)(*strict*)
   apply(simp add: leq_def get_line_def get_pos_def)
  apply(rename_tac nat1 nat2)(*strict*)
  apply(case_tac y)
   apply(rename_tac nat1 nat2 nat)(*strict*)
   apply(simp add: leq_def get_line_def get_pos_def)
  apply(rename_tac nat1 nat2 nat1a nat2a)(*strict*)
  apply(clarsimp)
  apply(simp add: leq_def get_line_def get_pos_def)
  apply(force)
  done

lemma THE_get_DT_revert_position_eq: "
  is_DT_revert_position S rp
  \<Longrightarrow> (\<forall>rp'. is_DT_revert_position S rp' \<longrightarrow> leq rp rp')
  \<Longrightarrow> (THE rp. is_DT_revert_position S rp \<and> (\<forall>rp'. is_DT_revert_position S rp' \<longrightarrow> leq rp rp')) = rp"
  apply(rule the_equality)
   apply(force)
  apply(rename_tac rpa)(*strict*)
  apply(clarsimp)
  apply(rule leq_leq_eq)
   apply(rename_tac rpa)(*strict*)
   apply(force)
  apply(rename_tac rpa)(*strict*)
  apply(force)
  done

lemma get_DT_revert_position_eq2: "
  is_DT_revert_position S rp
  \<Longrightarrow> (is_DT_revert_position S rp \<Longrightarrow> (\<forall>rp'. is_DT_revert_position S rp' \<longrightarrow> leq rp rp'))
  \<Longrightarrow> get_DT_revert_position S = Some rp"
  apply(rule get_DT_revert_position_eq)
   apply(force)
  apply(rule THE_get_DT_revert_position_eq)
   apply(force)
  apply(force)
  done

lemma leq_gen_elim: "
  m<n
  \<Longrightarrow> leq (gen m x) (elim n)"
  apply(simp add: leq_def get_line_def get_pos_def)
  done

lemma first_empty_rhs_with_left_degen_front: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> c'
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> first_empty_rhs
           (\<pi> @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # w) = \<lparr>prod_lhs = A, prod_rhs = []\<rparr>"
  apply(simp add: first_empty_rhs_def)
  apply(rule the_equality)
   apply(rule_tac
      x="length \<pi>"
      in exI)
   apply(clarsimp)
   apply(rename_tac j)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac j)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and i="j"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac j)(*strict*)
      apply(force)
     apply(rename_tac j)(*strict*)
     apply(force)
    apply(rename_tac j)(*strict*)
    apply(force)
   apply(rename_tac j)(*strict*)
   apply(clarsimp)
   apply(rename_tac j e ci ci')(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac j e ci ci' l r)(*strict*)
   apply(simp add: left_degen_def)
   apply(simp add: sat_refined_def)
   apply(erule_tac
      x="j"
      in allE)
   apply(clarsimp)
   apply(rename_tac j e ci ci' l r wa Aa waa)(*strict*)
   apply (metis list.simps(2) nth_append_1)
  apply(rename_tac p)(*strict*)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i=length \<pi>")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i>length \<pi>")
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "i<length \<pi>")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="i"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci ci')(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e ci ci' l r)(*strict*)
  apply(simp add: left_degen_def)
  apply(simp add: sat_refined_def)
  apply(thin_tac "\<forall>j<i. prod_rhs ((\<pi> @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # w) ! j) \<noteq> []")
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i e ci ci' l r wa Aa waa)(*strict*)
  apply (metis list.simps(2) nth_append_1)
  done

lemma leq_elim_elim: "
  n\<le>m
  \<Longrightarrow> leq (elim n) (elim m)"
  apply(simp add: leq_def get_line_def get_pos_def)
  apply(force)
  done

lemma leq_elim_gen: "
  n\<le>m
  \<Longrightarrow> leq (elim n) (gen m x)"
  apply(simp add: leq_def get_line_def get_pos_def)
  apply(force)
  done

lemma get_revert_prod_sound_rhs_empty: "
       F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> Esplit_signature (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)) = r @ [teB b]
  \<Longrightarrow> setA (Esplit_signature Sb) = {}
  \<Longrightarrow> \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> \<in> cfg_productions G
  \<Longrightarrow> ESplitItem_elem SL = Some (teA (cons_l3   q1 X q2))
  \<Longrightarrow> length (Esplit_signature S1) = length S1
  \<Longrightarrow> ESplitItem_elem S2 = Some (teB b)
  \<Longrightarrow> length (nat_seq 0 (length S1)) = Suc (length S1)
  \<Longrightarrow> nat_seq 0 (length S1) ! length S1 = length S1
  \<Longrightarrow> r = []
  \<Longrightarrow> get_revert_prod (restrict G' G 
          (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb) (Suc (length S1 + length r))) 
  = Some \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr>"
  apply(simp add: Xstep_gen_def)
  apply(simp add: Xstep_mergeL_def Xstep_elem_def nth_opt_def)
  apply(case_tac SL)
  apply(rename_tac ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prodsa ESplitItem_elema ESplitItem_to)(*strict*)
  apply(clarsimp)
  apply(rename_tac ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_to)(*strict*)
  apply(rename_tac el fr ig el\<pi> \<pi> to)
  apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: Xstep_merge1_def)
  apply(rule conjI)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_toWasNotEliminated_def)
   apply(simp add: get_revert_prod_def)
   apply(subgoal_tac "get_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) = Some (gen (length S1) (length \<pi>))")
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: get_prod_at_DT_revert_position_def)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) (length S1) ! length \<pi>"
      and s="teB \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr>"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule nth_map)
     apply(rule_tac
      t="length (nat_seq 0 n)" for n
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="liftB (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2) ! length \<pi>"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule liftB_nth)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq 0 SSX ! SSY" for SSX SSY
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsXX_def)
    apply(subgoal_tac "derives G (\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2) = []")
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp add: strict_prefix_def option_to_list_def)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(rule_tac
      G="G"
      in derive_empty_if_first_prod_has_empty_rhs)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(subgoal_tac "EValidSplit_ValidItem G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb)")
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      prefer 2
      apply(simp add: EValidSplit_def)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_belongs_def)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(rule_tac
      rp="gen (length S1) (length \<pi>)"
      in get_DT_revert_position_eq2)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: is_DT_revert_position_def)
    apply(rule_tac
      t="before_ident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) (get_line (gen (length S1) (length \<pi>)))"
      and s="True"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp add: before_ident_line_def get_line_def)
     apply(clarsimp)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(simp add: EValidSplitExt_def)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(subgoal_tac "\<not> Pident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! i)")
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp add: Eident_lines_def Eident_line_def Pident_line_def)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq 0 (length S1) ! i = SSX" for SSX)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: Pident_line_def)
     apply(subgoal_tac "length(restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) i) = length(ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i))")
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "length(ESplitItem_elim ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! i)) = length(ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i))")
       apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! i"
      in ssubst)
       apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(rule nth_append_1)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i"
      in ssubst)
       apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(rule nth_append_1)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(rule restrict_newprods_preserves_length)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule nth_map)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "length (restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) (length S1)) = length(\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2)")
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(simp add: valid_DT_revert_position_def)
     apply(simp add: get_prod_at_DT_revert_position_def)
     apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(rule nth_map)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(case_tac "foldl (@) [] (ESplitItem_elim_prods S2) = [] \<and> ESplitItem_prods S2 = []")
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "EValidSplit_ValidItem G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb)")
       apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
       prefer 2
       apply(simp add: EValidSplit_def)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_gen_def)
      apply(clarsimp)
      apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
       prefer 2
       apply(rule_tac
      G="G"
      and d="d"
      and i="length \<pi>"
      and kleene_starT="False"
      and END="True"
      in cfgLM.trans_der_step_detail)
         apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
         apply(simp add: split_TSstructure_def)
        apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
        apply(force)
       apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to d)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac el fr ig el\<pi> \<pi> to d e ci l r)(*strict*)
      apply(case_tac ci)
      apply(rename_tac el fr ig el\<pi> \<pi> to d e ci l r cfg_confa)(*strict*)
      apply(clarsimp)
      apply(rename_tac el fr ig el\<pi> \<pi> to d e l r)(*strict*)
      apply(simp add: option_to_list_def)
      apply(case_tac fr)
       apply(rename_tac el fr ig el\<pi> \<pi> to d e l r)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r)(*strict*)
       apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
        apply(rename_tac el ig el\<pi> \<pi> to d e l r)(*strict*)
        prefer 2
        apply(rule_tac cfgLM_trans_der_from_empty)
        apply(force)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r)(*strict*)
       apply(clarsimp)
      apply(rename_tac el fr ig el\<pi> \<pi> to d e l r a)(*strict*)
      apply(clarsimp)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
      apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
       prefer 2
       apply(simp add: split_TSstructure_def CFGtermLeft_def)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
      apply(erule_tac
      x="d"
      in allE)
      apply(erule_tac
      x="\<lparr>cfg_conf = [teA a]\<rparr>"
      in allE)
      apply(erule_tac
      x="\<pi>"
      in allE)
      apply(erule_tac
      x="\<lparr>cfg_conf = l @ teA (cons_l3   q1 X q2) # r\<rparr>"
      in allE)
      apply(clarsimp)
      apply(erule impE)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
       apply(simp add: cfgLM.trans_der_def)
       apply(rule_tac
      m="Suc 0"
      and v="[Some SSx]" for SSx
      in get_labels_drop_tail)
        apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
        apply(force)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
       apply(force)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
      apply(erule impE)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
       apply(rule_tac
      x="[]"
      in exI)
       apply(clarsimp)
       apply(rule_tac
      x="[SSX]" for SSX
      in exI)
       apply(force)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a)(*strict*)
      apply(clarsimp)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a w1 w2)(*strict*)
      apply(case_tac l)
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a w1 w2)(*strict*)
       prefer 2
       apply(rename_tac el ig el\<pi> \<pi> to d e l r a w1 w2 aa list)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e r a w1 w2 list)(*strict*)
       apply(case_tac w1)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w1 w2 list)(*strict*)
        apply(clarsimp)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list)(*strict*)
        apply(case_tac w2)
         apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list)(*strict*)
         apply(clarsimp)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list aa lista)(*strict*)
        apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e r a w1 w2 list aa lista)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list lista)(*strict*)
       apply(case_tac list)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list lista)(*strict*)
        prefer 2
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list lista aa listb)(*strict*)
        apply(clarsimp)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 lista aa listb)(*strict*)
        apply(case_tac "ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (case ESplitItem_from S2 of None \<Rightarrow> [] | Some A \<Rightarrow> [A])) to")
         apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 lista aa listb)(*strict*)
         apply(clarsimp)
        apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 lista aa listb ab list)(*strict*)
        apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e r a w2 list lista)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2 lista)(*strict*)
       apply(case_tac lista)
        apply(rename_tac el ig el\<pi> \<pi> to d e a w2 lista)(*strict*)
        prefer 2
        apply(rename_tac el ig el\<pi> \<pi> to d e a w2 lista aa list)(*strict*)
        apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2 lista)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2)(*strict*)
       apply(case_tac w2)
        apply(rename_tac el ig el\<pi> \<pi> to d e a w2)(*strict*)
        apply(force)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2 aa list)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a list)(*strict*)
       apply(subgoal_tac "ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (case ESplitItem_from S2 of None \<Rightarrow> [] | Some A \<Rightarrow> [A])) to = list")
        apply(rename_tac el ig el\<pi> \<pi> to d e a list)(*strict*)
        prefer 2
        apply(rule liftA_inj)
        apply(force)
       apply(rename_tac el ig el\<pi> \<pi> to d e a list)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a)(*strict*)
       apply(erule_tac
      x="length \<pi>"
      in allE)
       apply(clarsimp)
       apply(simp add: get_configuration_def)
      apply(rename_tac el ig el\<pi> \<pi> to d e l r a w1 w2)(*strict*)
      apply(clarsimp)
      apply(rename_tac el ig el\<pi> \<pi> to d e a w1 w2)(*strict*)
      apply(case_tac w1)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w1 w2)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2)(*strict*)
       apply(case_tac w2)
        apply(rename_tac el ig el\<pi> \<pi> to d e a w2)(*strict*)
        apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a w2 aa list)(*strict*)
       apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a list)(*strict*)
       apply(case_tac list)
        apply(rename_tac el ig el\<pi> \<pi> to d e a list)(*strict*)
        apply(clarsimp)
       apply(rename_tac el ig el\<pi> \<pi> to d e a list aa lista)(*strict*)
       apply(clarsimp)
      apply(rename_tac el ig el\<pi> \<pi> to d e a w1 w2 aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprods_def)
     apply(rule_tac
      t="liftB (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2) ! length \<pi>"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(rule liftB_nth)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprodsX_def)
     apply(rule_tac
      t="nat_seq 0 SSX ! SSY" for SSX SSY
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(rule nat_seq_nth_compute)
       apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprodsXX_def)
     apply(subgoal_tac "derives G (\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2) = []")
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: strict_prefix_def option_to_list_def)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule_tac
      G="G"
      in derive_empty_if_first_prod_has_empty_rhs)
       apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(subgoal_tac "EValidSplit_ValidItem G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb)")
       apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
       prefer 2
       apply(simp add: EValidSplit_def)
      apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_belongs_def)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: restrict_newprods_def)
    apply(simp add: restrict_newprodsX_def)
    apply(rule_tac
      t="length(nat_seq SSx SSy)" for SSx SSy
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule nat_seq_length_prime)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="length (liftB (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2))"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
     apply(rule liftB_length)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to rp')(*strict*)
   apply(simp add: is_DT_revert_position_def)
   apply(clarsimp)
   apply(thin_tac "prod_rhs (get_prod_at_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) (gen (length S1) (length \<pi>))) = [] \<and> Suc (length \<pi>) < length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! length S1)) \<or> Suc (length S1) \<in> Pident_lines (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) \<and> Suc (length \<pi>) = length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! length S1))")
   apply(rename_tac el fr ig el\<pi> \<pi> to rp')(*strict*)
   apply(case_tac rp')
    apply(rename_tac el fr ig el\<pi> \<pi> to rp' nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp add: valid_DT_revert_position_def)
    apply(clarsimp)
    apply(thin_tac "length \<pi> < length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! length S1))")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(thin_tac " (case PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! length S1) ! length \<pi> of teA a \<Rightarrow> {a} | teB b \<Rightarrow> {}) = {}")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule leq_gen_elim)
    apply(subgoal_tac "length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) = Suc(length S1)")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! nat) = []")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq 0 (length S1) ! nat"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb)")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp add: EValidSplitExt_def EValidSplitExt_no_elim_before_nonterminal_def)
    apply(erule conjE)+
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat"
      in allE)
    apply(clarsimp)
    apply(case_tac "nat < length S1")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! nat"
      and s="S1!nat"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule_tac
      t="S1!nat"
      and s="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat"
      in subst)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! nat"
      and s="[\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]!SSX" for SSX
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nth_append_2_prime)
       apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat=length S1")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to rp' nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(simp add: valid_DT_revert_position_def)
   apply(clarsimp)
   apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! nat1) ! nat2")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
    apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) = Suc(length S1)")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(subgoal_tac "nat_seq 0 (length S1) ! nat1 = SSX" for SSX)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(thin_tac "length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1))) = Suc (length S1)")
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(simp add: leq_def get_pos_def get_line_def)
   apply(case_tac "length S1 = nat1 \<and> length \<pi> \<le> nat2")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) ! nat1 = (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! nat1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(rule_tac
      ?x1.0="Sb"
      and ?x2.0="[]"
      in nth_eq_ignore_append)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! nat1)) = length (ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) ! nat1))")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length (ESplitItem_prods ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! nat1)) - Suc 0))"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rule liftB_length)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(erule disjE)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(simp add: get_prod_at_DT_revert_position_def)
    apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb)")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(subgoal_tac "EValidSplitExt_no_pop_in_prods_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(simp add: EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat2"
      in allE)
    apply(erule_tac
      P="nat2 < length (ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1))"
      in impE)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(subgoal_tac "(ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1) ! nat2)= ba")
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule_tac
      t="S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb"
      and s="S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # (S2 # Sb)"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule_tac
      el="el"
      and fr="fr"
      and ig="ig"
      and el\<pi>="el\<pi>"
      and to="ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to"
      and G="G"
      and G'="G'"
      and ?S1.0="Sb"
      in nonabstracted_productions_are_unmodified)
        apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
        apply(force)
       apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(case_tac "nat1=length S1")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1"
      and s="S1!nat1"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(rule_tac
      t="S1!nat1"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! nat1"
      in subst)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(case_tac "nat1=length S1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat1<length S1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(simp add: EValidSplitExt_def)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
   apply(erule_tac
      x="length S1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="Suc nat1"
      in allE)
   apply(case_tac "Suc nat1 < length S1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(simp add: Pident_line_def Pident_lines_def)
    apply(clarsimp)
    apply(case_tac "Suc nat1=length S1")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(simp add: Eident_line_def Eident_lines_def Pident_line_def Pident_lines_def)
   apply(clarsimp)
   apply(subgoal_tac "length(ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! Suc nat1)) = length(PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! Suc nat1))")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! Suc nat1)) = length(PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr> # Sb) (Suc (length S1)) ! Suc nat1))")
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq 0 (length S1) ! Suc nat1"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      f="\<lambda>X. length(ESplitItem_elim X)"
      in arg_cong)
    apply(rule nth_eq_ignore_append)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq 0 (length S1) ! Suc nat1"
      in ssubst)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprods_def)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! Suc nat1 = (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods S2) @ ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2 @ drop (length (ESplitItem_elim S2) + length (option_to_list (ESplitItem_from S2))) to\<rparr>]) ! Suc nat1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(rule conjI)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprodsX_def)
     apply(clarsimp)
     apply(rule_tac
      t="length(nat_seq SSx SSy)" for SSx SSy
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule liftB_length)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(rule nth_eq_ignore_append)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(simp add: Xstep_merge1_toWasEliminated_def)
  apply(simp add: get_revert_prod_def)
  apply(subgoal_tac "get_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1))) = Some (elim (length S1))")
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(clarsimp)
   apply(simp add: get_prod_at_DT_revert_position_def)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(subgoal_tac "el\<pi>=[]")
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(rename_tac el fr ig \<pi> to)(*strict*)
    apply(subgoal_tac "EValidSplit_ValidItem G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = [], ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac el fr ig \<pi> to)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def)
    apply(rename_tac el fr ig \<pi> to)(*strict*)
    apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac el fr ig \<pi> to d da)(*strict*)
    apply(rule_tac
      d="d"
      in first_empty_rhs_with_left_degen_front)
      apply(rename_tac el fr ig \<pi> to d da)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac el fr ig \<pi> to d da)(*strict*)
     apply(force)
    apply(rename_tac el fr ig \<pi> to d da)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(subgoal_tac "EValidSplitExt_no_elim_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    prefer 2
    apply(simp add: EValidSplitExt_def )
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: EValidSplitExt_no_elim_before_nonterminal_def)
   apply(erule_tac
      x="(length S1)"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="(length S1)"
      in allE)
   apply(clarsimp)
   apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
   apply(subgoal_tac "length (el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2)) = length(option_to_list fr @ drop (length to) (ESplitItem_elim S2))")
    apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplit_producing G (S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def)
    apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: EValidSplit_producing_def)
    apply(erule_tac
      x="\<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>"
      in ballE)
     apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply (metis append_Cons eq_Nil_appendI in_set_butlast list.simps(3))
    apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(rename_tac ig el\<pi> \<pi> to y)(*strict*)
    apply(simp add: option_to_list_def)
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_elim_def)
   apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_elim_def)
  apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
  apply(rule get_DT_revert_position_eq2)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
   apply(rule_tac
      t="before_ident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1))) (get_line (elim (length S1)))"
      and s="True"
      in ssubst)
    apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: before_ident_line_def get_line_def)
    apply(clarsimp)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "\<not> Pident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! i)")
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(simp add: Eident_lines_def Eident_line_def Pident_line_def)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (length S1) ! i = SSX" for SSX)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(simp add: Pident_line_def)
    apply(subgoal_tac "length(restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) i) = length(ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i))")
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "length(ESplitItem_elim ((S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! i)) = length(ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i))")
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(rule_tac
      t=" ((S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! i)"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i"
      in ssubst)
      apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i"
      in ssubst)
     apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to i)(*strict*)
    apply(rule restrict_newprods_preserves_length)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
   apply(subgoal_tac "EValidSplit_producing G (S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="\<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>"
      in ballE)
    apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
   apply(rename_tac fr ig el\<pi> \<pi> to)(*strict*)
   apply (metis Cons_eq_appendI append_Nil in_set_butlast list.simps(2))
  apply(rename_tac el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to rp')(*strict*)
  apply(case_tac rp')
   apply(rename_tac el fr ig el\<pi> \<pi> to rp' nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(rule leq_elim_elim)
   apply(case_tac "nat<length S1")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "EValidSplitExt_no_elim_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    prefer 2
    apply(simp add: EValidSplitExt_def )
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(simp add: EValidSplitExt_no_elim_before_nonterminal_def)
   apply(erule_tac
      x="(length S1)"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
   apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length S1) ! nat = SSX" for SSX)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(subgoal_tac "length(PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! nat)) = length(ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) ! nat))")
    apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! nat"
      in ssubst)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  apply(rule_tac
    t="(S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) ! nat"
    in ssubst)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat = SSX" for SSX)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) ! nat = SSX" for SSX)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to rp' nat1 nat2)(*strict*)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(rule leq_elim_gen)
  apply(case_tac "nat1<length S1")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(clarsimp)
  apply(simp add: is_DT_revert_position_def)
  apply(clarsimp)
  apply(erule disjE)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "EValidSplitExt_no_pop_in_prods_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  prefer 2
  apply(simp add: EValidSplitExt_def)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(simp add: EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
  apply(erule_tac
    x="length S1"
    in allE)
  apply(clarsimp)
  apply(erule_tac
    x="nat1"
    in allE)
  apply(clarsimp)
  apply(erule_tac
    x="nat2"
    in allE)
  apply(erule impE)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(rule_tac
    t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1"
    in ssubst)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(rule_tac
    t="length (ESplitItem_prods (S1 ! nat1))"
    and s="length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! nat1))"
    in ssubst)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length S1) ! nat1 = SSX" for SSX)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(force)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprods_def restrict_newprodsX_def)
   apply(rule_tac
    t="(S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! nat1"
    in ssubst)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S1 ! nat1)) - Suc 0)) = SSX" for SSX)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(rule conjI)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule liftB_length)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(simp add: get_prod_at_DT_revert_position_def valid_DT_revert_position_def)
  apply(clarsimp)
  apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! nat1) ! nat2")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "ESplitItem_prods ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1) ! nat2 = ba")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule_tac
    t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1"
    in ssubst)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule_tac
    k="Suc 0"
    in nonabstracted_productions_are_unmodified2)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule_tac
    t="length (ESplitItem_prods (S1 ! nat1))"
    and s="length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! nat1))"
    in ssubst)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length S1) ! nat1 = SSX" for SSX)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprods_def restrict_newprodsX_def)
  apply(rule_tac
    t="(S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! nat1"
    in ssubst)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S1 ! nat1)) - Suc 0)) = SSX" for SSX)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule conjI)
   apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule liftB_length)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
  apply(clarsimp)
  apply(simp add: get_prod_at_DT_revert_position_def valid_DT_revert_position_def)
  apply(clarsimp)
  apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! nat1) ! nat2")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(thin_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! length S1) \<noteq> []")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(thin_tac "length S1 < length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)))")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(simp add: EValidSplitExt_def)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
  apply(erule_tac
    x="length S1"
    in allE)
  apply(clarsimp)
  apply(case_tac "Suc nat1 < length S1")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(subgoal_tac "Suc nat1=length S1")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(simp add: Pident_lines_def Pident_line_def)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)) ! length S1) = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2)")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(subgoal_tac "EValidSplit_producing G (S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
  apply(rename_tac fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def)
  apply(rename_tac fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(simp add: EValidSplit_producing_def)
  apply(erule_tac
    x="\<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>"
    in ballE)
  apply(rename_tac fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply (metis append_Cons eq_Nil_appendI in_set_butlast list.simps(3))
  apply(rename_tac fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ig el\<pi> \<pi> to nat1 nat2 ba y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="Suc nat1"
    in allE)
  apply(clarsimp)
  apply(subgoal_tac "Suc nat1 \<notin> Pident_lines (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr> # Sb) (Suc (length S1)))")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(simp (no_asm) add: Pident_lines_def Pident_line_def Eident_lines_def Eident_line_def)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length S1) ! Suc nat1 = SSX" for SSX)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) ! Suc nat1 = SSX" for SSX)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(simp add: Eident_lines_def Eident_line_def)
  apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! Suc nat1 = SSX" for SSX)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length(restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el @ option_to_list fr @ drop (length to) (ESplitItem_elim S2), ESplitItem_from = ESplitItem_from S2, ESplitItem_ignore = ESplitItem_ignore S2, ESplitItem_elim_prods = el\<pi> @ (\<pi> @ \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = []\<rparr> # foldl (@) [] (take (length to) (ESplitItem_elim_prods S2))) # drop (length to) (ESplitItem_elim_prods S2), ESplitItem_prods = ESplitItem_prods S2, ESplitItem_elem = Some (teB b), ESplitItem_to = ESplitItem_to S2\<rparr>]) (Suc nat1)) = length (ESplitItem_prods (S1 ! Suc nat1))")
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(force)
  apply(rename_tac el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
  apply(rule restrict_newprods_preserves_length)
  apply(force)
  done

lemma leq_gen_gen: "
  n\<le>m \<and> x\<le>y
  \<Longrightarrow> leq (gen n x) (gen m y)"
  apply(simp add: leq_def get_line_def get_pos_def)
  apply(force)
  done

lemma get_revert_prod_sound_rhs_read: "
       F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr> # Xstep_gen [B] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr> # Xstep_gen [B] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> Esplit_signature (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr> # Xstep_gen [B] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)) = [teB ba, teA B, teB b]
  \<Longrightarrow> setA (Esplit_signature Sb) = {}
  \<Longrightarrow> \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> ESplitItem_elem SL = Some (teA (cons_l3   q1 X q2))
  \<Longrightarrow> length (Esplit_signature S1) = length S1
  \<Longrightarrow> ESplitItem_elem S2 = Some (teB b)
  \<Longrightarrow> length (nat_seq 0 (length S1)) = Suc (length S1)
  \<Longrightarrow> nat_seq 0 (length S1) ! length S1 = length S1
  \<Longrightarrow> get_revert_prod (restrict G' G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr> # Xstep_gen [B] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb) (Suc (Suc (Suc (length S1))))) = Some \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA B]\<rparr>"
  apply(case_tac B)
   apply(rename_tac q bb)(*strict*)
   apply(subgoal_tac "LR1ProdForm G")
    apply(rename_tac q bb)(*strict*)
    apply(simp add: LR1ProdForm_def)
    apply(erule_tac
      x="\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l2   q bb)]\<rparr>"
      in ballE)
     apply(rename_tac q bb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q bb)(*strict*)
    apply(clarsimp)
   apply(rename_tac q bb)(*strict*)
   apply(simp add: split_TSstructure_def F2LR1inputx_def)
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(force)
  apply(rename_tac q1a bb q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2')
  apply(rename_tac q1' X' q2')(*strict*)
  apply(subgoal_tac "nat_seq 0 0 = [0]")
   apply(rename_tac q1' X' q2')(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac q1' X' q2')(*strict*)
  apply(simp add: Xstep_gen_def)
  apply(simp add: Xstep_mergeL_def Xstep_elem_def nth_opt_def)
  apply(case_tac SL)
  apply(rename_tac q1' X' q2' ESplitItem_elim ESplitItem_from ESplitItem_ignorea ESplitItem_elim_prods ESplitItem_prodsa ESplitItem_elema ESplitItem_toa)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_to)(*strict*)
  apply(rename_tac el fr ig el\<pi> \<pi> to)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: Esplit_signature_def)
  apply(simp add: option_to_list_def)
  apply(simp add: get_revert_prod_def)
  apply(subgoal_tac "get_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) = Some (gen (length S1) (length \<pi>))")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   prefer 2
   apply(rule get_DT_revert_position_eq2)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: is_DT_revert_position_def)
    apply(simp add: valid_DT_revert_position_def)
    apply(rule_tac
      t="before_ident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (get_line (gen (length S1) (length \<pi>)))"
      and s="True"
      in ssubst)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp (no_asm) add: Pident_lines_def Pident_line_def restrict_def restrict_map_def restrict_len_def before_ident_line_def)
     apply(clarsimp)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: Pident_line_def get_line_def)
     apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! i = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! i = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! i = S1 ! i")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(simp add: EValidSplitExt_def)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(simp add: Eident_lines_def Eident_line_def)
     apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac " length(restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) i) = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule restrict_newprods_preserves_length)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[\<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]"
      and G="G"
      and G'="G'"
      and ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>]"
      and n="length S1"
      in restrict_newprods_preserves_length)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp (no_asm) add: Pident_lines_def Pident_line_def)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = ([\<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>,S2])!SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[S2]"
      and G="G"
      and G'="G'"
      and ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>]"
      and n="Suc(length S1)"
      in restrict_newprods_preserves_length)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>]) ! Suc (length S1) = [SSy]!SSX" for SSy SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(case_tac "restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1) ! length \<pi>")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
     prefer 2
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(thin_tac "restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (Suc (length S1)) = []")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(simp add: restrict_newprods_def)
    apply(case_tac "restrict_newignore (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1) = []")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
     prefer 2
     apply(clarsimp)
     apply (metis Nat.lessI setA_liftB liftB_length Suc_length nth_setA)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsX_def)
    apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length \<pi>) ! length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>]) (Some (teB ba)) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = (cons_l3 q1' X' q2') # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "nat_seq 0 (length \<pi>) ! length \<pi> = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsXX_def)
    apply(subgoal_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>] = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule derives_single)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def restrict_newto_def restrict_newignore_def new_post_sig_def)
    apply(subgoal_tac "length (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule drop_and_crop_length)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "Suc (length to + length ig) \<le> Suc (length to)+ length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) \<le> Suc (length to)")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      S="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2])"
      and i="Suc(length S1)"
      in ignore_toberemoved_suffix)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(case_tac c)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(simp add: drop_and_crop_def cropTol3l2_def butn_def)
     apply(case_tac "Suc (length to + length ig) \<le> length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "length(to @ ig) =length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(thin_tac "to @ ig = a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(clarsimp)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "Suc (length to + length ig) - length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) = Suc (length(a#list))")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      prefer 2
      apply(rule_tac
      t="length to+length ig"
      and s="length(to@ig)"
      in ssubst)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(rule_tac
      t="Suc (length (to @ ig))"
      and s="Suc(length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))"
      in ssubst)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(case_tac "to = [] \<and> (Suc (length list) \<le> length to \<or> ig = [])")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(simp add: strict_prefix_def)
     apply(case_tac "butlast (take (Suc (length list)) to) @ [cropTol3l2_single (last (take (Suc (length list)) to))]")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "to @ ig = restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "\<not> strict_prefix [teB ba, teA (cons_l3   q1' X' q2')] (teB ba # liftA (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length to + length ig)))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "suffix SSX (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      k="Suc(Suc (length S1))"
      in ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      c="c"
      in entirely_ignored_can_not_happend_to_early)
            apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
            apply(force)
           apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
           apply(force)
          apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
          apply(thin_tac "EValidSplit G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
          apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
          apply(force)
         apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
         apply(force)
        apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
        apply(force)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      t="S2"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (Suc (length S1))"
      in subst)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      t="S2"
      and s="[S2]!0"
      in ssubst)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to rp')(*strict*)
   apply(case_tac "rp'")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to rp' nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule leq_gen_elim)
    apply(case_tac "nat \<le> length S1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplitExt_no_elim_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp add: EValidSplitExt_no_elim_before_nonterminal_def)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat = (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>])!nat")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule nth_append_2_prime_prime_X)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(case_tac "nat = length S1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
     apply(clarsimp)
     apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) = ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) ! length S1)")
      apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
      apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
      apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(subgoal_tac "nat < length S1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat) = ESplitItem_elim ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>]) ! nat)")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! nat = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! nat"
      in ssubst)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule_tac
      t="S1!nat"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>]) ! nat"
      in subst)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to rp' nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(rule leq_gen_gen)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) ! Suc (length S1) = SSX" for SSX)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(rule ccontr)
    apply(subgoal_tac "nat1<length S1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! nat1 = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc nat1 = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(subgoal_tac "length (ESplitItem_prods (S1 ! nat1)) = length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat1))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(rule sym)
     apply(rule restrict_newprods_preserves_length)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (gen (length S1) (length \<pi>))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(clarsimp)
    apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat1) ! nat2")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1 = S1!nat1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(erule disjE)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(clarsimp)
     apply(simp add: get_prod_at_DT_revert_position_def)
     apply(subgoal_tac "X" for X)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      prefer 2
      apply(rule_tac
      G="G"
      and G'="G'"
      and k="Suc(Suc(Suc 0))"
      and ba="bb"
      and n="nat1"
      and m="nat2"
      and ?S1.0="S1"
      in nonabstracted_productions_are_unmodified2)
        apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
        apply(force)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb)")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(simp add: EValidSplitExt_def EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
     apply(clarsimp)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="nat1"
      in allE)
     apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(clarsimp)
    apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(simp add: EValidSplitExt_def EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="Suc nat1"
      in allE)
    apply(case_tac "Suc nat1<Suc (length S1)")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "Suc nat1 \<notin> Pident_lines (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))))")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def Pident_lines_def Pident_line_def)
     apply(clarsimp)
     apply(simp add: Eident_lines_def Eident_line_def)
     apply(subgoal_tac "length(ESplitItem_prods ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>]) ! Suc nat1)) = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      prefer 2
      apply(rule sym)
      apply(rule_tac
      G="G"
      and G'="G'"
      and ?S2.0=" \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # [S2]"
      in restrict_newprods_preserves_length)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(clarsimp)
     apply(erule impE)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(rule_tac
      t="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) ! Suc nat1"
      and s="((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>]) ! Suc nat1)"
      in subst)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
       apply(rule nth_append_2_prime_prime_X)
         apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
         apply(force)
        apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
        apply(force)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) ! Suc nat1 = (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc nat1")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(rule sym)
     apply(rule nth_append_2_prime_prime_X)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(thin_tac "is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (gen (length S1) (length \<pi>))")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(case_tac "length S1<nat1")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(clarsimp)
    apply(subgoal_tac "length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) = (Suc (Suc (Suc (length S1))))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) = Suc (Suc (Suc (length S1)))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat1) ! nat2")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(clarsimp)
    apply(case_tac "Suc(length S1)=nat1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(subgoal_tac "length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (length (nat_seq 0 (length S1))))) ! length (nat_seq 0 (length S1)))) = 0")
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length S1))"
      in ssubst)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(simp (no_asm))
     apply(rule_tac
      t="min (length S1) (Suc (Suc (Suc (length S1))))"
      and s="length S1"
      in ssubst)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(subgoal_tac "nat_seq 0 (Suc(Suc(length S1))) ! Suc(length S1) = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length S1))"
      in ssubst)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(simp (no_asm))
     apply(subgoal_tac "SSX = length (ESplitItem_prods ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2])! (Suc (length S1))))" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      prefer 2
      apply(rule_tac
      ?S2.0="[]"
      in restrict_newprods_preserves_length)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      prefer 2
      apply(rule nth_append_2)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(thin_tac "Suc (length S1) = length (nat_seq 0 (length S1))")
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(subgoal_tac "Suc(length S1) < nat1")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(clarsimp)
    apply(case_tac "nat1=Suc(Suc(length S1))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2 bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(simp add: get_line_def before_ident_line_def)
    apply(erule_tac
      x="Suc (length S1)"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "Pident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! Suc (length S1))")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(thin_tac "\<not> Pident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! Suc (length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(simp add: Pident_line_def)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)=SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(restrict_newprods G' G ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2])@[]) (Suc (length S1))) = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[]"
      in restrict_newprods_preserves_length)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(thin_tac "length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S1)) = length S1")
   apply(subgoal_tac "length S1=nat1")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(simp add: is_DT_revert_position_def)
   apply(clarsimp)
   apply(case_tac "nat2 < length \<pi>")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(erule disjE)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "Suc nat2 < length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(thin_tac "before_ident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (get_line (gen (length S1) nat2))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(simp add: valid_DT_revert_position_def)
    apply(clarsimp)
    apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! nat2")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 a)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length S1 < length (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(thin_tac "nat2 < length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(subgoal_tac "EValidSplitExt_no_pop_in_prods_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb)")
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(simp add: EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
    apply(erule_tac
      x="Suc(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat2"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>]) ! nat2 = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule_tac
      ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>]"
      and k="(Suc (Suc 0))"
      in nonabstracted_productions_are_unmodified2)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>]) ! length S1 = SSX" for SSX)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
     prefer 2
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2 bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(simp add: get_prod_at_DT_revert_position_def)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1)) = length(\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>])")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq 0 (Suc (Suc (length S1))) ! length S1"
      in ssubst)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    prefer 2
    apply(rule_tac
      ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>]"
      and ?S2.0="[\<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]"
      and n="length S1"
      in restrict_newprods_preserves_length)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(simp add: get_prod_at_DT_revert_position_def)
  apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi>")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(subgoal_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> \<noteq> teA a")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(thin_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> = teA a")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprods_def)
   apply(case_tac "restrict_newignore (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1) = []")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(clarsimp)
    apply (metis Nat.lessI setA_liftB liftB_length Suc_length nth_setA)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
   apply(subgoal_tac "length (nat_seq 0 (length \<pi>)) = SSX" for SSX)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length \<pi>) ! length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>]) (Some (teB ba)) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length \<pi>) ! length \<pi> = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprodsXX_def)
  apply(subgoal_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>] = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule derives_single)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(thin_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>] = [teB ba, teA (cons_l3   q1' X' q2')]")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: option_to_list_def restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule drop_and_crop_length)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(subgoal_tac "Suc (length to + length ig) \<le> Suc (length to)+ length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) \<le> Suc (length to)")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule_tac
    S="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2])"
    and i="Suc(length S1)"
    in ignore_toberemoved_suffix)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rule nth_append_2)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(simp add: drop_and_crop_def cropTol3l2_def butn_def)
  apply(case_tac "Suc (length to + length ig) \<le> length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(to @ ig) =length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(thin_tac "to @ ig = a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length to + length ig) - length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) = Suc (length(a#list))")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   prefer 2
   apply(rule_tac
    t="length to+length ig"
    and s="length(to@ig)"
    in ssubst)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(rule_tac
    t="Suc (length (to @ ig))"
    and s="Suc(length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))"
    in ssubst)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "to = [] \<and> (Suc (length list) \<le> length to \<or> ig = [])")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(case_tac "butlast (take (Suc (length list)) to) @ [cropTol3l2_single (last (take (Suc (length list)) to))]")
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to a list aa lista)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "to @ ig = restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "\<not> strict_prefix [teB ba, teA (cons_l3   q1' X' q2')] (teB ba # liftA (drop_and_crop (cons_l3 q1' X' q2' # to @ ig) (length to + length ig)))")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "suffix SSX (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule_tac
    k="Suc(Suc (length S1))"
    in ESplitItem_ignore_restrict_toberemoved_suffix)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    c="c"
    in entirely_ignored_can_not_happend_to_early)
         apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
         apply(force)
        apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
        apply(force)
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(thin_tac "EValidSplit G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
       apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    t="S2"
    and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) ! Suc (Suc (length S1))"
    in subst)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    t="S2"
    and s="[S2]!0"
    in ssubst)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rule nth_append_2_prime)
    apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
   apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> = teB (\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>)")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(simp add: get_DT_revert_position_def)
  apply(case_tac "\<exists>rp. is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) rp")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb rp)(*strict*)
  apply(thin_tac "(THE rp. is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) rp \<and> (\<forall>rp'. is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) rp' \<longrightarrow> leq rp rp')) = gen (length S1) (length \<pi>)")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb rp)(*strict*)
  apply(thin_tac "is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) rp")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb rp)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprods_def)
  apply(case_tac "restrict_newignore (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1) = []")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(clarsimp)
  apply (metis Nat.lessI liftB_nth2 Suc_length nth_append_length)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprodsX_def)
  apply(subgoal_tac "length(nat_seq 0 (length \<pi>)) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length \<pi>) ! (length \<pi>) = SSX" for SSX)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(force)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(case_tac "restrict_newprodsXX G (length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>]) (Some (teB ba)) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teB ba, teA (cons_l3   q1' X' q2')]\<rparr>], ESplitItem_elem = Some (teB ba), ESplitItem_to = cons_l3 q1' X' q2' # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q1' X' q2'), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = []\<rparr>, S2]) (length S1))")
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' X' q2' el fr ig el\<pi> \<pi> to bb)(*strict*)
  apply(clarsimp)
  done

lemma get_revert_prod_sound_rhs_push: "
F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr> # Xstep_gen [C] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ SL # S2 # Sb)
  \<Longrightarrow> EValidSplitExt (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr> # Xstep_gen [C] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb)
  \<Longrightarrow> Esplit_signature (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr> # Xstep_gen [C] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)) = [teA B, teA C, teB b]
  \<Longrightarrow> setA (Esplit_signature Sb) = {}
  \<Longrightarrow> \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> ESplitItem_elem SL = Some (teA (cons_l3   q1 X q2))
  \<Longrightarrow> length (Esplit_signature S1) = length S1
  \<Longrightarrow> ESplitItem_elem S2 = Some (teB b)
  \<Longrightarrow> length (nat_seq 0 (length S1)) = Suc (length S1)
  \<Longrightarrow> nat_seq 0 (length S1) ! length S1 = length S1
  \<Longrightarrow> get_revert_prod (restrict G' G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr> # Xstep_gen [C] (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2) @ Sb) (Suc (Suc (Suc (length S1))))) = Some \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr>"
  apply(subgoal_tac "LR1ProdForm G")
   prefer 2
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(simp add: split_TSstructure_def F2LR1inputx_def)
   apply(force)
  apply(simp add: LR1ProdForm_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA B, teA C]\<rparr>"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac q2a q3 A2)(*strict*)
  apply(rename_tac q1' q2' X')
  apply(rename_tac q1' q2' X')(*strict*)
  apply(subgoal_tac "nat_seq 0 0 = [0]")
   apply(rename_tac q1' q2' X')(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac q1' q2' X')(*strict*)
  apply(simp add: Xstep_gen_def)
  apply(simp add: Xstep_mergeL_def Xstep_elem_def nth_opt_def)
  apply(case_tac SL)
  apply(rename_tac q1' q2' X' ESplitItem_elim ESplitItem_from ESplitItem_ignorea ESplitItem_elim_prods ESplitItem_prodsa ESplitItem_elema ESplitItem_toa)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_to)(*strict*)
  apply(rename_tac el fr ig el\<pi> \<pi> to)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: Esplit_signature_def)
  apply(simp add: option_to_list_def)
  apply(simp add: get_revert_prod_def)
  apply(subgoal_tac "get_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) = Some (gen (length S1) (length \<pi>))")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   prefer 2
   apply(rule get_DT_revert_position_eq2)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: is_DT_revert_position_def)
    apply(simp add: valid_DT_revert_position_def)
    apply(rule_tac
      t="before_ident_line (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (get_line (gen (length S1) (length \<pi>)))"
      and s="True"
      in ssubst)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp (no_asm) add: Pident_lines_def Pident_line_def restrict_def restrict_map_def restrict_len_def before_ident_line_def)
     apply(clarsimp)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: Pident_line_def get_line_def)
     apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! i = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! i = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! i = S1 ! i")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(subgoal_tac "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(simp add: EValidSplitExt_def)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(simp add: Eident_lines_def Eident_line_def)
     apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! i = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac " length(restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) i) = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
      prefer 2
      apply(rule restrict_newprods_preserves_length)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to i)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[\<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]"
      and G="G"
      and G'="G'"
      and ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>]"
      and n="length S1"
      in restrict_newprods_preserves_length)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp (no_asm) add: Pident_lines_def Pident_line_def)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[S2]"
      and G="G"
      and G'="G'"
      and ?S1.0="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>]"
      and n="Suc(length S1)"
      in restrict_newprods_preserves_length)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>]) ! Suc (length S1) = [SSy]!SSX" for SSy SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(case_tac "restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1) ! length \<pi>")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
     prefer 2
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(thin_tac "restrict_newprods G' G (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (Suc (length S1)) = []")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(simp add: restrict_newprods_def)
    apply(case_tac "restrict_newignore (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1) = []")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
     prefer 2
     apply(clarsimp)
     apply (metis Nat.lessI setA_liftB liftB_length Suc_length nth_setA)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsX_def)
    apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length \<pi>) ! length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>]) (Some (teA (cons_l3   q1' X' q2'))) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "nat_seq 0 (length \<pi>) ! length \<pi> = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsXX_def)
    apply(subgoal_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>] = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule derives_single)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def restrict_newto_def restrict_newignore_def new_post_sig_def)
    apply(subgoal_tac "length (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule drop_and_crop_length)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "Suc (length to + length ig) \<le> Suc (length to)+ length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) \<le> Suc (length to)")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      S="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2])"
      and i="Suc(length S1)"
      in ignore_toberemoved_suffix)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(case_tac c)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(simp add: drop_and_crop_def cropTol3l2_def butn_def)
     apply(case_tac "Suc (length to + length ig) \<le> length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "length(to @ ig) =length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(thin_tac "to @ ig = a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(clarsimp)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "Suc (length to + length ig) - length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) = Suc (length(a#list))")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      prefer 2
      apply(rule_tac
      t="length to+length ig"
      and s="length(to@ig)"
      in ssubst)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(rule_tac
      t="Suc (length (to @ ig))"
      and s="Suc(length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))"
      in ssubst)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(case_tac "to = [] \<and> (Suc (length list) \<le> length to \<or> ig = [])")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
     apply(clarsimp)
     apply(simp add: strict_prefix_def)
     apply(case_tac "butlast (take (Suc (length list)) to) @ [cropTol3l2_single (last (take (Suc (length list)) to))]")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "to @ ig = restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(thin_tac "\<not> strict_prefix [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)] (teA (cons_l3   q1' X' q2') # liftA (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length to + length ig)))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "suffix SSX (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     prefer 2
     apply(rule_tac
      k="Suc(Suc (length S1))"
      in ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      c="c"
      in entirely_ignored_can_not_happend_to_early)
            apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
            apply(force)
           apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
           apply(force)
          apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
          apply(thin_tac "EValidSplit G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
          apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
          apply(force)
         apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
         apply(force)
        apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
        apply(force)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      t="S2"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (Suc (length S1))"
      in subst)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(rule_tac
      t="S2"
      and s="[S2]!0"
      in ssubst)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to rp')(*strict*)
   apply(case_tac "rp'")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to rp' nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule leq_gen_elim)
    apply(case_tac "nat \<le> length S1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplitExt_no_elim_before_nonterminal (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp add: EValidSplitExt_no_elim_before_nonterminal_def)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat = (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>])!nat")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule nth_append_2_prime_prime_X)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(case_tac "nat = length S1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
     apply(clarsimp)
     apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) = ESplitItem_elim ((S1 @ \<lparr>ESplitItem_elim = [], ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) ! length S1)")
      apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
      apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
      apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(subgoal_tac "nat < length S1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat) = ESplitItem_elim ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>]) ! nat)")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! nat = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! nat"
      in ssubst)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(rule_tac
      t="S1!nat"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr>]) ! nat"
      in subst)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to rp' nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(rule leq_gen_gen)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) ! Suc (length S1) = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(rule ccontr)
    apply(subgoal_tac "nat1<length S1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! nat1 = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc nat1 = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(subgoal_tac "length (ESplitItem_prods (S1 ! nat1)) = length (PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat1))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(rule sym)
     apply(rule restrict_newprods_preserves_length)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "is_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) (gen (length S1) (length \<pi>))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(clarsimp)
    apply(case_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! nat1) ! nat2")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb) ! nat1 = S1!nat1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(erule disjE)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(simp add: get_prod_at_DT_revert_position_def)
     apply(subgoal_tac "X" for X)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      prefer 2
      apply(rule_tac
      G="G"
      and G'="G'"
      and k="Suc(Suc(Suc 0))"
      and ba="ba"
      and n="nat1"
      and m="nat2"
      and ?S1.0="S1"
      in nonabstracted_productions_are_unmodified2)
        apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
        apply(force)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     apply(simp add: EValidSplitExt_def EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
     apply(clarsimp)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="nat1"
      in allE)
     apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(thin_tac "EValidSplitExt (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(simp add: EValidSplitExt_def EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="Suc nat1"
      in allE)
    apply(case_tac "Suc nat1<Suc (length S1)")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "Suc nat1 \<notin> Pident_lines (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))))")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def Pident_lines_def Pident_line_def)
     apply(clarsimp)
     apply(simp add: Eident_lines_def Eident_line_def)
     apply(subgoal_tac "length(ESplitItem_prods ((S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>]) ! Suc nat1)) = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      prefer 2
      apply(rule sym)
      apply(rule_tac
      G="G"
      and G'="G'"
      and ?S2.0=" \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # [S2]"
      in restrict_newprods_preserves_length)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(erule impE)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(rule_tac
      t="((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) ! Suc nat1"
      and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>])!(Suc nat1)"
      in subst)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
       apply(rule nth_append_2_prime_prime_X)
         apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
         apply(force)
        apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
        apply(force)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) ! Suc nat1 = (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2#[]) ! Suc nat1")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(rule sym)
     apply(rule nth_append_2_prime_prime_X)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(thin_tac "is_DT_revert_position (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1))))) (gen (length S1) (length \<pi>))")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(case_tac "length S1<nat1")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def)
    apply(clarsimp)
    apply(subgoal_tac "length (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1))))) = (Suc (Suc (Suc (length S1))))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1))))) = Suc (Suc (Suc (length S1)))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    apply(case_tac "PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! nat1) ! nat2")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(case_tac "Suc(length S1)=nat1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(subgoal_tac "length (PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (length (nat_seq 0 (length S1))))) ! length (nat_seq 0 (length S1)))) = 0")
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length S1))"
      in ssubst)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(simp (no_asm))
     apply(rule_tac
      t="min (length S1) (Suc (Suc (Suc (length S1))))"
      and s="length S1"
      in ssubst)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(subgoal_tac "nat_seq 0 (Suc(Suc(length S1))) ! Suc(length S1) = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length S1))"
      in ssubst)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(simp (no_asm))
     apply(subgoal_tac "SSX = length (ESplitItem_prods (((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # []))! (Suc (length S1))))" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      prefer 2
      apply(rule_tac
      ?S2.0="[]"
      in restrict_newprods_preserves_length)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(subgoal_tac "((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # [])) ! Suc (length S1) = SSX" for SSX)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      prefer 2
      apply(rule nth_append_2)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(thin_tac "Suc (length S1) = length (nat_seq 0 (length S1))")
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(subgoal_tac "Suc(length S1) < nat1")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(case_tac "nat1=Suc(Suc(length S1))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(simp add: get_line_def before_ident_line_def)
    apply(erule_tac
      x="Suc (length S1)"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! Suc (length S1) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "Pident_line (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! Suc (length S1))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(thin_tac "\<not> Pident_line (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! Suc (length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(simp add: Pident_line_def)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(subgoal_tac "((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # [])) ! Suc (length S1)=SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(restrict_newprods G' G (((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # []))@[]) (Suc (length S1))) = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule_tac
      ?S2.0="[]"
      in restrict_newprods_preserves_length)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(thin_tac "length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S1)) = length S1")
   apply(subgoal_tac "length S1=nat1")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(simp add: is_DT_revert_position_def)
   apply(clarsimp)
   apply(case_tac "nat2 < length \<pi>")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(erule disjE)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(clarsimp)
    apply(thin_tac "Suc nat2 < length (PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(thin_tac "before_ident_line (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1))))) (get_line (gen (length S1) nat2))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(simp add: valid_DT_revert_position_def)
    apply(clarsimp)
    apply(case_tac "PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1) ! nat2")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 a)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(clarsimp)
    apply(thin_tac "length S1 < length (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(thin_tac "nat2 < length (PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(subgoal_tac "EValidSplitExt_no_pop_in_prods_before_nonterminal ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb))")
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(simp add: EValidSplitExt_def)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(simp add: EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
    apply(erule_tac
      x="Suc(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="(length S1)"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="nat2"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>]) ! nat2 = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule_tac
      ?S1.0="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # [])"
      and k="(Suc (Suc 0))"
      in nonabstracted_productions_are_unmodified2)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # []) ! length S1 = SSX" for SSX)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
     prefer 2
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2 ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(simp add: get_prod_at_DT_revert_position_def)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1)) = length(\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>])")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq 0 (Suc (Suc (length S1))) ! length S1"
      in ssubst)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    prefer 2
    apply(rule_tac
      ?S1.0="(S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # [])"
      and n="length S1"
      in restrict_newprods_preserves_length)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to nat2)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(simp add: get_prod_at_DT_revert_position_def)
  apply(case_tac "PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi>")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(subgoal_tac "PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> \<noteq> teA a")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(thin_tac "PSplitItem_prods (restrict G' G ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb)) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> = teA a")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprods_def)
   apply(case_tac "restrict_newignore ((S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # [])) (length S1) = []")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(clarsimp)
    apply (metis Nat.lessI setA_liftB liftB_length Suc_length nth_setA)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
   apply(subgoal_tac "length (nat_seq 0 (length \<pi>)) = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length \<pi>) ! length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>]) (Some (teA (cons_l3   q1' X' q2'))) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(subgoal_tac "nat_seq 0 (length \<pi>) ! length \<pi> = SSX" for SSX)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprodsXX_def)
  apply(subgoal_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>] = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule derives_single)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(thin_tac "derives G [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>] = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: option_to_list_def restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule drop_and_crop_length)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))) = Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(subgoal_tac "Suc (length to + length ig) \<le> Suc (length to)+ length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "Suc (length to + length ig) - length (restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) \<le> Suc (length to)")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule_tac
    S="S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]"
    and i="Suc(length S1)"
    in ignore_toberemoved_suffix)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(subgoal_tac "(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rule nth_append_2)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(simp add: drop_and_crop_def cropTol3l2_def butn_def)
  apply(case_tac "Suc (length to + length ig) \<le> length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(to @ ig) =length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(thin_tac "to @ ig = a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length to + length ig) - length (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)) = Suc (length(a#list))")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   prefer 2
   apply(rule_tac
    t="length to+length ig"
    and s="length(to@ig)"
    in ssubst)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(rule_tac
    t="Suc (length (to @ ig))"
    and s="Suc(length(a # list @ restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)))"
    in ssubst)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "to = [] \<and> (Suc (length list) \<le> length to \<or> ig = [])")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(case_tac "butlast (take (Suc (length list)) to) @ [cropTol3l2_single (last (take (Suc (length list)) to))]")
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to a list aa lista)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "to @ ig = restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1)")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(thin_tac "\<not> strict_prefix [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)] (teA (cons_l3   q1' X' q2') # liftA (drop_and_crop (cons_l3 q2' X q2 # to @ ig) (length to + length ig)))")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(subgoal_tac "restrict_toberemovedX (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "suffix SSX (restrict_toberemoved (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (length S1))" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  prefer 2
  apply(rule_tac
    k="Suc(Suc (length S1))"
    in ESplitItem_ignore_restrict_toberemoved_suffix)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    c="c"
    in entirely_ignored_can_not_happend_to_early)
         apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
         apply(force)
        apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
        apply(force)
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(thin_tac "EValidSplit G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = Some (teA (cons_l3   q1 X q2)), ESplitItem_to = to\<rparr> # S2 # Sb)")
       apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
       apply(force)
      apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
      apply(force)
     apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
     apply(force)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    t="S2"
    and s="(S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) ! Suc (Suc (length S1))"
    in subst)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(rule_tac
    t="S2"
    and s="[S2]!0"
    in ssubst)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  prefer 2
  apply(rule nth_append_2_prime)
    apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
    apply(force)
   apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
   apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to c)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_prods (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1)))) ! length S1) ! length \<pi> = teB (\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>)")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(thin_tac "get_DT_revert_position (restrict G' G (S1 @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr> # S2 # Sb) (Suc (Suc (Suc (length S1))))) = Some (gen (length S1) (length \<pi>))")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "length(nat_seq 0 (Suc (Suc (length S1)))) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (Suc (Suc (length S1))) ! length S1 = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprods_def)
  apply(case_tac "restrict_newignore (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1) = []")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  prefer 2
  apply(clarsimp)
  apply (metis Nat.lessI liftB_nth2 Suc_length nth_append_length)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprodsX_def)
  apply(subgoal_tac "length(nat_seq 0 (length \<pi>)) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length \<pi>) ! (length \<pi>) = SSX" for SSX)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(force)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(case_tac "restrict_newprodsXX G (length \<pi>) (\<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>]) (Some (teA (cons_l3   q1' X' q2'))) (restrict_newto (S1 @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ [\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = [teA (cons_l3   q1' X' q2'), teA (cons_l3   q2' X q2)]\<rparr>], ESplitItem_elem = Some (teA (cons_l3   q1' X' q2')), ESplitItem_to = cons_l3 q2' X q2 # to\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (cons_l3 q2' X q2), ESplitItem_ignore = to @ ig, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (cons_l3   q2' X q2)), ESplitItem_to = []\<rparr>, S2]) (length S1))")
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1' q2' X' el fr ig el\<pi> \<pi> to ba)(*strict*)
  apply(clarsimp)
  done

lemma get_revert_prod_sound: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> EValidSplit G (Sa @ Sb)
  \<Longrightarrow> EValidSplitExt S
  \<Longrightarrow> EValidSplitExt (Sa @ Sb)
  \<Longrightarrow> A=(cons_l3 q1 X q2)
  \<Longrightarrow> Esplit_signature S = xl @ teA A # teB b # x
  \<Longrightarrow> Esplit_signature Sa = xl @ r @ [teB b]
  \<Longrightarrow> Esplit_signature Sb = x
  \<Longrightarrow> length Sa = length (Esplit_signature Sa)
  \<Longrightarrow> Esplit_step_relation G S \<lparr>prod_lhs = A, prod_rhs = r\<rparr> (Sa @ Sb)
  \<Longrightarrow> setA x = {}
  \<Longrightarrow> get_revert_prod (restrict G' G (Sa @ Sb) (length Sa)) = Some \<lparr>prod_lhs = A, prod_rhs = r\<rparr>"
  apply(simp add: Esplit_step_relation_def)
  apply(clarsimp)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(simp add: Esplit_signature_append setAConcat)
  apply(subgoal_tac "Esplit_signature [SL] = [teA (cons_l3   q1 X q2)]")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def option_to_list_def)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "Esplit_signature (SL # S2) = Esplit_signature [SL] @ Esplit_signature S2")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(rule_tac
      t="SL#S2"
      and s="[SL]@S2"
      in ssubst)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(simp (no_asm) only: Esplit_signature_append)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "Esplit_signature (SL # S2) = teA (cons_l3   q1 X q2) # Esplit_signature S2")
  apply(subgoal_tac "Esplit_signature S2 = teB b # Esplit_signature Sb")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(subgoal_tac "strict_prefix (Esplit_signature S1) xl \<or> SSX" for SSX)
    apply(rename_tac S1 SL S2)(*strict*)
    prefer 2
    apply(rule mutual_strict_prefix_strict_prefix)
    apply(force)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(erule disjE)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 c)(*strict*)
    apply(case_tac c)
     apply(rename_tac S1 SL S2 c)(*strict*)
     apply(clarsimp)
    apply(rename_tac S1 SL S2 c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 list)(*strict*)
    apply(simp add: Esplit_signature_append setAConcat)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(erule disjE)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 c)(*strict*)
    apply(case_tac c)
     apply(rename_tac S1 SL S2 c)(*strict*)
     apply(clarsimp)
    apply(rename_tac S1 SL S2 c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 a list)(*strict*)
    apply(subgoal_tac " list @ teA (cons_l3   q1 X q2) # Esplit_signature S2 = teB b # Esplit_signature Sb")
     apply(rename_tac S1 SL S2 a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac S1 SL S2 a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac S1 SL S2 a list aa lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac S1 SL S2 a lista)(*strict*)
     apply (metis elemInsetA emptyE)
    apply(rename_tac S1 SL S2 a list)(*strict*)
    apply(rule_tac
      a="xl@[a]"
      and b="xl@[teA (cons_l3   q1 X q2)]"
      in append_linj_length)
     apply(rename_tac S1 SL S2 a list)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 a list)(*strict*)
    apply(rule_tac
      t="(xl @ [teA (cons_l3   q1 X q2)]) @ teB b # Esplit_signature Sb"
      and s="Esplit_signature S1 @ teA (cons_l3   q1 X q2) # Esplit_signature S2"
      in ssubst)
     apply(rename_tac S1 SL S2 a list)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 a list)(*strict*)
    apply(rule_tac
      t="Esplit_signature S1"
      and s="xl @ a # list"
      in ssubst)
     apply(rename_tac S1 SL S2 a list)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 a list)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac S1 SL S2)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "Esplit_signature S1 = xl")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(case_tac "S2")
   apply(rename_tac S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL)(*strict*)
   apply(simp add: Esplit_signature_def)
  apply(rename_tac S1 SL S2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac S1 SL a list)(*strict*)
  apply(rename_tac S2 S2L)
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(simp add: nth_opt_def)
  apply(subgoal_tac "Esplit_signature [S2] = [teB b]")
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def)
   apply(case_tac "ESplitItem_elem S2")
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(rule_tac
      xs="S2L"
      in rev_cases)
     apply(rename_tac S1 SL S2 S2L)(*strict*)
     apply(clarsimp)
    apply(rename_tac S1 SL S2 S2L ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 ys y)(*strict*)
    apply(subgoal_tac "(\<forall>x\<in> set (butlast (S1 @ SL # S2 # ys @ [y])). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y))")
     apply(rename_tac S1 SL S2 ys y)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_producing_def)
    apply(rename_tac S1 SL S2 ys y)(*strict*)
    apply(erule_tac
      x="S2"
      in ballE)
     apply(rename_tac S1 SL S2 ys y)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 ys y)(*strict*)
    apply(subgoal_tac "(butlast (S1 @ SL # S2 # ys @ [y]))=SSX" for SSX)
     apply(rename_tac S1 SL S2 ys y)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac S1 SL S2 ys y)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L a)(*strict*)
   apply(subgoal_tac "foldl (@) (option_to_list (ESplitItem_elem S2)) (map (option_to_list \<circ> ESplitItem_elem) S2L) = SSX" for SSX)
    apply(rename_tac S1 SL S2 S2L a)(*strict*)
    prefer 2
    apply(rule foldl_first)
   apply(rename_tac S1 SL S2 S2L a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(subgoal_tac "Esplit_signature (S2#S2L) = Esplit_signature [S2] @ Esplit_signature S2L")
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   prefer 2
   apply(rule_tac
      t="S2#S2L"
      and s="[S2]@S2L"
      in ssubst)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   apply(simp (no_asm) only: Esplit_signature_append)
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(clarsimp)
  apply(thin_tac "Esplit_signature (S2 # S2L) = teB b # Esplit_signature Sb")
  apply(subgoal_tac "length (Esplit_signature S1) = length S1")
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   prefer 2
   apply (metis EValidSplit_Esplit_signature_length list.simps(3))
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length(Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = (cons_l3 q1 X q2), prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)) = Suc(length r)")
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   prefer 2
   apply(subgoal_tac "length(Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) = length r - Suc 0")
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    prefer 2
    apply(rule Xstep_gen_length)
     apply(rename_tac S1 SL S2 S2L)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   apply(simp (no_asm) add: Xstep_mergeL_def)
   apply(rule conjI)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = (cons_l3 q1 X q2), prod_rhs = r\<rparr>)")
     apply(rename_tac S1 SL S2 S2L)(*strict*)
     prefer 2
     apply(rename_tac S1 SL S2 S2L a)(*strict*)
     apply(clarsimp)
     apply(case_tac r)
      apply(rename_tac S1 SL S2 S2L a)(*strict*)
      apply(clarsimp)
      apply(simp add: Xstep_elem_def nth_opt_def)
     apply(rename_tac S1 SL S2 S2L a aa list)(*strict*)
     apply(clarsimp)
     apply(simp add: Xstep_elem_def nth_opt_def)
     apply(clarsimp)
     apply(rename_tac S1 SL S2 S2L a list)(*strict*)
     apply(simp add: Xstep_gen_def)
     apply(case_tac "filterA list = []")
      apply(rename_tac S1 SL S2 S2L a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac S1 SL S2 S2L a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_elem_def nth_opt_def)
    apply(case_tac r)
     apply(rename_tac S1 SL S2 S2L)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 S2L a list)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   apply(clarsimp)
   apply(case_tac r)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L a list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac S1 SL S2 S2L a list)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL S2 S2L a aa lista)(*strict*)
   apply(simp add: split_TSstructure_def LR1ProdFormSimp_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = a # aa # lista\<rparr>"
      in ballE)
    apply(rename_tac S1 SL S2 S2L a aa lista)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S1 SL S2 S2L a aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL S2 S2L a aa lista ba A B)(*strict*)
   apply(subgoal_tac "nat_seq 0 0 = [0]")
    apply(rename_tac S1 SL S2 S2L a aa lista ba A B)(*strict*)
    prefer 2
    apply (metis natUptTo_n_n)
   apply(rename_tac S1 SL S2 S2L a aa lista ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac S1 SL S2 S2L a aa lista ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac S1 SL S2 S2L ba B)(*strict*)
    apply(simp add: Xstep_gen_def)
   apply(rename_tac S1 SL S2 S2L a aa lista ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL S2 S2L B C)(*strict*)
   apply(simp add: Xstep_gen_def)
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(subgoal_tac "Sa = S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)")
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   prefer 2
   apply(rule length_append_equal)
    apply(rename_tac S1 SL S2 S2L)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 S2L)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2 S2L)(*strict*)
  apply(clarsimp)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(simp add: Esplit_signature_append setAConcat)
  apply(thin_tac "Esplit_signature [SL] = [teA (cons_l3   q1 X q2)]")
  apply(thin_tac "length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr> # Xstep_gen (filterA (tl r)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some S2)) = Suc (length r)")
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "ESplitItem_elem S2 = Some (teB b)")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def option_to_list_def)
   apply(case_tac "ESplitItem_elem S2")
    apply(rename_tac S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 a)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(thin_tac "Esplit_signature [S2] = [teB b]")
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = cons_l3 q1 X q2, prod_rhs = r\<rparr>"
      in ballE)
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "length(nat_seq 0 (length S1))=SSX" for SSX)
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length S1) ! (length S1) = SSX" for SSX)
   apply(rename_tac S1 SL S2)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(rule get_revert_prod_sound_rhs_empty)
                 apply(rename_tac S1 SL S2)(*strict*)
                 apply(force)
                apply(rename_tac S1 SL S2)(*strict*)
                apply(force)
               apply(rename_tac S1 SL S2)(*strict*)
               apply(force)
              apply(rename_tac S1 SL S2)(*strict*)
              apply(force)
             apply(rename_tac S1 SL S2)(*strict*)
             apply(force)
            apply(rename_tac S1 SL S2)(*strict*)
            apply(force)
           apply(rename_tac S1 SL S2)(*strict*)
           apply(force)
          apply(rename_tac S1 SL S2)(*strict*)
          apply(force)
         apply(rename_tac S1 SL S2)(*strict*)
         apply(force)
        apply(rename_tac S1 SL S2)(*strict*)
        apply(force)
       apply(rename_tac S1 SL S2)(*strict*)
       apply(force)
      apply(rename_tac S1 SL S2)(*strict*)
      apply(force)
     apply(rename_tac S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2)(*strict*)
  apply(erule exE)+
  apply(rename_tac S1 SL S2 ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac S1 SL S2 ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL S2 ba B)(*strict*)
   apply(rule get_revert_prod_sound_rhs_read)
                apply(rename_tac S1 SL S2 ba B)(*strict*)
                apply(force)
               apply(rename_tac S1 SL S2 ba B)(*strict*)
               apply(force)
              apply(rename_tac S1 SL S2 ba B)(*strict*)
              apply(force)
             apply(rename_tac S1 SL S2 ba B)(*strict*)
             apply(force)
            apply(rename_tac S1 SL S2 ba B)(*strict*)
            apply(force)
           apply(rename_tac S1 SL S2 ba B)(*strict*)
           apply(force)
          apply(rename_tac S1 SL S2 ba B)(*strict*)
          apply(force)
         apply(rename_tac S1 SL S2 ba B)(*strict*)
         apply(force)
        apply(rename_tac S1 SL S2 ba B)(*strict*)
        apply(force)
       apply(rename_tac S1 SL S2 ba B)(*strict*)
       apply(force)
      apply(rename_tac S1 SL S2 ba B)(*strict*)
      apply(force)
     apply(rename_tac S1 SL S2 ba B)(*strict*)
     apply(force)
    apply(rename_tac S1 SL S2 ba B)(*strict*)
    apply(force)
   apply(rename_tac S1 SL S2 ba B)(*strict*)
   apply(force)
  apply(rename_tac S1 SL S2 ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac S1 SL S2 ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac S1 SL S2 B)(*strict*)
   apply(subgoal_tac "LR1ProdForm G")
    apply(rename_tac S1 SL S2 B)(*strict*)
    prefer 2
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rename_tac S1 SL S2 B)(*strict*)
   apply(simp add: LR1ProdForm_def)
   apply(force)
  apply(rename_tac S1 SL S2 ba A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac S1 SL S2 B C)(*strict*)
  apply(rule get_revert_prod_sound_rhs_push)
               apply(rename_tac S1 SL S2 B C)(*strict*)
               apply(force)+
  done

lemma LR1_property_part2_equal_productions2: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S1
  \<Longrightarrow> EValidSplit G (S1a @ S1b)
  \<Longrightarrow> EValidSplitExt S1
  \<Longrightarrow> EValidSplitExt (S1a @ S1b)
  \<Longrightarrow> A1=(cons_l3 q11 X1 q12)
  \<Longrightarrow> A2=(cons_l3 q21 X2 q22)
  \<Longrightarrow> Esplit_signature S1 = xl1 @ teA A1 # teB b # Esplit_signature S1b
  \<Longrightarrow> Esplit_signature S1a = xl1 @ r1 @ [teB b]
  \<Longrightarrow> length S1a = length (Esplit_signature S1a)
  \<Longrightarrow> Esplit_step_relation G S1 \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr> (S1a @ S1b)
  \<Longrightarrow> EValidSplit G S2
  \<Longrightarrow> EValidSplit G (S2a @ S2b)
  \<Longrightarrow> EValidSplitExt S2
  \<Longrightarrow> EValidSplitExt (S2a @ S2b)
  \<Longrightarrow> Esplit_signature S2 = xl2 @ teA A2 # teB b # Esplit_signature S2b
  \<Longrightarrow> Esplit_signature S2a = xl2 @ r2 @ [teB b]
  \<Longrightarrow> length S2a = length (Esplit_signature S2a)
  \<Longrightarrow> Esplit_step_relation G S2 \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr> (S2a @ S2b)
  \<Longrightarrow> restrict G' G (S1a @ S1b) (length S1a) = restrict G' G (S2a @ S2b) (length S2a)
  \<Longrightarrow> setA (Esplit_signature S1b) = {}
  \<Longrightarrow> setA (Esplit_signature S2b) = {}
  \<Longrightarrow> \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr> = \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>"
  apply(subgoal_tac "get_revert_prod (restrict G' G (S1a @ S1b) (length S1a)) = Some \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr>")
   apply(subgoal_tac "get_revert_prod (restrict G' G (S2a @ S2b) (length S2a)) = Some \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>")
    apply(subgoal_tac "get_revert_prod (restrict G' G (S1a @ S1b) (length S1a)) = get_revert_prod (restrict G' G (S2a @ S2b) (length S2a))")
     apply(force)
    apply(force)
   apply(rule get_revert_prod_sound)
               apply(force)
              apply(force)
             prefer 4
             apply(force)
            prefer 4
            apply(force)
           prefer 4
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule get_revert_prod_sound)
              apply(force)
             apply(force)
            prefer 2
            apply(force)
           prefer 3
           apply(force)
          prefer 3
          apply(force)
         prefer 3
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma LR1_property_part2_equal_productions: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S1
  \<Longrightarrow> EValidSplit G (S1a @ S1b)
  \<Longrightarrow> EValidSplitExt S1
  \<Longrightarrow> EValidSplitExt (S1a @ S1b)
  \<Longrightarrow> A1=(cons_l3 q11 X1 q12)
  \<Longrightarrow> A2=(cons_l3 q21 X2 q22)
  \<Longrightarrow> Esplit_signature S1 = xl1 @ teA A1 # teB b # Esplit_signature S1b
  \<Longrightarrow> Esplit_signature (S1a @ S1b) = xl1 @ r1 @ teB b # Esplit_signature S1b
  \<Longrightarrow> Esplit_signature S1a = xl1 @ r1 @ [teB b]
  \<Longrightarrow> length S1a = Suc (length xl1 + length r1)
  \<Longrightarrow> Esplit_step_relation G S1 \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr> (S1a @ S1b)
  \<Longrightarrow> EValidSplit G S2
  \<Longrightarrow> EValidSplit G (S2a @ S2b)
  \<Longrightarrow> EValidSplitExt S2
  \<Longrightarrow> EValidSplitExt (S2a @ S2b)
  \<Longrightarrow> Esplit_signature S2 = xl2 @ teA A2 # teB b # Esplit_signature S2b
  \<Longrightarrow> Esplit_signature (S2a @ S2b) = xl2 @ r2 @ teB b # Esplit_signature S2b
  \<Longrightarrow> Esplit_signature S2a = xl2 @ r2 @ [teB b]
  \<Longrightarrow> length S2a = Suc (length xl2 + length r2)
  \<Longrightarrow> Esplit_step_relation G S2 \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr> (S2a @ S2b)
  \<Longrightarrow> xl1 @ r1 = xl2 @ r2
  \<Longrightarrow> restrict G' G (S1a @ S1b) (Suc (length xl1 + length r1)) = restrict G' G (S2a @ S2b) (Suc (length xl2 + length r2))
  \<Longrightarrow> setA (Esplit_signature S1b) = {}
  \<Longrightarrow> setA (Esplit_signature S2b) = {}
  \<Longrightarrow> A1 = A2 \<and> r1 = r2"
  apply(subgoal_tac "Esplit_signature (S2a @ S2b) = SSX" for SSX)
   prefer 2
   apply(rule Esplit_signature_append)
  apply(subgoal_tac "Esplit_signature (S1a @ S1b) = SSX" for SSX)
   prefer 2
   apply(rule Esplit_signature_append)
  apply(thin_tac "Esplit_signature (S2a @ S2b) = xl2 @ r2 @ teB b # Esplit_signature S2b")
  apply(thin_tac "Esplit_signature (S1a @ S1b) = xl1 @ r1 @ teB b # Esplit_signature S1b")
  apply(subgoal_tac "\<lparr>prod_lhs = A1, prod_rhs = r1\<rparr> = \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>")
   apply(force)
  apply(rule_tac
      S1a="S1a"
      and S2a="S2a"
      and ?S1.0="S1"
      and ?S1b.0="S1b"
      and ?S2b.0="S2b"
      and ?S2.0="S2"
      in LR1_property_part2_equal_productions2)
                      apply(force)+
  done

theorem LR1_property_part2: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=xl1@teA A1#teB b#x1\<rparr>)
  \<Longrightarrow> d1 (Suc n1) = Some (pair (Some \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr>) \<lparr>cfg_conf=xl1@r1@teB b#x1\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=xl2@teA A2#teB b#x2\<rparr>)
  \<Longrightarrow> d2 (Suc n2) = Some (pair (Some \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>) \<lparr>cfg_conf=xl2@r2@teB b#x2\<rparr>)
  \<Longrightarrow> xl1@r1=xl2@r2
  \<Longrightarrow> \<lparr>prod_lhs = A1, prod_rhs = r1\<rparr> = \<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and n="n1"
      in cfgRM_derivation_to_Esplit_derivation)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d2a S)(*strict*)
  apply(rename_tac d1x S1)
  apply(rename_tac d1x S1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d2"
      and n="n2"
      in cfgRM_derivation_to_Esplit_derivation)
     apply(rename_tac d1x S1)(*strict*)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def)
     apply(force)
    apply(rename_tac d1x S1)(*strict*)
    apply(force)
   apply(rename_tac d1x S1)(*strict*)
   apply(force)
  apply(rename_tac d1x S1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2a S)(*strict*)
  apply(rename_tac d2x S2)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "EValidSplit G S1")
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(subgoal_tac "S1 \<in> SSC" for SSC)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1x"
      in Esplit.belongs_configurations)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(rule Esplit.derivation_initial_belongs)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(simp add: Esplit_configurations_def)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "EValidSplit G S2")
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(subgoal_tac "S2 \<in> SSC" for SSC)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2x"
      in Esplit.belongs_configurations)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(rule Esplit.derivation_initial_belongs)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(simp add: Esplit_configurations_def)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(rule_tac
      S="S1"
      and e="\<lparr>prod_lhs = A1, prod_rhs = r1\<rparr>"
      and w="xl1 @ teA A1 # teB b # x1"
      and w'="xl1 @ r1 @ teB b # x1"
      in ESplit_cfgRM_step_can_be_simulated)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n1"
      and m="Suc n1"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S')(*strict*)
  apply(rename_tac S1x)
  apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   prefer 2
   apply(rule_tac
      S="S2"
      and e="\<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>"
      and w="xl2 @ teA A2 # teB b # x2"
      and w'="xl2 @ r2 @ teB b # x2"
      in ESplit_cfgRM_step_can_be_simulated)
      apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="n2"
      and m="Suc n2"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1x S')(*strict*)
  apply(rename_tac S2x)
  apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
   prefer 2
   apply(rule_tac
      S="S1x"
      and b="b"
      and x="x1"
      and v="xl1 @ r1"
      in EValidSplit_take_prefix)
      apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S2a)(*strict*)
  apply(rename_tac S1a S1b)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
   prefer 2
   apply(rule_tac
      S="S2x"
      and b="b"
      and x="x2"
      and v="xl2 @ r2"
      in EValidSplit_take_prefix)
      apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S1c S2a)(*strict*)
  apply(rename_tac S2a S2b)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      ?S1.0="S1a"
      and S1'="S1b"
      and ?S2.0="S2a"
      and S2'="S2b"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and ?n1.0="Suc n1"
      and ?n2.0="Suc n2"
      and v="xl1 @ r1"
      and b="b"
      and ?x1.0="Esplit_signature S1b"
      in equal_split_prefix)
                  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                  apply(force)
                 apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                 apply(force)
                apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                apply(force)
               apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
               apply(force)
              apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
              apply(force)
             apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
             apply(rule_tac
      t="xl1@r1"
      and s="xl2@r2"
      in ssubst)
              apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
              apply(force)
             apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
             apply(force)
            apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
            apply(force)
           apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
           apply(force)
          apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
          apply(force)
         apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
         apply(force)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "setA (Esplit_signature S1b) = {}")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n1"
      and m="Suc n1"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = r")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB r"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(subgoal_tac "strict_prefix xl1 l \<or> SSX" for SSX)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    prefer 2
    apply(rule mutual_strict_prefix_strict_prefix)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(erule disjE)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c)(*strict*)
    apply(rule_tac
      xs="c"
      in rev_cases)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y)(*strict*)
    apply(case_tac ys)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(subgoal_tac "LR1ProdFormSimp G")
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     prefer 2
     apply(simp add: split_TSstructure_def)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(simp add: LR1ProdFormSimp_def)
    apply(erule_tac
      x="\<lparr>prod_lhs = A1, prod_rhs = r1\<rparr>"
      in ballE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
     apply(case_tac list)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list a lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarify)
     apply(subgoal_tac "A1=B")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
      prefer 2
      apply(rule sym)
      apply (metis Cons_eq_appendI append_Nil DT_two_elements.inject(1) unequal_by_first_char)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarify)
     apply(thin_tac "[teA A1] @ list @ [y, teA A1] = teA A1 # list @ [y, teA A1]")
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(subgoal_tac "CFG_no_self_loop G")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
      prefer 2
      apply(simp add: split_TSstructure_def)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(simp add: CFG_no_self_loop_def)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
    apply(case_tac list)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(erule disjE)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c)(*strict*)
    apply(rule_tac
      xs="c"
      in rev_cases)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y)(*strict*)
    apply(case_tac ys)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
     apply(case_tac l')
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
      apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' y list)(*strict*)
    apply (metis ConsApp setA_liftB setA_decompose setA_setmp_concat_2 all_not_in_conv append_Nil elemInsetA emptyE empty_subsetI)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l')(*strict*)
   apply(case_tac l')
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l')(*strict*)
    apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "setA (Esplit_signature S2b) = {}")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="n2"
      and m="Suc n2"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = r")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB r"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(subgoal_tac "strict_prefix xl2 l \<or> SSX" for SSX)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    prefer 2
    apply(rule mutual_strict_prefix_strict_prefix)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(erule disjE)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c)(*strict*)
    apply(rule_tac
      xs="c"
      in rev_cases)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y)(*strict*)
    apply(case_tac ys)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' ys y a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(subgoal_tac "LR1ProdFormSimp G")
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     prefer 2
     apply(simp add: split_TSstructure_def)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(simp add: LR1ProdFormSimp_def)
    apply(erule_tac
      x="\<lparr>prod_lhs = A2, prod_rhs = r2\<rparr>"
      in ballE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
     apply(case_tac list)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list a lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarify)
     apply(subgoal_tac "A2=B")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
      prefer 2
      apply(rule sym)
      apply (metis Cons_eq_appendI append_Nil DT_two_elements.inject(1) unequal_by_first_char)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
     apply(clarify)
     apply(thin_tac "[teA A2] @ list @ [y, teA A2] = teA A2 # list @ [y, teA A2]")
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(subgoal_tac "CFG_no_self_loop G")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
      prefer 2
      apply(simp add: split_TSstructure_def)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list)(*strict*)
     apply(simp add: CFG_no_self_loop_def)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' y list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
    apply(case_tac list)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(erule disjE)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c)(*strict*)
    apply(rule_tac
      xs="c"
      in rev_cases)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y)(*strict*)
    apply(case_tac ys)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
     apply(case_tac l')
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
      apply(clarsimp)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' ys y a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l' y list)(*strict*)
    apply (metis ConsApp setA_liftB setA_decompose setA_setmp_concat_2 all_not_in_conv append_Nil elemInsetA emptyE empty_subsetI)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l l')(*strict*)
   apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l')(*strict*)
   apply(case_tac l')
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l')(*strict*)
    apply(clarsimp)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b l' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(case_tac A1)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n1"
      and \<pi>="map the (get_labels d1 n1)"
      in cfgRM_reachable_only_l3_nonterminals)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(rule cfgRM.derivation_initial_belongs)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(simp add: split_TSstructure_def)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply (metis get_labels_length)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(rule_tac
      G="G"
      in cfgRM.get_labels_the_Some_on_defined_positions)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(case_tac "d1 0")
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba a option baa)(*strict*)
       apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba baa)(*strict*)
       apply(simp add: cfg_initial_configurations_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply (metis get_labels_length)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(rule_tac
      xs="teB b # Esplit_signature S1b"
      in rev_cases)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast (xl1 @ teA (cons_l2   q ba) # ys @ [y]) = SSX" for SSX)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: filterA_distrib_append filterA_liftB)
   apply (metis only_l3_nonterminals_drop only_l3_nonterminals_l2_at_front)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
  apply(case_tac A2)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="n2"
      and \<pi>="map the (get_labels d2 n2)"
      in cfgRM_reachable_only_l3_nonterminals)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(rule cfgRM.derivation_initial_belongs)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
        apply(simp add: split_TSstructure_def)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply(rule_tac
      t="length (get_labels d2 n2)"
      and s="n2"
      in ssubst)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply (metis get_labels_length)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(rule_tac
      G="G"
      in cfgRM.get_labels_the_Some_on_defined_positions)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
       apply(case_tac "d2 0")
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
        apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa a option bb)(*strict*)
       apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa bb)(*strict*)
       apply(simp add: cfg_initial_configurations_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (get_labels d2 n2)"
      and s="n2"
      in ssubst)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
      apply (metis get_labels_length)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
   apply(rule_tac
      xs="teB b # Esplit_signature S2b"
      in rev_cases)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast (xl2 @ teA (cons_l2   q baa) # ys @ [y]) = SSX" for SSX)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa ys y)(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q baa ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: filterA_distrib_append filterA_liftB)
   apply (metis only_l3_nonterminals_drop only_l3_nonterminals_l2_at_front)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 q1a baa q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q11 A1 q12 q21 A2 q22)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
  apply(subgoal_tac "EValidSplitExt S1")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
   apply(subgoal_tac "EValidSplitExt S2")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
    apply(subgoal_tac "EValidSplitExt (S1a@S1b)")
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(subgoal_tac "EValidSplitExt (S2a@S2b)")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(thin_tac "Esplit.derivation_initial G d1x")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(thin_tac "Esplit.derivation_initial G d2x")
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(thin_tac "get_labels d2x n2 = get_labels d2 n2")
      apply(thin_tac "get_labels d1x n1 = get_labels d1 n1")
      apply(thin_tac "d1x n1 = Some (pair e1 S1)")
      apply(thin_tac "d2x n2 = Some (pair e2 S2)")
      apply(thin_tac "cfgRM.derivation_initial G d1")
      apply(thin_tac "d1 n1 = SSX" for SSX)
      apply(thin_tac "d1 (Suc n1) = SSX" for SSX)
      apply(thin_tac "cfgRM.derivation_initial G d2")
      apply(thin_tac "d2 n2 = SSX" for SSX)
      apply(thin_tac "d2 (Suc n2) = SSX" for SSX)
      apply(clarsimp)
      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(subgoal_tac "X" for X)
       apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       prefer 2
       apply(rule_tac
      ?A1.0="cons_l3 q11 A1 q12"
      and ?A2.0="cons_l3 q21 A2 q22"
      and S2a="S2a"
      and S1a="S1a"
      and ?S1.0="S1"
      and ?S2.0="S2"
      in LR1_property_part2_equal_productions)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(force)
                     apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                     apply(rule_tac
      t="length xl1 + length r1"
      and s="length (xl1@r1)"
      in ssubst)
                      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                      apply(simp (no_asm))
                     apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                     apply(force)
                    apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                    apply(force)
                   apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                   apply(force)
                  apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                  apply(force)
                 apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                 apply(force)
                apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
                apply(force)
               apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
               apply(force)
              apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
              apply(force)
             apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
             apply(force)
            apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
            apply(rule_tac
      t="length xl2 + length r2"
      and s="length (xl2@r2)"
      in ssubst)
             apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
             apply(simp (no_asm))
            apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
            apply(force)
           apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
           apply(force)
          apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
          apply(force)
         apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
         apply(rule_tac
      t="Suc (length xl1 + length r1)"
      and s="Suc (length xl2 + length r2)"
      in ssubst)
          apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
         apply (metis length_append)
        apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
        apply(force)
       apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(force)
      apply(rename_tac S1 S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(rule_tac
      G="G"
      and G'="G'"
      and d="derivation_append d2x (der2 S2 \<lparr>prod_lhs = cons_l3 q21 A2 q22, prod_rhs = r2\<rparr> (S2a @ S2b)) n2"
      and n="Suc n2"
      in Esplit_derivation_enforces_EValidSplitExt)
         apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
         apply(simp add: Esplit_TSstructure_def F2LR1input_def)
         apply(force)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(rule Esplit.derivation_append_preserves_derivation_initial)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
        apply(simp add: Esplit_TSstructure_def F2LR1input_def)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(rule Esplit.derivation_append_preserves_derivation)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
        apply(rule Esplit.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(rule Esplit.der2_is_derivation)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(clarsimp)
      apply(simp add: der2_def)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
    apply(rule_tac
      G="G"
      and G'="G'"
      and d="derivation_append d1x (der2 S1 \<lparr>prod_lhs = cons_l3 q11 A1 q12, prod_rhs = r1\<rparr> (S1a @ S1b)) n1"
      and n="Suc n1"
      in Esplit_derivation_enforces_EValidSplitExt)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
        apply(simp add: Esplit_TSstructure_def F2LR1input_def)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(rule Esplit.derivation_append_preserves_derivation_initial)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(rule Esplit.derivation_append_preserves_derivation)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(rule Esplit.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(rule Esplit.der2_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
   apply(rule_tac
      G="G"
      and G'="G'"
      and d="d2x"
      and n="n2"
      in Esplit_derivation_enforces_EValidSplitExt)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
  apply(rule_tac
      G="G"
      and G'="G'"
      and d="d1x"
      and n="n1"
      in Esplit_derivation_enforces_EValidSplitExt)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q11 A1 q12 q21 A2 q22)(*strict*)
  apply(force)
  done

lemma no_pre_DT_revert_position: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> EValidSplitExt S
  \<Longrightarrow> Esplit_signature S = w @ v @ teA A # liftB \<alpha>
  \<Longrightarrow> is_DT_revert_position (restrict G' G S (length w)) rp
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> Q"
  apply(subgoal_tac "get_line rp \<le> length w")
   prefer 2
   apply(simp add: is_DT_revert_position_def valid_DT_revert_position_def restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq 0 (min (length S) (length w) - Suc 0))=SSX" for SSX)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(case_tac rp)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply(simp add: get_line_def)
   apply(rename_tac nat1 nat2)(*strict*)
   apply(clarsimp)
   apply(simp add: get_line_def)
  apply(subgoal_tac "\<exists>Sw Sv SA S\<alpha>. S = Sw @ Sv @ SA # S\<alpha> \<and> Esplit_signature Sw = w \<and> length Sw = length (Esplit_signature Sw) \<and> Esplit_signature Sv = v \<and> length Sv = length (Esplit_signature Sv) \<and> Esplit_signature [SA] = [teA A] \<and> Esplit_signature S\<alpha> = liftB \<alpha> ")
   prefer 2
   apply(rule no_pre_DT_revert_position_hlp2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac Sw Sv SA S\<alpha>)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Sw Sv SA S\<alpha>)(*strict*)
   prefer 2
   apply(rule_tac
      S="Sw@Sv"
      in EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac Sw Sv SA S\<alpha>)(*strict*)
  apply(clarsimp)
  apply(case_tac rp)
   apply(rename_tac Sw Sv SA S\<alpha> nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac i)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(subgoal_tac "(Sw@Sv @ SA # S\<alpha>) ! length (Sw@Sv) = (SA#S\<alpha>)!SSX" for SSX)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
     apply(force)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(simp add: is_DT_revert_position_def)
   apply(simp add: valid_DT_revert_position_def)
   apply(clarsimp)
   apply(simp add: EValidSplitExt_def EValidSplitExt_no_elim_before_nonterminal_def)
   apply(clarsimp)
   apply(erule_tac
      x="length (Sw@Sv)"
      in allE)
   apply(erule impE)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(erule impE)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(clarsimp)
    apply(simp add: Esplit_signature_def option_to_list_def)
    apply(case_tac "ESplitItem_elem SA")
     apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
     apply(clarsimp)
    apply(rename_tac Sw Sv SA S\<alpha> i a)(*strict*)
    apply(clarsimp)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(simp add: get_line_def)
   apply(erule_tac
      x="i"
      in allE)
   apply (simp add: Esplit_signature_append)
   apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature Sw) - Suc 0)) = SSX" for SSX)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(subgoal_tac "(nat_seq 0 (length (Esplit_signature Sw) - Suc 0) ! i) = SSX" for SSX)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
     apply(force)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(simp add: restrict_def restrict_map_def restrict_len_def)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(subgoal_tac "length(PSplitItem_elim (restrict G' G (Sw @ Sv @ SA # S\<alpha>) (length (Esplit_signature Sw)) ! i)) = length(ESplitItem_elim ((Sw @ Sv @ SA # S\<alpha>) ! i)) ")
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    apply(rule nth_map)
    apply(simp add: restrict_def restrict_map_def restrict_len_def)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(Sw @ Sv @ SA # S\<alpha>) ! i = Sw!i")
    apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(simp add: restrict_def restrict_map_def restrict_len_def)
   apply(rename_tac Sw Sv SA S\<alpha> i)(*strict*)
   apply(force)
  apply(rename_tac Sw Sv SA S\<alpha> nat1 nat2)(*strict*)
  apply(simp add: get_line_def)
  apply(rename_tac i1 i2)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
  apply(simp add: is_DT_revert_position_def)
  apply(simp add: valid_DT_revert_position_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature Sw) - Suc 0)) = SSX" for SSX)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
  apply(subgoal_tac "(Sw @ Sv @ SA # S\<alpha>) ! i1 = Sw!i1")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
  apply(case_tac "PSplitItem_prods (restrict G' G (Sw @ Sv @ SA # S\<alpha>) (length (Esplit_signature Sw)) ! i1) ! i2")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 a)(*strict*)
   apply(clarsimp)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "get_prod_at_DT_revert_position (restrict G' G (Sw @ Sv @ SA # S\<alpha>) (length (Esplit_signature Sw))) (gen i1 i2) = b")
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(clarsimp)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(simp add: EValidSplitExt_def EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
    apply(clarsimp)
    apply(erule_tac
      x="length (Sw@Sv)"
      in allE)
    apply(clarsimp)
    apply(erule impE)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(rule_tac
      t="(Sw @ Sv @ SA # S\<alpha>) ! length (Esplit_signature (Sw @ Sv))"
      and s="(SA#S\<alpha>)!X" for X
      in ssubst)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(rule nth_append_2_prime)
        apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
        apply(force)
       apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
       apply(force)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(clarsimp)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(clarsimp)
     apply(simp add: Esplit_signature_def option_to_list_def)
     apply(case_tac "ESplitItem_elem SA")
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(clarsimp)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(erule_tac
      x="i1"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="i2"
      in allE)
    apply(subgoal_tac " length (ESplitItem_prods ((Sw @ Sv @ SA # S\<alpha>) ! i1)) = length (PSplitItem_prods (restrict G' G (Sw @ Sv @ SA # S\<alpha>) (length (Esplit_signature Sw)) ! i1))")
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(subgoal_tac "(i1 + (length Sw - i1 - Suc 0) + Suc 0) = length (Esplit_signature Sw)")
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(subgoal_tac "ESplitItem_prods (Sw ! i1) ! i2 = SSX" for SSX)
       apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
       prefer 2
       apply(rule_tac
      k="length Sw - i1 - Suc 0"
      and G="G"
      and S1'="Sv@SA#S\<alpha>"
      and G'="G'"
      in nonabstracted_productions_are_unmodified3)
         apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
         apply(force)
        apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
        apply(force)
       apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
       apply(force)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(rule nth_map)
     apply(rule_tac
      t="length (nat_seq 0 (length (Esplit_signature Sw) - Suc 0))"
      in ssubst)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(simp add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq 0 (length (Esplit_signature Sw) - Suc 0) ! i1"
      in ssubst)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(simp add: restrict_def restrict_map_def restrict_len_def)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprods_def)
    apply(rule conjI)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprodsX_def)
     apply(clarsimp)
     apply(rule_tac
      t="length (nat_seq 0 (length (ESplitItem_prods (Sw ! i1)) - Suc 0))"
      in ssubst)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
     apply(force)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2)(*strict*)
    apply(clarsimp)
    apply (metis liftB_length)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(simp add: get_prod_at_DT_revert_position_def)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(simp add: EValidSplitExt_def EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
  apply(clarsimp)
  apply(erule_tac
      x="length (Esplit_signature Sw) + length (Esplit_signature Sv)"
      in allE)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(rule_tac
      t="(Sw @ Sv @ SA # S\<alpha>) ! length (Esplit_signature (Sw @ Sv))"
      and s="(SA#S\<alpha>)!X" for X
      in ssubst)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(rule nth_append_2_prime)
      apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
     apply(force)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(simp add: Esplit_signature_def option_to_list_def)
   apply(case_tac "ESplitItem_elem SA")
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(case_tac "Suc i1 = length (Sw@Sv)")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(simp add: Pident_line_def Pident_lines_def)
   apply(clarsimp)
   apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(erule_tac
      x="Suc i1"
      in allE)
  apply(erule impE)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply (simp add: Esplit_signature_append)
   apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(simp add: Eident_line_def Eident_lines_def Pident_line_def Pident_lines_def)
  apply(clarsimp)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "nat_seq 0 (length (Esplit_signature Sw) - Suc 0) ! Suc i1 = SSX" for SSX)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(force)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(Sw @ Sv @ SA # S\<alpha>) ! Suc i1 = Sw!Suc i1")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (restrict_newprods G' G Sw (Suc i1)) = length (ESplitItem_prods (Sw ! Suc i1))")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(force)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(simp add: restrict_newprods_def)
  apply(subgoal_tac "length(nat_seq 0 (length (ESplitItem_prods (Sw ! Suc i1)) - Suc 0)) = SSX" for SSX)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(case_tac "restrict_newignore Sw (nat_seq 0 (length (Esplit_signature Sw) - Suc 0) ! i1) = []")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(case_tac "restrict_newignore Sw (Suc i1) = []")
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsX_def)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(liftB (ESplitItem_prods (Sw ! Suc i1))) = SSX" for SSX)
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    prefer 2
    apply(rule liftB_length)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(case_tac "ESplitItem_prods (Sw ! Suc i1)")
    apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(case_tac "restrict_newignore Sw (Suc i1) = []")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length(liftB (ESplitItem_prods (Sw ! Suc i1))) = SSX" for SSX)
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   prefer 2
   apply(rule liftB_length)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
  apply(case_tac "ESplitItem_prods (Sw ! Suc i1)")
   apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b)(*strict*)
   apply(clarsimp)
  apply(rename_tac Sw Sv SA S\<alpha> i1 i2 b a list)(*strict*)
  apply(clarsimp)
  done

lemma F_SDPDA_TO_CFG_STD__enforces_cfg_LRk_3: "
  F2LR1inputx G' G
  \<Longrightarrow> split_TSstructure G'
  \<Longrightarrow> cfgRM.derivation_initial G' d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf = \<beta>1 @ teA A1 # teB b # liftB \<alpha>3\<rparr>)
  \<Longrightarrow> d1 (Suc n1) = Some (pair (Some \<lparr>prod_lhs = A1, prod_rhs = \<beta>2\<rparr>) \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>3\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G' d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2\<rparr>)
  \<Longrightarrow> d2 (Suc n2) = Some (pair (Some \<lparr>prod_lhs = A2, prod_rhs = []\<rparr>) \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ liftB \<alpha>2\<rparr>)
  \<Longrightarrow> \<lparr>prod_lhs = A1, prod_rhs = \<beta>2\<rparr> \<in> cfg_productions G'
  \<Longrightarrow> \<lparr>prod_lhs = A2, prod_rhs = []\<rparr> \<in> cfg_productions G'
  \<Longrightarrow> False"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and n="n1"
      in cfgRM_derivation_to_Esplit_derivation)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d2a S)(*strict*)
  apply(rename_tac d1x S1)
  apply(rename_tac d1x S1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d2"
      and n="n2"
      in cfgRM_derivation_to_Esplit_derivation)
     apply(rename_tac d1x S1)(*strict*)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def)
     apply(force)
    apply(rename_tac d1x S1)(*strict*)
    apply(force)
   apply(rename_tac d1x S1)(*strict*)
   apply(force)
  apply(rename_tac d1x S1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2a S)(*strict*)
  apply(rename_tac d2x S2)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "EValidSplit G' S1")
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(subgoal_tac "S1 \<in> SSC" for SSC)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1x"
      in Esplit.belongs_configurations)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(rule Esplit.derivation_initial_belongs)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(simp add: Esplit_configurations_def)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "EValidSplit G' S2")
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(subgoal_tac "S2 \<in> SSC" for SSC)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2x"
      in Esplit.belongs_configurations)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(rule Esplit.derivation_initial_belongs)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(simp add: Esplit_configurations_def)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   prefer 2
   apply(rule_tac
      S="S1"
      and e="\<lparr>prod_lhs = A1, prod_rhs = \<beta>2\<rparr>"
      and w="\<beta>1 @ teA A1 # teB b # liftB \<alpha>3"
      and w'="\<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>3"
      in ESplit_cfgRM_step_can_be_simulated)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n1"
      and m="Suc n1"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S')(*strict*)
  apply(rename_tac S1x)
  apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   prefer 2
   apply(rule_tac
      S="S2"
      and e="\<lparr>prod_lhs = A2, prod_rhs = []\<rparr>"
      and w="\<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2"
      and w'="\<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ liftB \<alpha>2"
      in ESplit_cfgRM_step_can_be_simulated)
      apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="n2"
      and m="Suc n2"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1x S')(*strict*)
  apply(rename_tac S2x)
  apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
   prefer 2
   apply(rule_tac
      S="S1x"
      and b="b"
      and x="liftB \<alpha>3"
      and v="\<beta>1 @ \<beta>2"
      in EValidSplit_take_prefix)
      apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1x S2x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S2a)(*strict*)
  apply(rename_tac S1a S1b)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
   prefer 2
   apply(rule_tac
      S="S2x"
      and b="b"
      and x="liftB \<alpha>1 @ liftB \<alpha>2"
      and v="\<beta>1 @ \<beta>2"
      in EValidSplit_take_prefix)
      apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S2x S1a S1b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S1c S2a)(*strict*)
  apply(rename_tac S2a S2b)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      ?S1.0="S1a"
      and S1'="S1b"
      and ?S2.0="S2a"
      and S2'="S2b"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and ?n1.0="Suc n1"
      and ?n2.0="Suc n2"
      and v="\<beta>1 @ \<beta>2"
      and b="b"
      and ?x1.0="Esplit_signature S1b"
      in equal_split_prefix)
                  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                  apply(force)
                 apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                 apply(force)
                apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
                apply(force)
               apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
               apply(force)
              apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
              apply(force)
             apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
             apply(force)
            apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
            apply(force)
           apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
           apply(force)
          apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
          apply(force)
         apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
         apply(force)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "setA (Esplit_signature S1b) = {}")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply (simp add: Esplit_signature_append)
   apply(rule setA_liftB)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "setA (Esplit_signature S2b) = {}")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply (simp add: Esplit_signature_append)
   apply(simp add: setAConcat setA_liftB)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply (simp add: Esplit_signature_append)
  apply(subgoal_tac "EValidSplitExt S1")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and G'="G"
      and d="d1x"
      and n="n1"
      in Esplit_derivation_enforces_EValidSplitExt)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "EValidSplitExt S2")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and G'="G"
      and d="d2x"
      and n="n2"
      in Esplit_derivation_enforces_EValidSplitExt)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "EValidSplitExt (S1a@S1b)")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and G'="G"
      and d="derivation_append d1x (der2 S1 \<lparr>prod_lhs = A1, prod_rhs = \<beta>2\<rparr> (S1a @ S1b)) n1"
      and n="Suc n1"
      in Esplit_derivation_enforces_EValidSplitExt)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(rule Esplit.derivation_append_preserves_derivation_initial)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(rule Esplit.derivation_append_preserves_derivation)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(rule Esplit.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(rule Esplit.der2_is_derivation)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(subgoal_tac "EValidSplitExt (S2a@S2b)")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and G'="G"
      and d="derivation_append d2x (der2 S2 \<lparr>prod_lhs = A2, prod_rhs = []\<rparr> (S2a @ S2b)) n2"
      and n="Suc n2"
      in Esplit_derivation_enforces_EValidSplitExt)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
       apply(simp add: Esplit_TSstructure_def F2LR1input_def)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(rule Esplit.derivation_append_preserves_derivation_initial)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(simp add: Esplit_TSstructure_def F2LR1input_def)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(rule Esplit.derivation_append_preserves_derivation)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
      apply(rule Esplit.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
     apply(rule Esplit.der2_is_derivation)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b)(*strict*)
  apply(case_tac A1)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n1"
      and \<pi>="map the (get_labels d1 n1)"
      in cfgRM_reachable_only_l3_nonterminals)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(rule cfgRM.derivation_initial_belongs)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(simp add: split_TSstructure_def)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(simp add: cfgRM.trans_der_def cfgRM.derivation_initial_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply (metis get_labels_length)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(rule_tac
      G="G'"
      in cfgRM.get_labels_the_Some_on_defined_positions)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(rule conjI)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
       apply(case_tac "d1 0")
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
        apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba a option baa)(*strict*)
       apply(clarsimp)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba baa)(*strict*)
       apply(simp add: cfg_initial_configurations_def)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
      apply (metis get_labels_length)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
   apply(rule_tac
      xs="teB b # Esplit_signature S1b"
      in rev_cases)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast (\<beta>1 @ teA (cons_l2   q ba) # ys @ [y]) = SSX" for SSX)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q ba ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: filterA_distrib_append filterA_liftB)
   apply (metis only_l3_nonterminals_drop only_l3_nonterminals_l2_at_front)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
   prefer 2
   apply(rule_tac
      Sa="S1a"
      and Sb="S1b"
      in get_revert_prod_sound)
               apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
               apply(force)
              apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
              apply(force)
             apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
             prefer 2
             apply(force)
            apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
            prefer 3
            apply(force)
           apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
           prefer 3
           apply(force)
          apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
          prefer 3
          apply(force)
         apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
         apply(force)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
  apply(subgoal_tac "get_revert_prod (restrict G G' (S2a @ S2b) (length S2a)) = Some \<lparr>prod_lhs = cons_l3 q1 ba q2, prod_rhs = \<beta>2\<rparr>")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
  apply(simp add: get_revert_prod_def)
  apply(case_tac "get_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2)))")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_DT_revert_position_def)
  apply(case_tac "\<exists>rp. is_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))) rp")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
  apply(thin_tac "get_prod_at_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))) (THE rp. is_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))) rp \<and> (\<forall>rp'. is_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))) rp' \<longrightarrow> leq rp rp')) = \<lparr>prod_lhs = cons_l3 q1 ba q2, prod_rhs = \<beta>2\<rparr>")
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
  apply(subgoal_tac "restrict G G' S2 (length (\<beta>1 @ \<beta>2 @ [teB b])) = restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))")
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
   apply(rule_tac
      w="\<beta>1@\<beta>2@[teB b]"
      and S="S2"
      in no_pre_DT_revert_position)
         apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
         apply(force)
        apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
        apply(force)
       apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
       apply(force)
      apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
      apply(force)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
    apply(rule_tac
      t="restrict G G' S2 (length (\<beta>1 @ \<beta>2 @ [teB b]))"
      and s="restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))"
      in ssubst)
     apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
     apply(force)
    apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
    apply(force)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
  apply(thin_tac "cfgRM.derivation_initial G' d1")
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>cfg_conf = \<beta>1 @ teA (cons_l3   q1 ba q2) # teB b # liftB \<alpha>3\<rparr>)")
  apply(thin_tac "d1 (Suc n1) = Some (pair (Some \<lparr>prod_lhs = cons_l3 q1 ba q2, prod_rhs = \<beta>2\<rparr>) \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>3\<rparr>)")
  apply(thin_tac "cfgRM.derivation_initial G' d2")
  apply(thin_tac "d2 n2 = Some (pair e2 \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2\<rparr>)")
  apply(thin_tac "d2 (Suc n2) = Some (pair (Some \<lparr>prod_lhs = A2, prod_rhs = []\<rparr>) \<lparr>cfg_conf = \<beta>1 @ \<beta>2 @ teB b # liftB \<alpha>1 @ liftB \<alpha>2\<rparr>)")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 q1 ba q2, prod_rhs = \<beta>2\<rparr> \<in> cfg_productions G'")
  apply(thin_tac "\<lparr>prod_lhs = A2, prod_rhs = []\<rparr> \<in> cfg_productions G'")
  apply(thin_tac "Esplit.derivation_initial G' d1x")
  apply(thin_tac "d1x n1 = Some (pair e1 S1)")
  apply(thin_tac "Esplit_signature S1 = \<beta>1 @ teA (cons_l3   q1 ba q2) # teB b # liftB \<alpha>3")
  apply(thin_tac "get_labels d1x n1 = get_labels d1 n1")
  apply(thin_tac "Esplit.derivation_initial G' d2x")
  apply(thin_tac "d2x n2 = Some (pair e2 S2)")
  apply(thin_tac "get_labels d2x n2 = get_labels d2 n2")
  apply(thin_tac "EValidSplit G' S1")
  apply(thin_tac "EValidSplit G' (S1a @ S1b)")
  apply(thin_tac "Esplit_step_relation G' S1 \<lparr>prod_lhs = cons_l3 q1 ba q2, prod_rhs = \<beta>2\<rparr> (S1a @ S1b)")
  apply(thin_tac "Esplit_signature S1a = \<beta>1 @ \<beta>2 @ [teB b]")
  apply(thin_tac "length S1a = Suc (length \<beta>1 + length \<beta>2)")
  apply(thin_tac "Esplit_signature S1b = liftB \<alpha>3")
  apply(thin_tac "restrict G G' (S1a @ S1b) (Suc (length \<beta>1 + length \<beta>2)) = restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))")
  apply(thin_tac "setA (liftB \<alpha>3) = {}")
  apply(thin_tac "setA (liftB \<alpha>1 @ liftB \<alpha>2) = {}")
  apply(thin_tac "EValidSplitExt S1")
  apply(thin_tac "EValidSplitExt (S1a @ S1b)")
  apply(thin_tac "is_DT_revert_position (restrict G G' (S2a @ S2b) (Suc (length \<beta>1 + length \<beta>2))) rp")
  apply(rule_tac
      t="length (\<beta>1 @ \<beta>2 @ [teB b])"
      and s="Suc(length (\<beta>1 @ \<beta>2))"
      in ssubst)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
  apply(rule_tac
      t="Suc (length \<beta>1 + length \<beta>2)"
      and s="Suc(length (\<beta>1 @ \<beta>2))"
      in ssubst)
   apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
   apply(force)
  apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
  apply(rule_tac restrict_equal_before_step_nonterminal)
            apply(rename_tac d1x S1 d2x S2 S1a S1b S2a S2b q1 ba q2 rp)(*strict*)
            apply(force)+
  done

theorem F_SDPDA_TO_CFG_STD__enforces_cfg_LRk: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> \<not> duplicate_marking G
  \<Longrightarrow> cfg_LRk G' (Suc 0)"
  apply(subgoal_tac "valid_cfg (F_SDPDA_TO_CFG_STD G)")
   prefer 2
   apply (metis F_SDPDA_TO_CFG_STD__makes_CFG)
  apply(subgoal_tac "F2LR1inputx G' G")
   prefer 2
   apply(simp add: F2LR1inputx_def)
   apply(rule duplicate_marking_to_duplicate_markingH)
    apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
   apply(force)
  apply(subgoal_tac "split_TSstructure G'")
   prefer 2
   apply(rule F2LR1input_implies_split_TSstructure)
   apply(simp add: F2LR1input_def)
   apply(force)
  apply(simp add: cfg_LRk_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(case_tac "y1")
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2)(*strict*)
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in F_SDPDA_TO_CFG_STD__enforces_cfg_LRk_1)
               apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2)(*strict*)
               apply(force)+
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a list)(*strict*)
  apply(rename_tac a w1)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1)(*strict*)
  apply(case_tac v)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1)(*strict*)
   apply(case_tac y2)
    apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1 aa list)(*strict*)
   apply(rename_tac b w2)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1 b w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 a w1 b w2)(*strict*)
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and d="d1"
      and n="n1"
      and m="Suc n1"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l r)(*strict*)
   apply(subgoal_tac "r=teB b # liftB w1")
    apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l r)(*strict*)
    prefer 2
    apply (metis Cons_eq_appendI setA_liftB liftB.simps(2) append_Nil terminalTailEquals1)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and d="d2"
      and n="n2"
      and m="Suc n2"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l la r)(*strict*)
   apply(subgoal_tac "r=teB b # liftB w2")
    apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l la r)(*strict*)
    prefer 2
    apply (metis Cons_eq_appendI setA_liftB liftB.simps(2) append_Nil terminalTailEquals1)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 e2 e2' \<omega>2 w1 b w2 l la r)(*strict*)
   apply(clarsimp)
   apply(thin_tac "setA (liftB w1) = {}")
   apply(thin_tac "setA (liftB w2) = {}")
   apply(rename_tac \<delta>1 \<delta>2)
   apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and G'="G"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in LR1_property_part2)
            apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
            apply(force)
           apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 e1' d2 n2 e2 e2' w1 b w2 l la)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v a w1 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 a w1 aa list)(*strict*)
  apply(simp add: kPrefix_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and d="d1"
      and n="n1"
      and m="Suc n1"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l r)(*strict*)
  apply(subgoal_tac "r=teB aa # liftB w1")
   apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l r)(*strict*)
   prefer 2
   apply (metis Cons_eq_appendI setA_liftB liftB.simps(2) append_Nil terminalTailEquals1)
  apply(rename_tac d1 n1 \<delta>1 A1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and d="d2"
      and n="n2"
      and m="Suc n2"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l la r)(*strict*)
  apply(subgoal_tac "r=liftB y2")
   apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l la r)(*strict*)
   prefer 2
   apply (metis Cons_eq_appendI setA_liftB liftB.simps(2) append_Nil terminalTailEquals1)
  apply(rename_tac d1 n1 e1 e1' d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 w1 aa list l la r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 e1' d2 n2 y2 e2 e2' w1 aa list l la)(*strict*)
  apply(thin_tac "setA (liftB y2) = {}")
  apply(thin_tac "setA (liftB w1) = {}")
  apply(case_tac e1')
  apply(rename_tac d1 n1 e1 e1' d2 n2 y2 e2 e2' w1 aa list l la prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac e2')
  apply(rename_tac d1 n1 e1 e1' d2 n2 y2 e2 e2' w1 aa list l la prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
  apply(rename_tac b \<alpha> l1 cons_l2 A1 r1 A2 r2)
  apply(rename_tac d1 n1 e1 e1' d2 n2 y2 e2 e2' w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
  apply(rule_tac
      xs="r2"
      in rev_cases)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
   prefer 2
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2 ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y)(*strict*)
   apply(subgoal_tac "LR1ProdForm G'")
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def F2LR1inputx_def)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y)(*strict*)
   apply(simp add: LR1ProdForm_def)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = A2, prod_rhs = ys @ [y]\<rparr>"
      in ballE)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y)(*strict*)
    prefer 2
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y ba q1 q2 q3 q4 A1a)(*strict*)
   apply(erule disjE)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y ba q1 q2 q3 q4 A1a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 ba q1 q2 A1a)(*strict*)
    apply(rule_tac
      xs="\<alpha>"
      in rev_cases)
     apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 ba q1 q2 A1a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 ba q1 q2 A1a ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b l1 l2a A1 r1 ba q1 q2 A1a ys y)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y ba q1 q2 q3 q4 A1a)(*strict*)
   apply(erule disjE)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y ba q1 q2 q3 q4 A1a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 ba q1 q2 q3 A1a)(*strict*)
    apply(rule_tac
      xs="\<alpha>"
      in rev_cases)
     apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 ba q1 q2 q3 A1a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 ba q1 q2 q3 A1a ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b l1 cons_l2 A1 r1 ba q1 q2 q3 A1a ys y)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y ba q1 q2 q3 q4 A1a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y q1 q2 q3 q4 A1a A2a)(*strict*)
   apply(erule disjE)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y q1 q2 q3 q4 A1a A2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 A1a A2a)(*strict*)
    apply(rule_tac
      xs="\<alpha>"
      in rev_cases)
     apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 A1a A2a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 A1a A2a ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b l1 l2a A1 r1 q1 q2 A1a A2a ys y)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y q1 q2 q3 q4 A1a A2a)(*strict*)
   apply(erule disjE)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 A2 ys y q1 q2 q3 q4 A1a A2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 q3 A1a A2a)(*strict*)
    apply(rule_tac
      xs="\<alpha>"
      in rev_cases)
     apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 q3 A1a A2a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 l2a A1 r1 q1 q2 q3 A1a A2a ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b l1 l2a A1 r1 q1 q2 q3 A1a A2a ys y)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 ys y q1 q2 q3 q4 A1a A2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 q1 q2 q3 q4 A1a A2a)(*strict*)
   apply(rule_tac
      xs="\<alpha>"
      in rev_cases)
    apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 q1 q2 q3 q4 A1a A2a)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 q1 q2 q3 q4 A1a A2a ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b l1 cons_l2 A1 r1 q1 q2 q3 q4 A1a A2a ys y)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 cons_l2 A1 r1 A2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 n1 e1 d2 n2 y2 e2 w1 b \<alpha> l1 A1 r1 A2)(*strict*)
  apply(rename_tac \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)
  apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
  apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in F_SDPDA_TO_CFG_STD__enforces_cfg_LRk_3)
           apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
           apply(force)
          apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
          apply(force)
         apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
         apply(force)
        apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
        apply(force)
       apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
       apply(force)
      apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
      apply(force)
     apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 e1 d2 n2 \<alpha>2 e2 \<alpha>3 b \<alpha>1 \<beta>1 A1 \<beta>2 A2)(*strict*)
  apply(force)
  done

hide_fact first_empty_rhs_with_left_degen_front
hide_fact F_SDPDA_TO_CFG_STD__enforces_cfg_LRk_3
hide_fact get_DT_revert_position_eq
hide_fact get_DT_revert_position_eq2
hide_fact get_revert_prod_sound
hide_fact get_revert_prod_sound_rhs_empty
hide_fact get_revert_prod_sound_rhs_push
hide_fact get_revert_prod_sound_rhs_read
hide_fact leq_elim_elim
hide_fact leq_elim_gen
hide_fact leq_gen_elim
hide_fact leq_gen_gen
hide_fact leq_leq_eq
hide_fact LR1_property_part2
hide_fact LR1_property_part2_equal_productions
hide_fact LR1_property_part2_equal_productions2
hide_fact no_pre_DT_revert_position
hide_fact THE_get_DT_revert_position_eq
  (* important F_SDPDA_TO_CFG_STD__enforces_cfg_LRk *)

end
