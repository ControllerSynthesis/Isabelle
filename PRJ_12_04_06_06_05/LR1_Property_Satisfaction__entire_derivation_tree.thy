section {*LR1\_Property\_Satisfaction\_\_entire\_derivation\_tree*}
theory
  LR1_Property_Satisfaction__entire_derivation_tree

imports
  PRJ_12_04_06_06_05__ENTRY

begin

record ('q,'s,'t) ESplitItem =
  ESplitItem_elim :: "('q,'s) DT_l2_l3_nonterminals list"
  ESplitItem_from :: "('q,'s) DT_l2_l3_nonterminals option"
  ESplitItem_ignore :: "('q,'s) DT_l2_l3_nonterminals list"
  ESplitItem_elim_prods :: "(('q,'s) DT_l2_l3_nonterminals, 't) cfg_step_label list list"
  ESplitItem_prods :: "((('q,'s) DT_l2_l3_nonterminals, 't) cfg_step_label) list"
  ESplitItem_elem :: "(('q,'s) DT_l2_l3_nonterminals, 't) DT_two_elements option"
  ESplitItem_to :: "('q,'s) DT_l2_l3_nonterminals list"

type_synonym ('q,'s,'t) ESplit = "('q,'s,'t) ESplitItem list"

definition EValidSplit_interlineX :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "EValidSplit_interlineX S1 S2 \<equiv>
  ESplitItem_elim S2 @ option_to_list (ESplitItem_from S2) @ ESplitItem_ignore S2
  = ESplitItem_to S1 @ ESplitItem_ignore S1"

definition EValidSplit_interline :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_interline S \<equiv>
  \<forall>i. Suc i < length S \<longrightarrow> EValidSplit_interlineX (S ! i) (S ! Suc i)"

definition EValidSplit_initial :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_initial G S \<equiv>
    ((ESplitItem_elim (hd S) = [] \<and> ESplitItem_from (hd S) = Some (cfg_initial G)) 
     \<or> (ESplitItem_elim (hd S) = [cfg_initial G] \<and> ESplitItem_from (hd S) = None))
  \<and> ESplitItem_ignore (hd S) = []"

definition EValidSplit_to_empty :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_to_empty G S \<equiv>
  \<forall>x \<in> set (butlast S) . 
   ESplitItem_to x = [] \<longrightarrow> 
      ESplitItem_prods x = [] 
      \<and> option_to_list (ESplitItem_elem x) = liftA (option_to_list (ESplitItem_from x))"

definition EValidSplit_final :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_final G S \<equiv>
  ESplitItem_to (last S) = [] \<and> ESplitItem_ignore (last S) = []"

definition EValidSplit_producing :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_producing G S \<equiv>
  \<forall>x \<in> set (butlast S). ESplitItem_from x \<noteq> None \<and> ESplitItem_elem x \<noteq> None"

definition EValidSplit_produce_or_elim :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_produce_or_elim G S \<equiv>
  \<forall>x \<in> set S. ESplitItem_from x = None \<longrightarrow> ESplitItem_elim x \<noteq> []"

definition EValidSplitItem_gen :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "EValidSplitItem_gen G S \<equiv>
    \<exists>d. cfgLM.trans_der G d 
        \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from S))\<rparr> 
        (ESplitItem_prods S)
        \<lparr>cfg_conf = (option_to_list (ESplitItem_elem S)) @ liftA (ESplitItem_to S)\<rparr>
  \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem S)
      \<longrightarrow> (\<forall>i < length (ESplitItem_prods S) . 
            hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the (ESplitItem_elem S)))
  \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem S)
      \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods S = [])"

definition EValidSplitItem_elim :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "EValidSplitItem_elim G S \<equiv>
  length (ESplitItem_elim_prods S) = length (ESplitItem_elim S)
  \<and> elim_map G (ESplitItem_elim S) (ESplitItem_elim_prods S) (map (\<lambda>x.[]) (ESplitItem_elim_prods S))"

definition EValidSplitItem_belongs :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "EValidSplitItem_belongs G S \<equiv>
    set (ESplitItem_elim S) \<subseteq> cfg_nonterminals G
  \<and> set (ESplitItem_ignore S) \<subseteq> cfg_nonterminals G
  \<and> set (option_to_list (ESplitItem_from S)) \<subseteq> cfg_nonterminals G
  \<and> set (ESplitItem_to S) \<subseteq> cfg_nonterminals G
  \<and> setA (option_to_list (ESplitItem_elem S)) \<subseteq> cfg_nonterminals G
  \<and> setB (option_to_list (ESplitItem_elem S)) \<subseteq> cfg_events G
  \<and> set ((ESplitItem_prods S)) \<subseteq> cfg_productions G
  \<and> (\<forall>x\<in> set (ESplitItem_elim_prods S) . set x \<subseteq> cfg_productions G)
  \<and> proper_l3_l2_seq (ESplitItem_elim S @ (option_to_list (ESplitItem_from S)) @ ESplitItem_ignore S)
  \<and> (filterA (option_to_list (ESplitItem_elem S)) @ (ESplitItem_to S) @ (ESplitItem_ignore S) \<noteq> [] \<longrightarrow> proper_l3_l2_seq (filterA (option_to_list (ESplitItem_elem S)) @ (ESplitItem_to S) @ (ESplitItem_ignore S)))"

definition EValidSplitItem :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "EValidSplitItem G S \<equiv>
  EValidSplitItem_belongs G S
  \<and> EValidSplitItem_elim G S
  \<and> EValidSplitItem_gen G S"

definition EValidSplit_ValidItem :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit_ValidItem G S \<equiv>
  \<forall>x \<in> set S. EValidSplitItem G x"

definition EValidSplit :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplit G S \<equiv>
  EValidSplit_interline S
  \<and> S \<noteq> []
  \<and> EValidSplit_initial G S
  \<and> EValidSplit_to_empty G S
  \<and> EValidSplit_final G S
  \<and> EValidSplit_producing G S
  \<and> EValidSplit_produce_or_elim G S
  \<and> EValidSplit_ValidItem G S"

definition Esplit_TSstructure :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> bool"
  where
    "Esplit_TSstructure G \<equiv>
  split_TSstructure G \<and> F2LR1input G"

definition Esplit_configurations :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit set"
  where
    "Esplit_configurations G \<equiv>
  {S. EValidSplit G S}"

definition Esplit_initial_configurations :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit set"
  where
    "Esplit_initial_configurations G \<equiv>
  {[\<lparr>ESplitItem_elim = [],
  ESplitItem_from = Some (cfg_initial G),
  ESplitItem_ignore = [],
  ESplitItem_elim_prods = [],
  ESplitItem_prods = [],
  ESplitItem_elem = Some (teA (cfg_initial G)),
  ESplitItem_to = []\<rparr>]}"

definition Esplit_step_labels :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label set"
  where
    "Esplit_step_labels G \<equiv>
  cfg_productions G"

definition Xstep_gen :: "
  ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 's, 't) ESplit"
  where
    "Xstep_gen w v \<equiv>
  if w = []
  then []
  else map 
      (\<lambda>n. 
      \<lparr>ESplitItem_elim = [],
      ESplitItem_from = Some (w ! n),
      ESplitItem_ignore = drop (Suc n) w @ v,
      ESplitItem_elim_prods = [],
      ESplitItem_prods = [],
      ESplitItem_elem = Some (teA (w ! n)),
      ESplitItem_to = []\<rparr>)
      (nat_seq 0 (length w - Suc 0))"

definition Xstep_elem :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label
  \<Rightarrow> ('q, 's, 't) ESplitItem"
  where
    "Xstep_elem I p \<equiv>
  I
    \<lparr>ESplitItem_prods := ESplitItem_prods I @ [p],
    ESplitItem_elem := nth_opt (prod_rhs p) 0,
    ESplitItem_to := filterA (drop (Suc 0) (prod_rhs p)) @ ESplitItem_to I\<rparr>"

(*
  prefix to1 elim2
  to1 @ c = elim2

  elim1 @ from1 @ ignore1 = to0 @ ignore0
  elim2 @ from2 @ ignore2 = to1 @ ignore1

  post_interface = to2 @ ignore2
  post_interface' = to2 @ ignore2
  compatibility: trivial

  pre_interface = elim1 @ from1 @ ignore1
  pre_interface' = elim1 @ from1 @ c @ from2 @ ignore2
  compatibility:
  elim1 @ from1 @ ignore1 = elim1 @ from1 @ c @ from2 @ ignore2
  \<Leftarrow> ignore1 = c @ from2 @ ignore2
  \<Leftarrow> to1 @ ignore1 = to1 @ c @ from2 @ ignore2
  \<Leftarrow> elim2 @ from2 @ ignore2 = elim2 @ from2 @ ignore2

*)

definition Xstep_merge1_toWasEliminated :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem"
  where
    "Xstep_merge1_toWasEliminated S1 S2 \<equiv>
  \<lparr>ESplitItem_elim = 
        ESplitItem_elim S1 
        @ (option_to_list (ESplitItem_from S1)) 
        @ (drop (length (ESplitItem_to S1)) (ESplitItem_elim S2)),
  ESplitItem_from = ESplitItem_from S2,
  ESplitItem_ignore = ESplitItem_ignore S2,
  ESplitItem_elim_prods = 
        (ESplitItem_elim_prods S1) 
        @ [(ESplitItem_prods S1) @ (foldl (@) [] (take (length (ESplitItem_to S1)) (ESplitItem_elim_prods S2)))] 
        @ (drop (length (ESplitItem_to S1)) (ESplitItem_elim_prods S2)),
  ESplitItem_prods = ESplitItem_prods S2,
  ESplitItem_elem = ESplitItem_elem S2,
  ESplitItem_to = ESplitItem_to S2\<rparr>"

(*
  elim2 @ c = to1
  c\<noteq>[]
  elim1 @ from1 @ ignore1 = to0 @ ignore0
  elim2 @ from2 @ ignore2 = to1 @ ignore1

  post_interface = to2 @ ignore2
  post_interface' = to2 @ c @ ignore1
  compatibility:
  to2 @ ignore2 = to2 @ c @ ignore1
  \<Leftarrow> ignore2 = c @ ignore1
  \<Leftarrow> elim2 @ from2 @ ignore2 = elim2 @ from2 @ c @ ignore1
  \<Leftarrow> to1 @ ignore1 = to1 @ ignore1

  pre_interface = elim1 @ from1 @ ignore1
  pre_interface' = elim1 @ from1 @ ignore1
  compatibility: trivial
*)
definition Xstep_merge1_toWasNotEliminated :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem"
  where
    "Xstep_merge1_toWasNotEliminated S1 S2 \<equiv>
  \<lparr>ESplitItem_elim = ESplitItem_elim S1,
  ESplitItem_from = ESplitItem_from S1,
  ESplitItem_ignore = ESplitItem_ignore S1,
  ESplitItem_elim_prods = ESplitItem_elim_prods S1,
  ESplitItem_prods = 
      ESplitItem_prods S1 
      @ (foldl (@) [] (ESplitItem_elim_prods S2)) 
      @ (ESplitItem_prods S2),
  ESplitItem_elem = ESplitItem_elem S2,
  ESplitItem_to = 
      ESplitItem_to S2 
      @ (drop (length ((ESplitItem_elim S2) @ (option_to_list (ESplitItem_from S2)))) (ESplitItem_to S1))\<rparr>"

definition Xstep_merge1 :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem
  \<Rightarrow> ('q, 's, 't) ESplitItem"
  where
    "Xstep_merge1 S1 S2 \<equiv>
  if strict_prefix (ESplitItem_elim S2) (ESplitItem_to S1)
  then Xstep_merge1_toWasNotEliminated S1 S2
  else Xstep_merge1_toWasEliminated S1 S2"

definition EmptyESplitItem :: "
  ('q, 's, 't) ESplitItem"
  where
    "EmptyESplitItem \<equiv>
  \<lparr>ESplitItem_elim = [],
  ESplitItem_from = None,
  ESplitItem_ignore = [],
  ESplitItem_elim_prods = [],
  ESplitItem_prods = [],
  ESplitItem_elem = None,
  ESplitItem_to = []\<rparr>"

definition Xstep_mergeL :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> ('q, 's, 't) ESplitItem option
  \<Rightarrow> ('q, 's, 't) ESplit"
  where
    "Xstep_mergeL I1S I2 \<equiv>
  (butlast I1S) 
  @ (case I2 of 
  None \<Rightarrow> (case ESplitItem_elem (last I1S) of 
    None \<Rightarrow> [Xstep_merge1 (last I1S) EmptyESplitItem]
    | Some e \<Rightarrow> [(last I1S)])
  | Some I2 \<Rightarrow> (case ESplitItem_elem (last I1S) of 
    None \<Rightarrow> [Xstep_merge1 (last I1S) I2]
    | Some e \<Rightarrow> [(last I1S), I2]))"

definition Esplit_signature :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements list"
  where
    "Esplit_signature S \<equiv>
  foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S)"

definition Esplit_step_relation :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "Esplit_step_relation G S e S' \<equiv>
  e \<in> cfg_productions G
  \<and> (\<exists>S1 SL S2. 
    S = S1 @ [SL] @ S2
    \<and> setA (Esplit_signature S2) = {}
    \<and> ESplitItem_elem SL = Some (teA (prod_lhs e))
    \<and> S' = S1 
          @ Xstep_mergeL 
              (Xstep_elem SL e
                # Xstep_gen (filterA (tl (prod_rhs e))) (ESplitItem_to SL @ ESplitItem_ignore SL)) 
              (nth_opt S2 0)
          @ drop (Suc 0) S2)"

definition Esplit_effects :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> 't list set"
  where
    "Esplit_effects G \<equiv>
  {w. (set w \<subseteq> cfg_events G) }"

definition Esplit_marking_condition :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> (nat
  \<Rightarrow> ((('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label, ('q, 's, 't) ESplit) derivation_configuration option)
  \<Rightarrow> bool"
  where
    "Esplit_marking_condition G d \<equiv>
  \<exists>n e c. d n = Some (pair e c) \<and> setA (Esplit_signature c) = {}"

definition Esplit_marked_effect :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> (nat
  \<Rightarrow> ((('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label, ('q, 's, 't) ESplit) derivation_configuration option)
  \<Rightarrow> ('t list) set"
  where
    "Esplit_marked_effect G d \<equiv>
  {w. \<exists>n e c. d n = Some (pair e c) \<and> setA (Esplit_signature c) = {} \<and> w = filterB (Esplit_signature c)}"

definition Esplit_unmarked_effect :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> (nat
  \<Rightarrow> ((('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label, ('q, 's, 't) ESplit) derivation_configuration option)
  \<Rightarrow> 't list set"
  where
    "Esplit_unmarked_effect G d \<equiv>
  {w. \<exists>n e c. d n = Some (pair e c) \<and> w = maximalPrefixB (Esplit_signature c)}"

lemma Esplit_inst_AX_initial_configuration_belongs: "
  (\<forall>G. Esplit_TSstructure G \<longrightarrow>
         Esplit_initial_configurations G \<subseteq> Esplit_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: Esplit_initial_configurations_def Esplit_configurations_def)
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: EValidSplit_def)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_interline_def)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_initial_def)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_to_empty_def option_to_list_def)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_final_def)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_producing_def)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplit_produce_or_elim_def)
  apply(rename_tac G)(*strict*)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(simp add: EValidSplitItem_def)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplitItem_belongs_def)
   apply(simp add: option_to_list_def)
   apply(rule conjI)
    apply(rename_tac G)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(simp add: only_l3_nonterminals_def only_l3_nonterminals_and_l3_adjacency_def proper_l3_seq_def proper_l3_l2_seq_def F2LR1input_def Esplit_TSstructure_def split_TSstructure_def F2LR1inputx_def cfg_sub_def valid_cfg_def F_SDPDA_TO_CFG_STD_def last_back_state_def)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(simp add: EValidSplitItem_elim_def elim_map_def)
  apply(rename_tac G)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac G)(*strict*)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac G)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def cfg_configurations_def)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac G i)(*strict*)
  apply(case_tac i)
   apply(rename_tac G i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac G i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G nat)(*strict*)
  apply(simp add: der1_def)
  done

lemma EValidSplit_interline_preserve: "
  S=S1@[B]@S2
  \<Longrightarrow> EValidSplit_interline (S1@[A]@S2)
  \<Longrightarrow> (\<And>S1' S1L. S1=S1'@[S1L] \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX S1L B)
  \<Longrightarrow> (\<And>S2' S2F. S2=S2F#S2' \<Longrightarrow> EValidSplit_interlineX A S2F \<Longrightarrow> EValidSplit_interlineX B S2F)
  \<Longrightarrow> EValidSplit_interline S"
  apply(clarsimp)
  apply(simp (no_asm) add: EValidSplit_interline_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "Suc i<length S1")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply (metis List.nth_append Suc_lessD)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1\<le>Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length S1=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(erule_tac
      x="w'"
      and P="\<lambda>S1'. (\<And> S1L. w' = S1' \<and> a' = S1L \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX S1L B)"
      in meta_allE)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="a'"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac w' a')(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="length w'"
      in allE)
    apply(clarsimp)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac w' a')(*strict*)
   apply (metis ConsApp Suc_length append_assoc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1<Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc(length S1)=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac S2)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ B # a # list) ! (Suc (length S1))"
      and s="a"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply (metis ConsApp append_assoc length_Suc nth_append_length)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="list"
      and P="\<lambda>S2'. (\<And>S2F. a = S2F \<and> list = S2' \<Longrightarrow> EValidSplit_interlineX A S2F \<Longrightarrow> EValidSplit_interlineX B S2F)"
      in meta_allE)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="a"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="length S1"
      in allE)
   apply(clarsimp)
   apply (metis ConsApp append_assoc length_Suc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(simp add: EValidSplit_interline_def)
  apply(subgoal_tac "(length S1) < i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac i)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(erule impE)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(S1 @ B # S2) ! Suc i"
      and s="(S1 @ A # S2) ! Suc i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(S1 @ B # S2) ! Suc i"
      and s=" S2 ! (Suc i-length(S1 @ B #[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ B # S2"
      and s="(S1 @ B #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ A # S2) ! Suc i"
      and s=" S2 ! (Suc i-length(S1 @ A#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ A # S2"
      and s="(S1 @ A #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(S1 @ B# S2) ! Suc (Suc i)"
      and s="(S1 @ A # S2) ! (Suc (Suc i))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(S1 @ B # S2) ! Suc (Suc i)"
      and s=" S2 ! (Suc (Suc i)-length(S1 @ B #[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ B # S2"
      and s="(S1 @ B #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ A # S2) ! (Suc (Suc i))"
      and s=" S2 ! ((Suc (Suc i))-length(S1 @ A#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ A # S2"
      and s="(S1 @ A #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma EValidSplit_interline_shrink: "
  S=(S1@C#S2)
  \<Longrightarrow> EValidSplit_interline (S1@[A,B]@S2)
  \<Longrightarrow> (\<And>S1' S1L. S1=S1'@[S1L] \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX S1L C)
  \<Longrightarrow> (\<And>S2' S2F. S2=S2F#S2' \<Longrightarrow> EValidSplit_interlineX B S2F \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX C S2F)
  \<Longrightarrow> EValidSplit_interline S"
  apply(simp (no_asm) add: EValidSplit_interline_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "Suc i<length S1")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply (metis List.nth_append Suc_lessD)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1\<le>Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length S1=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(erule_tac
      x="w'"
      and P="\<lambda>S1'. (\<And> S1L. w' = S1' \<and> a' = S1L \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX S1L C)"
      in meta_allE)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="a'"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac w' a')(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="length w'"
      in allE)
    apply(clarsimp)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac w' a')(*strict*)
   apply(erule meta_impE)
    apply(rename_tac w' a')(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="Suc(length w')"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(w' @ a' # A # B # S2) ! Suc (length w')=A")
     apply(rename_tac w' a')(*strict*)
     apply(subgoal_tac "(w' @ a' # A # B # S2) ! Suc (Suc(length w'))=B")
      apply(rename_tac w' a')(*strict*)
      apply(clarsimp)
     apply(rename_tac w' a')(*strict*)
     apply (metis ConsApp Suc_length append_assoc nth_append_length)
    apply(rename_tac w' a')(*strict*)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac w' a')(*strict*)
   apply (metis ConsApp Suc_length append_assoc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1<Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc(length S1)=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac S2)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="list"
      and P="\<lambda>S2'. (\<And>S2F. a = S2F \<and> list = S2' \<Longrightarrow> EValidSplit_interlineX B S2F \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX C S2F)"
      in meta_allE)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="a"
      in meta_allE)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ C # a # list) ! Suc (length S1)"
      and s="a"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac a list)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac a list)(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="Suc(length S1)"
      in allE)
    apply(clarsimp)
    apply (metis ConsApp append_assoc length_Suc nth_append_length)
   apply(rename_tac a list)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac a list)(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ A # B # a # list) ! Suc (length S1)=B")
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac a list)(*strict*)
   apply (metis ConsApp Suc_length append_assoc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "(length S1) < i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac i)
  apply(rename_tac i)(*strict*)
  apply(thin_tac "\<And>S1' S1L. S1 = S1' @ [S1L] \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX S1L C")
  apply(rename_tac i)(*strict*)
  apply(thin_tac "\<And>S2' S2F. S2 = S2F # S2' \<Longrightarrow> EValidSplit_interlineX B S2F \<Longrightarrow> EValidSplit_interlineX A B \<Longrightarrow> EValidSplit_interlineX C S2F")
  apply(rename_tac i)(*strict*)
  apply(simp add: EValidSplit_interline_def)
  apply(erule_tac
      x="Suc (Suc i)"
      in allE)
  apply(erule impE)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(S1 @ C # S2) ! Suc i"
      and s="(S1 @ A # B # S2) ! Suc (Suc i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      v="S2"
      in equivalent_append)
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
  apply(rule_tac
      t="(S1 @ C # S2) ! Suc (Suc i)"
      and s="(S1 @ A # B # S2) ! Suc (Suc (Suc i))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      v="S2"
      in equivalent_append)
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
  done

lemma Esplit_inst_AX_step_relation_preserves_belongs1: "
  Esplit_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2)
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> setA (Esplit_signature S2) = {}
  \<Longrightarrow> ESplitItem_elem SL = Some (teA (prod_lhs e))
  \<Longrightarrow> prod_rhs e = []
       \<Longrightarrow> EValidSplit G
           (S1 @
            Xstep_mergeL
             (Xstep_elem SL e #
              Xstep_gen (filterA (tl (prod_rhs e))) (ESplitItem_to SL @ ESplitItem_ignore SL))
             (nth_opt S2 0) @
            drop (Suc 0) S2)"
  apply(clarsimp)
  apply(simp add: Xstep_gen_def)
  apply(case_tac S2)
   apply(clarsimp)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_mergeL_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(thin_tac "setA (Esplit_signature []) = {}")
   apply(simp add: Xstep_merge1_def)
   apply(simp add: EmptyESplitItem_def Xstep_elem_def Xstep_merge1_toWasEliminated_def Xstep_merge1_toWasNotEliminated_def)
   apply(simp add: strict_prefix_def)
   apply(subgoal_tac "EValidSplit_final G (S1 @ [SL])")
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(simp add: EValidSplit_final_def)
   apply(clarsimp)
   apply(simp add: EValidSplit_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule EValidSplit_interline_preserve)
       apply(force)
      apply(force)
     apply(rename_tac S1' S1L)(*strict*)
     prefer 2
     apply(rename_tac S2' S2F)(*strict*)
     apply(simp add: Xstep_merge1_def)
    apply(rename_tac S1' S1L)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_interlineX_def)
    apply(simp add: option_to_list_def)
   apply(rule conjI)
    apply(simp add: EValidSplit_initial_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(clarsimp)
     apply(case_tac S1)
      apply(clarsimp)
      apply(simp add: option_to_list_def)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac S1)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: EValidSplit_to_empty_def EmptyESplitItem_def option_to_list_def prefix_def Xstep_merge1_toWasNotEliminated_def Xstep_merge1_toWasEliminated_def EValidSplit_to_empty_def Xstep_merge1_def EmptyESplitItem_def option_to_list_def prefix_def)
   apply(rule conjI)
    apply(simp add: EValidSplit_final_def EValidSplit_to_empty_def EmptyESplitItem_def option_to_list_def prefix_def Xstep_merge1_toWasNotEliminated_def Xstep_merge1_toWasEliminated_def EValidSplit_to_empty_def Xstep_merge1_def EmptyESplitItem_def option_to_list_def prefix_def)
   apply(rule conjI)
    apply(simp add: EValidSplit_producing_def EValidSplit_final_def EValidSplit_to_empty_def EmptyESplitItem_def option_to_list_def prefix_def Xstep_merge1_toWasNotEliminated_def Xstep_merge1_toWasEliminated_def EValidSplit_to_empty_def Xstep_merge1_def EmptyESplitItem_def option_to_list_def prefix_def)
   apply(rule conjI)
    apply(simp add: EValidSplit_produce_or_elim_def EValidSplit_producing_def EValidSplit_final_def EValidSplit_to_empty_def EmptyESplitItem_def option_to_list_def prefix_def Xstep_merge1_toWasNotEliminated_def Xstep_merge1_toWasEliminated_def EValidSplit_to_empty_def Xstep_merge1_def EmptyESplitItem_def option_to_list_def prefix_def)
    apply(clarsimp)
   apply(simp add: EValidSplit_ValidItem_def EValidSplit_produce_or_elim_def EValidSplit_producing_def Xstep_merge1_toWasEliminated_def EValidSplit_to_empty_def Xstep_merge1_def EmptyESplitItem_def option_to_list_def prefix_def)
   apply(clarsimp)
   apply(simp add: EValidSplitItem_def)
   apply(rule conjI)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(simp add: option_to_list_def)
   apply(rule conjI)
    apply(simp add: EValidSplitItem_elim_def)
    apply(clarsimp)
    apply(case_tac "ESplitItem_from SL")
     apply(clarsimp)
     apply(simp add: EValidSplit_final_def)
     apply(simp add: EValidSplitItem_gen_def)
     apply(clarsimp)
    apply(rename_tac a)(*strict*)
    apply(simp add: option_to_list_def)
    apply(rule_tac
      ?v1.0="ESplitItem_elim SL"
      in elim_map_compose)
            apply(rename_tac a)(*strict*)
            prefer 7
            apply(force)
           apply(rename_tac a)(*strict*)
           prefer 7
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac a)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac a)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac a)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(thin_tac "\<forall>x\<in> set S1. EValidSplitItem_belongs G x \<and> length (ESplitItem_elim_prods x) = length (ESplitItem_elim x) \<and> elim_map G (ESplitItem_elim x) (ESplitItem_elim_prods x) (map (\<lambda>x. []) (ESplitItem_elim_prods x)) \<and> EValidSplitItem_gen G x")
     apply(rename_tac a)(*strict*)
     apply(thin_tac "\<forall>x\<in> set S1. ESplitItem_to x = [] \<longrightarrow> ESplitItem_prods x = [] \<and> (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) = liftA (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A])")
     apply(rename_tac a)(*strict*)
     apply(simp add: EValidSplitItem_gen_def)
     apply(clarsimp)
     apply(rename_tac a d)(*strict*)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
      apply(rename_tac a d)(*strict*)
      prefer 2
      apply(rule_tac
      G="G"
      in cfgLM.trans_der_der2)
        apply(rename_tac a d)(*strict*)
        apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
       apply(rename_tac a d)(*strict*)
       apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
       apply(clarsimp)
       apply(erule_tac
      x="e"
      in ballE)
        apply(rename_tac a d)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac a d)(*strict*)
       apply(clarsimp)
       apply(simp add: cfg_configurations_def)
      apply(rename_tac a d)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
     apply(rename_tac a d)(*strict*)
     apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
      apply(rename_tac a d)(*strict*)
      prefer 2
      apply(rule_tac
      ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>)"
      in cfgLM_trans_der_concat_extend_prime)
        apply(rename_tac a d)(*strict*)
        apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
        apply(force)
       apply(rename_tac a d)(*strict*)
       apply(force)
      apply(rename_tac a d)(*strict*)
      apply(force)
     apply(rename_tac a d)(*strict*)
     apply(clarsimp)
     apply(rename_tac a d da)(*strict*)
     apply(rule_tac
      d="da"
      in elim_map_from_trans_der)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac d)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2)
  apply(rename_tac SL' S2)(*strict*)
  apply(simp add: nth_opt_def)
  apply(simp add: Xstep_mergeL_def)
  apply(simp add: Xstep_elem_def)
  apply(simp add: Xstep_elem_def Xstep_mergeL_def Xstep_merge1_def nth_opt_def)
  apply(rename_tac SL' S2)(*strict*)
  apply(rule conjI)
   apply(rename_tac SL' S2)(*strict*)
   apply(clarsimp)
   apply(simp add: strict_prefix_def Xstep_merge1_toWasEliminated_def)
   apply(simp (no_asm) add: EValidSplit_def)
   apply(clarsimp)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(simp add: Xstep_merge1_toWasNotEliminated_def)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(rule EValidSplit_interline_shrink)
       apply(rename_tac SL' S2 c)(*strict*)
       apply(simp add: EValidSplit_def)
      apply(rename_tac SL' S2 c)(*strict*)
      apply(force)
     apply(rename_tac SL' S2 c S1' S1L)(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_interlineX_def Xstep_elem_def Xstep_merge1_def prefix_def Xstep_merge1_toWasEliminated_def)
    apply(rename_tac SL' S2 c S2' S2F)(*strict*)
    apply(simp add: EValidSplit_interlineX_def Xstep_elem_def Xstep_merge1_def prefix_def Xstep_merge1_toWasEliminated_def)
    apply(clarsimp)
    apply(rename_tac SL' c S2' S2F)(*strict*)
    apply(case_tac "ESplitItem_from SL'")
     apply(rename_tac SL' c S2' S2F)(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_producing_def)
     apply(erule_tac
      x="SL'"
      in ballE)
      apply(rename_tac SL' c S2' S2F)(*strict*)
      apply(force)
     apply(rename_tac SL' c S2' S2F)(*strict*)
     apply(subgoal_tac "SL' \<in> set (butlast (S1 @ SL # SL' # S2F # S2'))")
      apply(rename_tac SL' c S2' S2F)(*strict*)
      apply(force)
     apply(rename_tac SL' c S2' S2F)(*strict*)
     apply(rule_tac
      ?w1.0="S1@[SL]"
      in in_set_butlast)
      apply(rename_tac SL' c S2' S2F)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac SL' c S2' S2F)(*strict*)
     apply(force)
    apply(rename_tac SL' c S2' S2F a)(*strict*)
    apply(clarsimp)
    apply(case_tac c)
     apply(rename_tac SL' c S2' S2F a)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' c S2' S2F a aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' S2' S2F a aa list)(*strict*)
    apply(subgoal_tac "option_to_list (Some a)=[a]")
     apply(rename_tac SL' S2' S2F a aa list)(*strict*)
     prefer 2
     apply(simp add: option_to_list_def)
    apply(rename_tac SL' S2' S2F a aa list)(*strict*)
    apply(clarsimp)
    apply(thin_tac "option_to_list (Some a) = [a]")
    apply(subgoal_tac "a=aa")
     apply(rename_tac SL' S2' S2F a aa list)(*strict*)
     prefer 2
     apply (metis Cons_eq_appendI append_Nil append_eq_appendI hlp1_renamed)
    apply(rename_tac SL' S2' S2F a aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' S2' S2F aa list)(*strict*)
    apply(subgoal_tac "drop (Suc (length (ESplitItem_elim SL'))) (ESplitItem_to SL) = list")
     apply(rename_tac SL' S2' S2F aa list)(*strict*)
     prefer 2
     apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ aa # list"
      in ssubst)
      apply(rename_tac SL' S2' S2F aa list)(*strict*)
      apply(force)
     apply(rename_tac SL' S2' S2F aa list)(*strict*)
     apply(rule_tac
      t="drop (Suc (length (ESplitItem_elim SL'))) (ESplitItem_elim SL' @ aa # list)"
      and s="list"
      in ssubst)
      apply(rename_tac SL' S2' S2F aa list)(*strict*)
      apply (metis ConsApp append_assoc dropPrecise length_Suc)
     apply(rename_tac SL' S2' S2F aa list)(*strict*)
     apply(force)
    apply(rename_tac SL' S2' S2F aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' S2' S2F aa)(*strict*)
    apply(rule_tac
      w="ESplitItem_elim SL' @ [aa]"
      in append_linj)
    apply(rule_tac
      t="(ESplitItem_elim SL' @ [aa]) @ drop (Suc (length (ESplitItem_elim SL'))) (ESplitItem_to SL) @ ESplitItem_ignore SL"
      and s="ESplitItem_to SL @ ESplitItem_ignore SL"
      in ssubst)
     apply(rename_tac SL' S2' S2F aa)(*strict*)
     apply(force)
    apply(rename_tac SL' S2' S2F aa)(*strict*)
    apply(rule_tac
      t="ESplitItem_to SL @ ESplitItem_ignore SL"
      and s="ESplitItem_elim SL' @ aa # ESplitItem_ignore SL'"
      in ssubst)
     apply(rename_tac SL' S2' S2F aa)(*strict*)
     apply(force)
    apply(rename_tac SL' S2' S2F aa)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(simp add: EValidSplit_initial_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(clarsimp)
     apply(case_tac S1)
      apply(rename_tac SL' S2 c)(*strict*)
      apply(clarsimp)
     apply(rename_tac SL' S2 c a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(clarsimp)
    apply(case_tac S1)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(simp only: EValidSplit_to_empty_def)
    apply(clarify)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac SL' S2 c x)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' S2 c x)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' c x)(*strict*)
     apply(subgoal_tac "butlast (S1 @ [SL, SL']) = S1@[SL]")
      apply(rename_tac SL' c x)(*strict*)
      prefer 2
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac SL' c x)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(subgoal_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w' @ [a']) = SSv" for SSv)
     apply(rename_tac SL' c x w' a')(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w' @ [a']) = S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w'")
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = S1 @ SL # SL' # w'")
     apply(rename_tac SL' c x w' a')(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac SL' c x w' a')(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' c w' a')(*strict*)
    apply(case_tac "ESplitItem_from SL'")
     apply(rename_tac SL' c w' a')(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_producing_def)
    apply(rename_tac SL' c w' a' a)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(case_tac "ESplitItem_elem SL'")
     apply(rename_tac SL' c w' a' a)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' c w' a' a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' c w' a' a)(*strict*)
    apply(subgoal_tac "a \<in> setA (Esplit_signature (SL' # w'@[a']))")
     apply(rename_tac SL' c w' a' a)(*strict*)
     apply(force)
    apply(rename_tac SL' c w' a' a)(*strict*)
    apply(rule set_setA)
    apply(simp only: Esplit_signature_def)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(rule_tac
      t="foldl (@) [teA a] (map (option_to_list \<circ> ESplitItem_elem) w')"
      in ssubst)
     apply(rename_tac SL' c w' a' a)(*strict*)
     apply(rule foldl_first)
    apply(rename_tac SL' c w' a' a)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplit_interlineX SL SL'")
     apply(rename_tac SL' S2 c)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_interline_def)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(rule_tac
      t="SL'"
      and s="((S1 @ SL # SL' # S2) ! Suc (length S1))"
      in ssubst)
      apply(rename_tac SL' S2 c)(*strict*)
      apply (metis ConsApp Suc_length concat_asso nth_append_length)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_final_def)
    apply(clarsimp)
    apply(simp add: EValidSplit_interlineX_def)
    apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac SL' S2 c)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' c)(*strict*)
     apply(case_tac c)
      apply(rename_tac SL' c)(*strict*)
      apply(clarsimp)
     apply(rename_tac SL' c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' a list)(*strict*)
     apply(simp add: EValidSplit_produce_or_elim_def EValidSplit_producing_def)
     apply(clarsimp)
     apply(subgoal_tac "butlast (S1 @ [SL, SL']) = S1@[SL]")
      apply(rename_tac SL' a list)(*strict*)
      prefer 2
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac SL' a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' a list y)(*strict*)
     apply(simp add: option_to_list_def)
     apply(case_tac "ESplitItem_from SL'")
      apply(rename_tac SL' a list y)(*strict*)
      apply(clarsimp)
     apply(rename_tac SL' a list y aa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "a=aa")
      apply(rename_tac SL' a list y aa)(*strict*)
      prefer 2
      apply (metis Cons_eq_appendI append_Nil append_eq_appendI hlp1_renamed rotate_simps)
     apply(rename_tac SL' a list y aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' list y aa)(*strict*)
     apply(subgoal_tac "ESplitItem_elim SL' @ [aa] = ESplitItem_elim SL' @ aa # list @ ESplitItem_ignore SL")
      apply(rename_tac SL' list y aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac SL' y aa)(*strict*)
      apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ [aa]"
      in ssubst)
       apply(rename_tac SL' y aa)(*strict*)
       apply(force)
      apply(rename_tac SL' y aa)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac SL' list y aa)(*strict*)
     apply(rule_tac
      t="ESplitItem_elim SL' @ aa # list @ ESplitItem_ignore SL"
      and s="ESplitItem_to SL @ ESplitItem_ignore SL"
      in ssubst)
      apply(rename_tac SL' list y aa)(*strict*)
      apply(force)
     apply(rename_tac SL' list y aa)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(clarsimp)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(clarsimp)
    apply(simp add: EValidSplit_producing_def)
    apply(clarsimp)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(subgoal_tac "EValidSplit_interlineX SL SL'")
     apply(rename_tac SL' S2 c x)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_interline_def)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(rule_tac
      t="SL'"
      and s="((S1 @ SL # SL' # S2) ! Suc (length S1))"
      in ssubst)
      apply(rename_tac SL' S2 c x)(*strict*)
      apply (metis ConsApp Suc_length concat_asso nth_append_length)
     apply(rename_tac SL' S2 c x)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(simp add: EValidSplit_interlineX_def)
    apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac SL' S2 c x)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' S2 c x)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' c x)(*strict*)
     apply(subgoal_tac "x \<in> set(butlast (S1 @ [SL, SL']))")
      apply(rename_tac SL' c x)(*strict*)
      apply(force)
     apply(rename_tac SL' c x)(*strict*)
     apply (metis butLastSimp set_append_contra1)
    apply(rename_tac SL' S2 c x)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(subgoal_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w' @ [a']) = (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w')")
     apply(rename_tac SL' c x w' a')(*strict*)
     prefer 2
     apply (metis append_Cons butlast_snoc_2 length_append)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w' @ [a']) = S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL') @ ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL' @ drop (length (ESplitItem_elim SL') + length (option_to_list (ESplitItem_from SL'))) (ESplitItem_to SL)\<rparr> # w'")
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = S1 @ SL # SL' # w'")
     apply(rename_tac SL' c x w' a')(*strict*)
     prefer 2
     apply (metis append_Cons butlast_snoc_2)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' c x w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' c x w' a')(*strict*)
     apply(force)
    apply(rename_tac SL' c x w' a')(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_def)
    apply(simp add: EValidSplit_produce_or_elim_def)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(simp add: EValidSplit_ValidItem_def)
   apply(simp add: EValidSplitItem_def)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(rule_tac
      B="set(ESplitItem_to SL)"
      in subset_trans)
      apply(rename_tac SL' S2 c)(*strict*)
      apply(rule set_drop_subset)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(rule foldl_subset)
     apply(rename_tac SL' S2 c x)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' S2 c x xa)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
     apply(clarsimp)
     apply(force)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplit_interlineX SL SL'")
     apply(rename_tac SL' S2 c)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_interline_def)
     apply(clarsimp)
     apply(erule_tac
      x="length S1"
      in allE)
     apply(clarsimp)
     apply(rule_tac
      t="SL'"
      and s="((S1 @ SL # SL' # S2) ! Suc (length S1))"
      in ssubst)
      apply(rename_tac SL' S2 c)(*strict*)
      apply (metis ConsApp Suc_length concat_asso nth_append_length)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplit_interlineX_def)
    apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ c"
      in ssubst)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(case_tac c)
     apply(rename_tac SL' S2 c)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' S2 a list)(*strict*)
    apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac SL' S2 a list)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac SL' S2 a list)(*strict*)
    apply(erule disjE)
     apply(rename_tac SL' S2 a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' a list)(*strict*)
     apply(simp add: EValidSplit_def)
     apply(simp add: EValidSplit_final_def)
     apply(clarsimp)
     apply(case_tac "ESplitItem_from SL'")
      apply(rename_tac SL' a list)(*strict*)
      apply(clarsimp)
      apply(simp add: option_to_list_def)
     apply(rename_tac SL' a list aa)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "a=aa")
      apply(rename_tac SL' a list aa)(*strict*)
      prefer 2
      apply (metis Cons_eq_appendI append_Nil append_eq_appendI hlp1_renamed rotate_simps)
     apply(rename_tac SL' a list aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' list aa)(*strict*)
     apply(simp add: EValidSplit_to_empty_def)
     apply(subgoal_tac "ESplitItem_elim SL' @ [aa] = ESplitItem_elim SL' @ aa # list @ ESplitItem_ignore SL")
      apply(rename_tac SL' list aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac SL' aa)(*strict*)
      apply(subgoal_tac "butlast (S1 @ [SL, SL']) = S1@[SL]")
       apply(rename_tac SL' aa)(*strict*)
       prefer 2
       apply(rule butlast_direct)
       apply(force)
      apply(rename_tac SL' aa)(*strict*)
      apply(clarsimp)
      apply(erule_tac
      P="length (ESplitItem_to SL) \<le> Suc (length (ESplitItem_elim SL'))"
      in impE)
       apply(rename_tac SL' aa)(*strict*)
       apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ [aa]"
      in ssubst)
        apply(rename_tac SL' aa)(*strict*)
        apply(force)
       apply(rename_tac SL' aa)(*strict*)
       apply(simp (no_asm))
      apply(rename_tac SL' aa)(*strict*)
      apply(case_tac "ESplitItem_elem SL'")
       apply(rename_tac SL' aa)(*strict*)
       apply(clarsimp)
      apply(rename_tac SL' aa a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
       apply(rename_tac SL' aa a ab)(*strict*)
       prefer 2
       apply(rename_tac SL' aa a b)(*strict*)
       apply(clarsimp)
      apply(rename_tac SL' aa a ab)(*strict*)
      apply(clarsimp)
      apply(rename_tac SL' aa ab)(*strict*)
      apply(simp add: Esplit_signature_def)
      apply(simp add: option_to_list_def)
     apply(rename_tac SL' list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' a list w' a')(*strict*)
    apply(subgoal_tac "ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL' = ESplitItem_elim SL' @ a # list @ ESplitItem_ignore SL")
     apply(rename_tac SL' a list w' a')(*strict*)
     prefer 2
     apply(rule_tac
      t="ESplitItem_elim SL' @ a # list @ ESplitItem_ignore SL"
      and s="ESplitItem_to SL @ ESplitItem_ignore SL"
      in ssubst)
      apply(rename_tac SL' a list w' a')(*strict*)
      apply(force)
     apply(rename_tac SL' a list w' a')(*strict*)
     apply(force)
    apply(rename_tac SL' a list w' a')(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem SL'")
     apply(rename_tac SL' a list w' a')(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(simp add: EValidSplit_def)
     apply(clarsimp)
     apply(simp add: EValidSplit_producing_def)
     apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = SSv" for SSv)
      apply(rename_tac SL' a list w' a')(*strict*)
      prefer 2
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac SL' a list w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' a list w' a' aa)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_from SL'")
     apply(rename_tac SL' a list w' a' aa)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(simp add: EValidSplit_def)
     apply(clarsimp)
     apply(simp add: EValidSplit_producing_def)
     apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = SSv" for SSv)
      apply(rename_tac SL' a list w' a' aa)(*strict*)
      prefer 2
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac SL' a list w' a' aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' a list w' a' aa ab)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(clarsimp)
    apply(rename_tac SL' a list w' a' aa)(*strict*)
    apply(case_tac aa)
     apply(rename_tac SL' a list w' a' aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac SL' a list w' a' ab)(*strict*)
     apply(subgoal_tac "ab \<in> setA (Esplit_signature (SL' # w'@[a']))")
      apply(rename_tac SL' a list w' a' ab)(*strict*)
      apply(force)
     apply(rename_tac SL' a list w' a' ab)(*strict*)
     apply(rule set_setA)
     apply(simp only: Esplit_signature_def)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(rule_tac
      t="foldl (@) [teA ab] (map (option_to_list \<circ> ESplitItem_elem) w')"
      in ssubst)
      apply(rename_tac SL' a list w' a' ab)(*strict*)
      apply(rule foldl_first)
     apply(rename_tac SL' a list w' a' ab)(*strict*)
     apply(force)
    apply(rename_tac SL' a list w' a' aa b)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' a list w' a' b)(*strict*)
    apply(subgoal_tac "(ESplitItem_to SL' = [] \<longrightarrow> list = [] \<longrightarrow> ESplitItem_ignore SL \<noteq> [])")
     apply(rename_tac SL' a list w' a' b)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ a # list"
      in ssubst)
      apply(rename_tac SL' a list w' a' b)(*strict*)
      apply(force)
     apply(rename_tac SL' a list w' a' b)(*strict*)
     apply(rule_tac
      t="drop (Suc (length (ESplitItem_elim SL'))) (ESplitItem_elim SL' @ a # list)"
      and s="list"
      in ssubst)
      apply(rename_tac SL' a list w' a' b)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac SL' a list w' a' b)(*strict*)
     apply(force)
    apply(rename_tac SL' a list w' a' b)(*strict*)
    apply(clarsimp)
    apply(rename_tac SL' a w' a' b)(*strict*)
    apply(subgoal_tac "length (ESplitItem_to SL) = Suc (length (ESplitItem_elim SL'))")
     apply(rename_tac SL' a w' a' b)(*strict*)
     apply(force)
    apply(rename_tac SL' a w' a' b)(*strict*)
    apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ [a]"
      in ssubst)
     apply(rename_tac SL' a w' a' b)(*strict*)
     apply(force)
    apply(rename_tac SL' a w' a' b)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac SL' S2 c)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(simp add: EValidSplitItem_elim_def)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac SL' S2 c d da)(*strict*)
   apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from x))\<rparr> (ESplitItem_prods x) \<lparr>cfg_conf = option_to_list (ESplitItem_elem x) @ liftA (ESplitItem_to x)\<rparr> \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem x) \<longrightarrow> (\<forall>i<length (ESplitItem_prods x). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the (ESplitItem_elem x))) \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem x) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods x = []))")
   apply(rename_tac SL' S2 c d da)(*strict*)
   apply(thin_tac "EValidSplitItem_elim G SL")
   apply(simp add: EValidSplitItem_elim_def)
   apply(clarsimp)
   apply(case_tac "ESplitItem_from SL")
    apply(rename_tac SL' S2 c d da)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac SL' S2 c d da)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac SL' S2 c d da)(*strict*)
    apply(clarsimp)
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
    apply(rename_tac SL' S2 c d da a)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in cfgLM.trans_der_der2)
      apply(rename_tac SL' S2 c d da a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
     apply(rename_tac SL' S2 c d da a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="e"
      in ballE)
      apply(rename_tac SL' S2 c d da a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac SL' S2 c d da a)(*strict*)
     apply(clarsimp)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac SL' S2 c d da a)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac SL' S2 c d da a)(*strict*)
    prefer 2
    apply(rule_tac
      ?v2.0="[teA (prod_lhs e)]"
      and ?v1.0="[]"
      and ?v4.0="liftA (ESplitItem_to SL)"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>)"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac SL' S2 c d da a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(force)
     apply(rename_tac SL' S2 c d da a)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c d da a)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(thin_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>) \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> [e] \<lparr>cfg_conf = liftB []\<rparr>")
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods SL) \<lparr>cfg_conf = teA (prod_lhs e) # liftA (ESplitItem_to SL)\<rparr>")
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA(ESplitItem_elim SL')\<rparr> (foldl (@) [] (ESplitItem_elim_prods SL')) \<lparr>cfg_conf=[]\<rparr>")
    apply(rename_tac SL' S2 c d da a)(*strict*)
    prefer 2
    apply(rule_tac
      xs="(ESplitItem_elim_prods SL')"
      in elim_map_to_trans_der)
       apply(rename_tac SL' S2 c d da a)(*strict*)
       apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(rename_tac SL' S2 c d da a)(*strict*)
      apply(force)
     apply(rename_tac SL' S2 c d da a)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c d da a)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(thin_tac "elim_map G (ESplitItem_elim SL') (ESplitItem_elim_prods SL') (map (\<lambda>x. []) (ESplitItem_elim_prods SL'))")
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(clarsimp)
   apply(rename_tac SL' S2 c d da a db dc)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac SL' S2 c d da a db dc)(*strict*)
    prefer 2
    apply(rule_tac
      ?v2.0="liftA (ESplitItem_elim SL')"
      and ?v1.0="[]"
      and ?v4.0="liftA c"
      and ?d1.0="db"
      and ?d2.0="dc"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac SL' S2 c d da a db dc)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(force)
     apply(rename_tac SL' S2 c d da a db dc)(*strict*)
     apply(rule_tac
      t="liftB [] @ liftA (ESplitItem_elim SL') @ liftA c"
      and s="liftA (ESplitItem_to SL)"
      in ssubst)
      apply(rename_tac SL' S2 c d da a db dc)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ c"
      in ssubst)
       apply(rename_tac SL' S2 c d da a db dc)(*strict*)
       apply(force)
      apply(rename_tac SL' S2 c d da a db dc)(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac SL' S2 c d da a db dc)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c d da a db dc)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c d da a db dc)(*strict*)
   apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods SL @ [e]) \<lparr>cfg_conf = liftA (ESplitItem_to SL)\<rparr>")
   apply(rename_tac SL' S2 c d da a db dc)(*strict*)
   apply(thin_tac "cfgLM.trans_der G dc \<lparr>cfg_conf = liftA (ESplitItem_elim SL')\<rparr> (foldl (@) [] (ESplitItem_elim_prods SL')) \<lparr>cfg_conf = []\<rparr>")
   apply(rename_tac SL' S2 c d da a db dc)(*strict*)
   apply(clarsimp)
   apply(rename_tac SL' S2 c d da a db)(*strict*)
   apply(case_tac "ESplitItem_from SL'")
    apply(rename_tac SL' S2 c d da a db)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac SL' S2 c d da a db)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac SL' S2 c d da a db)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="db"
      in exI)
    apply(rule_tac
      t="ESplitItem_to SL"
      and s="ESplitItem_elim SL' @ c"
      in ssubst)
     apply(rename_tac SL' S2 c d da a db)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c d da a db)(*strict*)
    apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(case_tac "ESplitItem_to SL'")
     apply(rename_tac SL' S2 c d da a db)(*strict*)
     prefer 2
     apply(rename_tac SL' S2 c d da a db aa list)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c d da a db)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem SL'")
     apply(rename_tac SL' S2 c d da a db)(*strict*)
     apply(clarsimp)
    apply(rename_tac SL' S2 c d da a db aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac SL' S2 c d da a db aa)(*strict*)
   apply(clarsimp)
   apply(case_tac c)
    apply(rename_tac SL' S2 c d da a db aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac SL' S2 c d da a db aa ab list)(*strict*)
   apply(clarsimp)
   apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
   apply(subgoal_tac "EValidSplit_interlineX SL SL'")
    apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="length S1"
      in allE)
  apply(clarsimp)
  apply(rule_tac
    t="SL'"
    and s="((S1 @ SL # SL' # S2) ! Suc (length S1))"
    in ssubst)
   apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
   apply (metis ConsApp Suc_length concat_asso nth_append_length)
  apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "ESplitItem_elim SL' @ option_to_list (Some aa) @ ESplitItem_ignore SL' = ESplitItem_elim SL' @ ab # list @ ESplitItem_ignore SL")
  apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
  prefer 2
  apply(rule_tac
    t="ESplitItem_elim SL' @ ab # list @ ESplitItem_ignore SL"
    and s="ESplitItem_to SL @ ESplitItem_ignore SL"
    in ssubst)
   apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db aa ab list)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  prefer 2
  apply(rule_tac
    ?v2.0="[teA ab]"
    and ?v1.0="[]"
    and ?v4.0="liftA list"
    and ?d1.0="db"
    and ?d2.0="da"
    in cfgLM_trans_der_concat_extend)
    apply(rename_tac SL' S2 d da a db ab list)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(force)
   apply(rename_tac SL' S2 d da a db ab list)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="derivation_append db (derivation_map da (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA list\<rparr>)) (Suc (length (ESplitItem_prods SL) + length (foldl (@) [] (ESplitItem_elim_prods SL'))))"
    in exI)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(rule_tac
    t="ESplitItem_to SL"
    and s="ESplitItem_elim SL' @ ab # list"
    in ssubst)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(simp (no_asm) add: liftA_commutes_over_concat)
  apply(case_tac "ESplitItem_elem SL'")
  apply(rename_tac SL' S2 d da a db ab list)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac SL' S2 d da a db ab list aa ac)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list ac)(*strict*)
  apply(subgoal_tac "ac \<in> setA (Esplit_signature (SL' # S2))")
   apply(rename_tac SL' S2 d da a db ab list ac)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 d da a db ab list ac)(*strict*)
  apply(rule set_setA)
  apply(simp only: Esplit_signature_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    t="foldl (@) [teA ac] (map (option_to_list \<circ> ESplitItem_elem) S2)"
    in ssubst)
   apply(rename_tac SL' S2 d da a db ab list ac)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac SL' S2 d da a db ab list ac)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db ab list aa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(subgoal_tac "\<forall>i\<le>(length (ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL'))). hd (cfg_conf (the (get_configuration (db i)))) \<noteq> teB b")
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  prefer 2
  apply(rule cfgLM_trans_der_no_terminal_reached)
   apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
   apply(force)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(case_tac "i<Suc(length (ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL')))")
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(erule_tac
    x="i"
    in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="i-(length (ESplitItem_prods SL @ e # foldl (@) [] (ESplitItem_elim_prods SL')))"
    and P="\<lambda>i. i < length (ESplitItem_prods SL') \<longrightarrow> hd (cfg_conf (the (get_configuration (da i)))) \<noteq> teB b"
    in allE)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(erule impE)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
  apply(case_tac "da (i - Suc (length (ESplitItem_prods SL) + length (foldl (@) [] (ESplitItem_elim_prods SL'))))")
  apply(rename_tac SL' S2 d da a db ab list b i)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac SL' S2 d da a db ab list b i aa option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i option ba)(*strict*)
  apply(case_tac ba)
  apply(rename_tac SL' S2 d da a db ab list b i option ba cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i option cfg_confa)(*strict*)
  apply(case_tac cfg_confa)
  apply(rename_tac SL' S2 d da a db ab list b i option cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i option)(*strict*)
  apply(case_tac list)
   apply(rename_tac SL' S2 d da a db ab list b i option)(*strict*)
   apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i option aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 d da a db ab list b i option cfg_confa aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "EValidSplit_interlineX SL SL'")
  apply(rename_tac SL' S2)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_interline_def)
  apply(clarsimp)
  apply(erule_tac
    x="length S1"
    in allE)
  apply(clarsimp)
  apply(rule_tac
    t="SL'"
    and s="((S1 @ SL # SL' # S2) ! Suc (length S1))"
    in ssubst)
  apply(rename_tac SL' S2)(*strict*)
  apply (metis ConsApp Suc_length concat_asso nth_append_length)
  apply(rename_tac SL' S2)(*strict*)
  apply(force)
  apply(rename_tac SL' S2)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "strict_prefix (ESplitItem_elim SL') (ESplitItem_to SL) \<or> prefix(ESplitItem_to SL) (ESplitItem_elim SL')")
  apply(rename_tac SL' S2)(*strict*)
  prefer 2
  apply(rule mutual_strict_prefix_prefix)
  apply(force)
  apply(rename_tac SL' S2)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' S2)(*strict*)
  apply(force)
  apply(rename_tac SL' S2)(*strict*)
  apply(simp add: prefix_def)
  apply(thin_tac "\<not> strict_prefix (ESplitItem_elim SL') (ESplitItem_to SL)")
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: Xstep_merge1_toWasEliminated_def)
  apply(simp add: EValidSplit_def)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule EValidSplit_interline_shrink)
    apply(rename_tac SL' S2 c)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(clarsimp)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(rule_tac
    t="drop (length (ESplitItem_to SL)) (ESplitItem_to SL @ c)"
    and s="c"
    in ssubst)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(rule_tac
    t="ESplitItem_to S1L @ ESplitItem_ignore S1L"
    and s="ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ ESplitItem_ignore SL"
    in ssubst)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
    w="ESplitItem_to SL"
    in append_linj)
  apply(rule_tac
    t="ESplitItem_to SL @ ESplitItem_ignore SL"
    and s="ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    in ssubst)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(rule_tac
    t="ESplitItem_to SL @ c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    and s="ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    in ssubst)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
    apply(rename_tac SL' S2 c S1' S1L)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c S1' S1L)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac SL' S2 c S1' S1L)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c S2' S2F)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(subgoal_tac "c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL' = ESplitItem_ignore SL")
  apply(rename_tac SL' S2 c)(*strict*)
  prefer 2
  apply(rule_tac
    w="ESplitItem_to SL"
    in append_linj)
  apply(rule_tac
    t="ESplitItem_to SL @ ESplitItem_ignore SL"
    and s="ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_initial_def)
  apply(clarsimp)
  apply(erule disjE)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(case_tac S1)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac SL' S2)(*strict*)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
  apply(rename_tac SL' S2 c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(case_tac S1)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_from SL'")
   apply(rename_tac SL' S2)(*strict*)
   apply(clarsimp)
  apply(rename_tac SL' S2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_to_empty_def)
  apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
  apply(rename_tac SL' S2 c)(*strict*)
  prefer 2
  apply(rule case_list)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' c x)(*strict*)
  apply(subgoal_tac "butlast (S1 @ [SL, SL']) = S1@[SL]")
   apply(rename_tac SL' c x)(*strict*)
   prefer 2
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac SL' c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(subgoal_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim SL'), ESplitItem_from = ESplitItem_from SL', ESplitItem_ignore = ESplitItem_ignore SL', ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ e # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'), ESplitItem_prods = ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL'\<rparr> # w' @ [a']) = SSv" for SSv)
  apply(rename_tac SL' c x w' a')(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = SSv" for SSv)
  apply(rename_tac SL' c x w' a')(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(clarsimp)
  apply(erule disjE)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_final_def)
  apply(clarsimp)
  apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
  apply(rename_tac SL' S2 c)(*strict*)
  prefer 2
  apply(rule case_list)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_producing_def)
  apply(clarsimp)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
  apply(rename_tac SL' S2 c x)(*strict*)
  prefer 2
  apply(rule case_list)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' c x)(*strict*)
  apply(erule_tac
    x="x"
    in ballE)
   apply(rename_tac SL' c x)(*strict*)
   apply(force)
  apply(rename_tac SL' c x)(*strict*)
  apply(subgoal_tac "x \<in> set (butlast (S1 @ [SL, SL']))")
   apply(rename_tac SL' c x)(*strict*)
   apply(force)
  apply(rename_tac SL' c x)(*strict*)
  apply (metis butLastSimp set_append_contra1)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(subgoal_tac "butlast (S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim SL'), ESplitItem_from = ESplitItem_from SL', ESplitItem_ignore = ESplitItem_ignore SL', ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ e # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'), ESplitItem_prods = ESplitItem_prods SL', ESplitItem_elem = ESplitItem_elem SL', ESplitItem_to = ESplitItem_to SL'\<rparr> # w' @ [a']) = SSw" for SSw)
  apply(rename_tac SL' c x w' a')(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast (S1 @ SL # SL' # w' @ [a']) = SSv" for SSv)
  apply(rename_tac SL' c x w' a')(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac SL' c x w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' c x w' a' y ya yb)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' c x w' a' y ya yb)(*strict*)
  apply(force)
  apply(rename_tac SL' c x w' a' y ya yb)(*strict*)
  apply(erule disjE)
  apply(rename_tac SL' c x w' a' y ya yb)(*strict*)
  apply(force)
  apply(rename_tac SL' c x w' a' y ya yb)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_produce_or_elim_def)
  apply(clarsimp)
  apply(rename_tac SL' S2 c y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplitItem_belongs_def)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule_tac
    B="set(ESplitItem_elim SL')"
    in subset_trans)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(rule set_drop_subset)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule foldl_subset)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(subgoal_tac "x \<in> set (ESplitItem_elim_prods SL')")
   apply(rename_tac SL' S2 c x)(*strict*)
   apply(clarsimp)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(rule_tac
    A="set (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))"
    in set_mp)
   apply(rename_tac SL' S2 c x)(*strict*)
   apply(rule List.set_take_subset)
  apply(rename_tac SL' S2 c x)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac SL' S2 c x xa)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c x xa)(*strict*)
  apply(subgoal_tac "x \<in> set ((ESplitItem_elim_prods SL'))")
   apply(rename_tac SL' S2 c x xa)(*strict*)
   prefer 2
   apply(rule_tac
    A="set(drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))"
    in set_mp)
    apply(rename_tac SL' S2 c x xa)(*strict*)
    apply(rule List.set_drop_subset)
   apply(rename_tac SL' S2 c x xa)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c x xa)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule_tac
    t="drop (length (ESplitItem_to SL)) (ESplitItem_to SL @ c)"
    and s="c"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule_tac
    t="c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    and s="ESplitItem_ignore SL"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule conjI)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(simp add: EValidSplitItem_elim_def)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from SL")
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(simp add: EValidSplit_producing_def)
  apply(erule_tac
    x="SL"
    and P="\<lambda>SL. (\<exists>y. ESplitItem_from SL = Some y) \<and> (\<exists>y. ESplitItem_elem SL = Some y)"
    in ballE)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(subgoal_tac "SL \<in> set (butlast (S1 @ SL # SL' # S2))")
   apply(rename_tac SL' S2 c)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(rule in_set_butlast)
   apply(rename_tac SL' S2 c)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="option_to_list (Some a)"
    and s="[a]"
    in ssubst)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(rule_tac
    t="drop (length (ESplitItem_to SL)) (ESplitItem_to SL @ c)"
    and s="c"
    in ssubst)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(rule_tac
    t="c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    and s="ESplitItem_ignore SL"
    in ssubst)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(rule_tac
    ?v1.0="ESplitItem_elim SL"
    in elim_map_compose)
         apply(rename_tac SL' S2 c a)(*strict*)
         apply(force)
        apply(rename_tac SL' S2 c a)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac SL' S2 c a)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac SL' S2 c a)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac SL' S2 c a)(*strict*)
     prefer 4
     apply(force)
    apply(rename_tac SL' S2 c a)(*strict*)
    prefer 4
    apply(force)
   apply(rename_tac SL' S2 c a)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
    apply(rename_tac SL' S2 c a)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c a)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac SL' S2 c a)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
   apply(rename_tac SL' S2 c a)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(rule_tac
    ?v1.0="[a]"
    and ?fw1.0="[[]]"
    and ?f\<pi>1.0="[(ESplitItem_prods SL @ e # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL')))]"
    in elim_map_compose)
         apply(rename_tac SL' S2 c a)(*strict*)
         prefer 7
         apply(force)
        apply(rename_tac SL' S2 c a)(*strict*)
        prefer 7
        apply(force)
       apply(rename_tac SL' S2 c a)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac SL' S2 c a)(*strict*)
      prefer 4
      apply(clarsimp)
      apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
       apply(rename_tac SL' S2 c a)(*strict*)
       apply(force)
      apply(rename_tac SL' S2 c a)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac SL' S2 c a)(*strict*)
     prefer 5
     apply(force)
    apply(rename_tac SL' S2 c a)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac SL' S2 c a)(*strict*)
   prefer 3
   apply(clarsimp)
   apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
    apply(rename_tac SL' S2 c a)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c a)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac SL' S2 c a)(*strict*)
  prefer 2
  apply(rule_tac
    ?fw1.0="map (\<lambda>x. []) (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))"
    and ?f\<pi>1.0="take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL')"
    and v="ESplitItem_elim SL'"
    in elim_map_decompose2)
         apply(rename_tac SL' S2 c a)(*strict*)
         apply(force)
        apply(rename_tac SL' S2 c a)(*strict*)
        prefer 3
        apply(clarsimp)
        apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
         apply(rename_tac SL' S2 c a)(*strict*)
         apply(force)
        apply(rename_tac SL' S2 c a)(*strict*)
        apply(simp (no_asm))
       apply(rename_tac SL' S2 c a)(*strict*)
       prefer 3
       apply(clarsimp)
       apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
        apply(rename_tac SL' S2 c a)(*strict*)
        apply(force)
       apply(rename_tac SL' S2 c a)(*strict*)
       apply(simp (no_asm))
      apply(rename_tac SL' S2 c a)(*strict*)
      prefer 3
      apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
       apply(rename_tac SL' S2 c a)(*strict*)
       apply(force)
      apply(rename_tac SL' S2 c a)(*strict*)
      apply(force)
     apply(rename_tac SL' S2 c a)(*strict*)
     prefer 3
     apply (metis append_take_drop_id_hlp)
    apply(rename_tac SL' S2 c a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
     apply(rename_tac SL' S2 c a)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c a)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac SL' S2 c a)(*strict*)
   prefer 2
   apply(rule map_append)
   apply (metis append_take_drop_id_hlp)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
   apply(rename_tac SL' S2 c a)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(thin_tac "EValidSplitItem_gen G SL'")
  apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2. EValidSplitItem_belongs G x \<and> length (ESplitItem_elim_prods x) = length (ESplitItem_elim x) \<and> elim_map G (ESplitItem_elim x) (ESplitItem_elim_prods x) (map (\<lambda>x. []) (ESplitItem_elim_prods x)) \<and> EValidSplitItem_gen G x")
  apply(rename_tac SL' S2 c a)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(subgoal_tac "ESplitItem_to SL @ c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL' = ESplitItem_to SL @ ESplitItem_ignore SL")
  apply(rename_tac SL' S2 c a d)(*strict*)
  prefer 2
  apply(rule_tac
    t="ESplitItem_to SL @ c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    and s="ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    in ssubst)
   apply(rename_tac SL' S2 c a d)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
  apply(rename_tac SL' S2 c a d)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    in cfgLM.trans_der_der2)
    apply(rename_tac SL' S2 c a d)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
   apply(rename_tac SL' S2 c a d)(*strict*)
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
    x="e"
    in ballE)
    apply(rename_tac SL' S2 c a d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac SL' S2 c a d)(*strict*)
   apply(clarsimp)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
  apply(rename_tac SL' S2 c a d)(*strict*)
  prefer 2
  apply(rule_tac
    ?v1.0="[]"
    and ?v4.0="liftA (ESplitItem_to SL)"
    and ?d1.0="d"
    and ?d2.0="(der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>)"
    in cfgLM_trans_der_concat_extend_prime)
    apply(rename_tac SL' S2 c a d)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(force)
   apply(rename_tac SL' S2 c a d)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods SL) \<lparr>cfg_conf = teA (prod_lhs e) # liftA (ESplitItem_to SL)\<rparr>")
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = liftB []\<rparr>) \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> [e] \<lparr>cfg_conf = liftB []\<rparr>")
  apply(rename_tac SL' S2 c a d)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA(take (length(ESplitItem_to SL)) (ESplitItem_elim SL'))\<rparr> (foldl (@) [] (take (length(ESplitItem_to SL))(ESplitItem_elim_prods SL'))) \<lparr>cfg_conf=[]\<rparr>")
  apply(rename_tac SL' S2 c a d da)(*strict*)
  prefer 2
  apply(rule_tac
    xs="take (length(ESplitItem_to SL))(ESplitItem_elim_prods SL')"
    in elim_map_to_trans_der)
     apply(rename_tac SL' S2 c a d da)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(rename_tac SL' S2 c a d da)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c a d da)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(rule elim_map_restrict)
     apply(rename_tac SL' S2 c a d da)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c a d da)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
     apply(rename_tac SL' S2 c a d da)(*strict*)
     apply(force)
    apply(rename_tac SL' S2 c a d da)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac SL' S2 c a d da)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
   apply(rename_tac SL' S2 c a d da)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(thin_tac "elim_map G (ESplitItem_elim SL') (ESplitItem_elim_prods SL') (map (\<lambda>x. []) (ESplitItem_elim_prods SL'))")
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  prefer 2
  apply(rule_tac
    ?v1.0="[]"
    and ?v4.0="[]"
    and ?d1.0="da"
    and ?d2.0="db"
    in cfgLM_trans_der_concat_extend_prime)
    apply(rename_tac SL' S2 c a d da db)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(force)
   apply(rename_tac SL' S2 c a d da db)(*strict*)
   apply(force)
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(rule_tac
    t="ESplitItem_to SL"
    and s="take (length (ESplitItem_to SL)) (ESplitItem_elim SL')"
    in ssubst)
   apply(rename_tac SL' S2 c a d da db)(*strict*)
   apply(rule_tac
    t="ESplitItem_elim SL'"
    and s="ESplitItem_to SL @ c"
    in ssubst)
    apply(rename_tac SL' S2 c a d da db)(*strict*)
    apply(force)
   apply(rename_tac SL' S2 c a d da db)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA (take (length (ESplitItem_to SL)) (ESplitItem_elim SL'))\<rparr> (foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods SL'))) \<lparr>cfg_conf = []\<rparr>")
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods SL @ [e]) \<lparr>cfg_conf = liftA (ESplitItem_to SL)\<rparr>")
  apply(rename_tac SL' S2 c a d da db)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c a d da)(*strict*)
  apply(rule elim_map_from_trans_der)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
  apply(rename_tac SL' S2 c)(*strict*)
  apply(subgoal_tac "ESplitItem_to SL @ c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL' = ESplitItem_to SL @ ESplitItem_ignore SL")
  apply(rename_tac SL' S2 c)(*strict*)
  prefer 2
  apply(rule_tac
    t="ESplitItem_to SL @ c @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    and s="ESplitItem_elim SL' @ option_to_list (ESplitItem_from SL') @ ESplitItem_ignore SL'"
    in ssubst)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac SL' S2 c d da)(*strict*)
  apply(case_tac "ESplitItem_from SL")
  apply(rename_tac SL' S2 c d da)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
  apply(rename_tac SL' S2 c d da)(*strict*)
  prefer 2
  apply(rule_tac cfgLM_trans_der_from_empty)
  apply(force)
  apply(rename_tac SL' S2 c d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_from SL'")
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  prefer 2
  apply(rule_tac cfgLM_trans_der_from_empty)
  apply(force)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_to SL'")
  apply(rename_tac SL' S2 c d da a)(*strict*)
  prefer 2
  apply(rename_tac SL' S2 c d da a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  prefer 2
  apply(case_tac "ESplitItem_elem SL'")
   apply(rename_tac SL' S2 c d da a)(*strict*)
   apply(clarsimp)
  apply(rename_tac SL' S2 c d da a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(rule_tac
    x="der1 \<lparr>cfg_conf = []\<rparr>"
    in exI)
  apply(rule cfgLM_trans_der_der1)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
  apply(rename_tac SL' S2 c d da a)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(rename_tac SL' S2 c d da a aa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="da"
    in exI)
  apply(clarsimp)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(subgoal_tac "A \<in> setA (Esplit_signature (SL' # S2))")
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(rule set_setA)
  apply(simp only: Esplit_signature_def)
  apply(clarsimp)
  apply(rule_tac
    t="ESplitItem_elem SL'"
    and s="Some (teA A)"
    in ssubst)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(force)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(rule_tac
    t="option_to_list (Some (teA A))"
    and s="[teA A]"
    in ssubst)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(rule_tac
    t="foldl (@) [teA A] (map (option_to_list \<circ> ESplitItem_elem) S2)"
    in ssubst)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac SL' S2 c d da a aa A)(*strict*)
  apply(force)
  done

lemma EValidSplit_interline_enlarge: "
  S=(S1@[B,C]@S2)
  \<Longrightarrow> EValidSplit_interline (S1@[A]@S2)
  \<Longrightarrow> (\<And>S1' S1L. S1=S1'@[S1L] \<Longrightarrow> EValidSplit_interlineX S1L A \<Longrightarrow> EValidSplit_interlineX S1L B)
  \<Longrightarrow> (\<And>S2' S2F. S2=S2F#S2' \<Longrightarrow> EValidSplit_interlineX A S2F \<Longrightarrow> EValidSplit_interlineX B C \<Longrightarrow> EValidSplit_interlineX C S2F)
  \<Longrightarrow> EValidSplit_interlineX B C
  \<Longrightarrow> EValidSplit_interline S"
  apply(simp (no_asm) add: EValidSplit_interline_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "Suc i<length S1")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply (metis List.nth_append Suc_lessD)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1\<le>Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length S1=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(thin_tac "\<And>S2' S2F. S2 = S2F # S2' \<Longrightarrow> EValidSplit_interlineX A S2F \<Longrightarrow> EValidSplit_interlineX C S2F")
   apply(rename_tac w' a')(*strict*)
   apply(erule_tac
      x="w'"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="a'"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac w' a')(*strict*)
    apply(simp add: EValidSplit_interline_def)
    apply(erule_tac
      x="length w'"
      in allE)
    apply(clarsimp)
    apply (metis ConsApp Suc_length append_assoc nth_append_length)
   apply(rename_tac w' a')(*strict*)
   apply (metis ConsApp Suc_length append_assoc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length S1<Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc(length S1)=Suc i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(thin_tac "EValidSplit_interline (S1 @ A # S2)")
   apply (metis ConsApp Suc_length append_assoc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "Suc(length S1)<Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc (length S1) = i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ B # C # S2) ! Suc (length S1)"
      and s="C"
      in ssubst)
    apply (metis ConsApp append_assoc length_Suc nth_append_length)
   apply(case_tac S2)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ B # C # a # list) ! Suc (Suc (length S1))"
      and s="a"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply (metis ConsApp append_assoc length_Suc nth_append_length)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="list"
      and P="\<lambda>X. (\<And>S2F. a = S2F \<and> list = X \<Longrightarrow> EValidSplit_interlineX A S2F \<Longrightarrow> EValidSplit_interlineX C S2F)"
      in meta_allE)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="a"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="length S1"
      in allE)
   apply(clarsimp)
   apply (metis ConsApp append_assoc length_Suc nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(simp add: EValidSplit_interline_def)
  apply(subgoal_tac "Suc (length S1) < i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac i)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(S1 @ B # C # S2) ! Suc i"
      and s="(S1 @ A # S2) ! i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(S1 @ B # C # S2) ! Suc i"
      and s=" S2 ! (Suc i-length(S1 @ B # C#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ B # C # S2"
      and s="(S1 @ B # C #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ A # S2) ! i"
      and s=" S2 ! (i-length(S1 @ A#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ A # S2"
      and s="(S1 @ A #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(S1 @ B # C # S2) ! Suc (Suc i)"
      and s="(S1 @ A # S2) ! (Suc i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(S1 @ B # C # S2) ! Suc (Suc i)"
      and s=" S2 ! (Suc (Suc i)-length(S1 @ B # C#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ B # C # S2"
      and s="(S1 @ B # C #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(S1 @ A # S2) ! (Suc i)"
      and s=" S2 ! ((Suc i)-length(S1 @ A#[]))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="S1 @ A # S2"
      and s="(S1 @ A #[])@ S2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma Esplit_inst_AX_step_relation_preserves_belongs2: "
Esplit_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2)
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setA (Esplit_signature S2) = {}
  \<Longrightarrow> ESplitItem_elem SL = Some (teA A)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> # Xstep_gen [B] (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2)"
  apply(subgoal_tac "nat_seq 0 0 = [0]")
   prefer 2
   apply (metis natUptTo_n_n)
  apply(simp add: Xstep_mergeL_def Xstep_elem_def Xstep_gen_def Xstep_merge1_def)
  apply(simp add: EValidSplit_def)
  apply(case_tac S2)
   apply(clarsimp)
   apply(simp add: nth_opt_def)
   apply(rule conjI)
    apply(rule EValidSplit_interline_enlarge)
        apply(force)
       apply(force)
      apply(rename_tac S1' S1L)(*strict*)
      apply(simp add: EValidSplit_interlineX_def)
     apply(rename_tac S2' S2F)(*strict*)
     apply(simp add: EValidSplit_interlineX_def)
    apply(simp add: EValidSplit_interlineX_def)
    apply(simp add: option_to_list_def)
   apply(simp add: EValidSplit_final_def)
   apply(rule conjI)
    apply(simp add: EValidSplit_initial_def)
    apply(clarsimp)
    apply(erule disjE)
     apply(clarsimp)
     apply(case_tac S1)
      apply(clarsimp)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac S1)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: EValidSplit_to_empty_def)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := [B]\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = [], ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>]) = SSv" for SSv)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: EValidSplit_producing_def)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := [B]\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = [], ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>])=SSw" for SSw)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := [B]\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = [], ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>]) = S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := [B]\<rparr>]")
    apply(rename_tac x)(*strict*)
    apply(erule disjE)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_produce_or_elim_def)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplitItem G SL")
     prefer 2
     apply(simp add: EValidSplit_ValidItem_def)
    apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(case_tac "ESplitItem_from SL")
     apply(rename_tac d)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
      apply(rename_tac d)(*strict*)
      prefer 2
      apply(rule_tac cfgLM_trans_der_from_empty)
      apply(simp add: option_to_list_def)
     apply(rename_tac d)(*strict*)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: EValidSplit_produce_or_elim_def)
   apply(simp add: EValidSplit_ValidItem_def)
   apply(rule conjI)
    apply(simp add: EValidSplitItem_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(simp add: EValidSplitItem_belongs_def)
     apply(clarsimp)
     apply(rule conjI)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
       apply(clarsimp)
      apply(clarsimp)
     apply(rule conjI)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def option_to_list_def)
     apply(rule conjI)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def option_to_list_def)
      apply(clarsimp)
      apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
       apply(clarsimp)
      apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(simp add: proper_l3_l2_seq_def)
     apply(clarsimp)
     apply(rename_tac w' q qa A Aa)(*strict*)
     apply(subgoal_tac "LR1ProdForm G")
      apply(rename_tac w' q qa A Aa)(*strict*)
      apply(simp add: LR1ProdForm_def)
      apply(erule_tac
      x=" \<lparr>prod_lhs = cons_l2 q A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
       apply(rename_tac w' q qa A Aa)(*strict*)
       apply(clarsimp)
       apply(rename_tac w' q qa A Aa q2)(*strict*)
       apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
        apply(rename_tac w' q qa A Aa q2)(*strict*)
        prefer 2
        apply(rule case_list)
       apply(rename_tac w' q qa A Aa q2)(*strict*)
       apply(erule_tac
      P="last_back_state w' = None"
      in disjE)
        apply(rename_tac w' q qa A Aa q2)(*strict*)
        apply(subgoal_tac "\<exists>w' x. [] = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
         apply(rename_tac w' q qa A Aa q2)(*strict*)
         prefer 2
         apply(rule last_back_state_not_empty)
         apply(force)
        apply(rename_tac w' q qa A Aa q2)(*strict*)
        apply(clarsimp)
       apply(rename_tac w' q qa A Aa q2)(*strict*)
       apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some qa" for SSw)
        apply(rename_tac w' q qa A Aa q2)(*strict*)
        prefer 2
        apply(rule last_back_state_not_empty)
        apply(force)
       apply(rename_tac w' q qa A Aa q2)(*strict*)
       apply(clarsimp)
       apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
       apply(subgoal_tac "\<exists>w' x. [] = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
        apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
        prefer 2
        apply(rule last_back_state_not_empty)
        apply(force)
       apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
       apply(clarsimp)
      apply(rename_tac w' q qa A Aa)(*strict*)
      apply(force)
     apply(rename_tac w' q qa A Aa)(*strict*)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
     apply(clarsimp)
     apply(rename_tac w' q qa A Aa Ga)(*strict*)
     apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
     apply(force)
    apply(rule conjI)
     apply(simp add: EValidSplitItem_elim_def)
    apply(simp add: EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(thin_tac "\<forall>x\<in> set S1. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from x))\<rparr> (ESplitItem_prods x) \<lparr>cfg_conf = option_to_list (ESplitItem_elem x) @ liftA (ESplitItem_to x)\<rparr> \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem x) \<longrightarrow> (\<forall>i<length (ESplitItem_prods x). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the (ESplitItem_elem x))) \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem x) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods x = []))")
    apply(rename_tac d)(*strict*)
    apply(simp add: option_to_list_def)
    apply(case_tac "ESplitItem_from SL")
     apply(rename_tac d)(*strict*)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
      apply(rename_tac d)(*strict*)
      prefer 2
      apply(rule_tac cfgLM_trans_der_from_empty)
      apply(simp add: option_to_list_def)
     apply(rename_tac d)(*strict*)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA A]\<rparr> SSe \<lparr>cfg_conf = [teB b,teA B]\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
     apply(rename_tac d a)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      in cfgLM.trans_der_der2)
       apply(rename_tac d a)(*strict*)
       apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(rename_tac d a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="e" for e
      in ballE)
       apply(rename_tac d a)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d a)(*strict*)
      apply(clarsimp)
      apply(simp add: cfg_configurations_def)
     apply(rename_tac d a)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
     apply(rename_tac d a)(*strict*)
     prefer 2
     apply(rule_tac
      ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<lparr>cfg_conf = [teB b, teA B]\<rparr>)"
      in cfgLM_trans_der_concat_extend)
       apply(rename_tac d a)(*strict*)
       apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
       apply(force)
      apply(rename_tac d a)(*strict*)
      apply(force)
     apply(rename_tac d a)(*strict*)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="derivation_append d (derivation_map (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<lparr>cfg_conf = [teB b, teA B]\<rparr>) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v\<rparr>)) (length (ESplitItem_prods SL))"
      in exI)
    apply(rename_tac d a)(*strict*)
    apply(rule conjI)
     apply(rename_tac d a)(*strict*)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac d a)(*strict*)
     prefer 2
     apply(rule_tac
      b="b"
      in cfgLM_trans_der_no_terminal_reached)
      apply(rename_tac d a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(force)
     apply(rename_tac d a)(*strict*)
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d a i)(*strict*)
    apply(case_tac "i\<le>length (ESplitItem_prods SL)")
     apply(rename_tac d a i)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(simp add: get_configuration_def derivation_map_def derivation_append_def)
    apply(rename_tac d a i)(*strict*)
    apply(clarsimp)
   apply(simp add: EValidSplitItem_def)
   apply(rule conjI)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(rule context_conjI)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      prefer 2
      apply(force)
     apply(clarsimp)
    apply(thin_tac "\<forall>x\<in> set S1. set (ESplitItem_elim x) \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_ignore x) \<subseteq> cfg_nonterminals G \<and> { xa. (Some xa = ESplitItem_from x)} \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_to x) \<subseteq> cfg_nonterminals G \<and> setA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_nonterminals G \<and> setB (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_events G \<and> set (ESplitItem_prods x) \<subseteq> cfg_productions G \<and> (\<forall>x\<in> set (ESplitItem_elim_prods x). set x \<subseteq> cfg_productions G) \<and> proper_l3_l2_seq (ESplitItem_elim x @ (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_ignore x) \<and> ((ESplitItem_to x = [] \<longrightarrow> filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) = [] \<longrightarrow> ESplitItem_ignore x \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_to x @ ESplitItem_ignore x)) \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
    apply(simp add: proper_l3_l2_seq_def)
    apply(clarsimp)
    apply(rename_tac w' q qa A Aa)(*strict*)
    apply(subgoal_tac "LR1ProdForm G")
     apply(rename_tac w' q qa A Aa)(*strict*)
     apply(simp add: LR1ProdForm_def)
     apply(erule_tac
      x=" \<lparr>prod_lhs = cons_l2 q A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac w' q qa A Aa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w' q qa A Aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' q qa A Aa q2)(*strict*)
     apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
      apply(rename_tac w' q qa A Aa q2)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac w' q qa A Aa q2)(*strict*)
     apply(erule_tac
      P="last_back_state w' = None"
      in disjE)
      apply(rename_tac w' q qa A Aa q2)(*strict*)
      apply(subgoal_tac "\<exists>w' x. [] = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
       apply(rename_tac w' q qa A Aa q2)(*strict*)
       prefer 2
       apply(rule last_back_state_not_empty)
       apply(force)
      apply(rename_tac w' q qa A Aa q2)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' q qa A Aa q2)(*strict*)
     apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some qa" for SSw)
      apply(rename_tac w' q qa A Aa q2)(*strict*)
      prefer 2
      apply(rule last_back_state_not_empty)
      apply(force)
     apply(rename_tac w' q qa A Aa q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
     apply(subgoal_tac "\<exists>w' x. [] = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
      apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
      prefer 2
      apply(rule last_back_state_not_empty)
      apply(force)
     apply(rename_tac q qa A Aa q2 w'a x)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' q qa A Aa)(*strict*)
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac w' q qa A Aa Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rule conjI)
    apply(simp add: EValidSplitItem_elim_def)
    apply(simp add: elim_map_def)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftA (option_to_list (Some B))\<rparr>"
      in exI)
   apply(simp add: option_to_list_def)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac d)(*strict*)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def F2LR1input_def valid_cfg_def)
    apply(clarsimp)
    apply(rename_tac d x)(*strict*)
    apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
     apply(rename_tac d x)(*strict*)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac d x)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d)(*strict*)
   apply(simp add: left_degen_def sat_refined_def)
   apply(clarsimp)
   apply(rename_tac d i)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac S2 S2L)
  apply(rename_tac S2 S2L)(*strict*)
  apply(simp add: nth_opt_def)
  apply(subgoal_tac "EValidSplit_interlineX SL S2")
   apply(rename_tac S2 S2L)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="length S1"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      t="S2"
      and s="((S1 @ SL # S2 # S2L) ! Suc (length S1))"
      in ssubst)
    apply(rename_tac S2 S2L)(*strict*)
    apply (metis ConsApp Suc_length concat_asso nth_append_length)
   apply(rename_tac S2 S2L)(*strict*)
   apply(force)
  apply(rename_tac S2 S2L)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(rule EValidSplit_interline_enlarge)
       apply(rename_tac S2 S2L)(*strict*)
       apply(force)
      apply(rename_tac S2 S2L)(*strict*)
      apply(force)
     apply(rename_tac S2 S2L S1' S1L)(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_interlineX_def)
    apply(rename_tac S2 S2L S2' S2F)(*strict*)
    apply(simp add: EValidSplit_interlineX_def)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: option_to_list_def)
   apply(simp add: EValidSplit_interlineX_def)
   apply(simp add: option_to_list_def)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplit_initial_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
    apply(case_tac S1)
     apply(rename_tac S2 S2L)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 S2L a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 S2L)(*strict*)
   apply(clarsimp)
   apply(case_tac S1)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 S2L a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplit_to_empty_def option_to_list_def)
   apply(subgoal_tac "S2L=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac S2 S2L)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac S2 S2L)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 x)(*strict*)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>, S2]) = SSv" for SSv)
     apply(rename_tac S2 x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac S2 x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac S2 x)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 x)(*strict*)
    apply(erule disjE)
     apply(rename_tac S2 x)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 x)(*strict*)
    apply(subgoal_tac "butlast (S1 @ [SL, S2]) = SSv" for SSv)
     apply(rename_tac S2 x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac S2 x)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 S2L)(*strict*)
   apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL # S2 # w' @ [a']) = SSv" for SSv)
    apply(rename_tac S2 x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast (S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr> # S2 # w' @ [a']) = SSv" for SSv)
    apply(rename_tac S2 x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac S2 x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplit_final_def)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(clarsimp)
   apply(rename_tac S2 S2L x)(*strict*)
   apply(subgoal_tac "S2L=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac S2 S2L x)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac S2 S2L x)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 S2L x)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 x)(*strict*)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>, S2]) = SSv" for SSv)
     apply(rename_tac S2 x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac S2 x)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>, S2]) = S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr>]")
    apply(rename_tac S2 x)(*strict*)
    apply(erule disjE)
     apply(rename_tac S2 x)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2)(*strict*)
     apply(erule_tac
      x="SL"
      in ballE)
      apply(rename_tac S2)(*strict*)
      apply(force)
     apply(rename_tac S2)(*strict*)
     apply (metis butLastSimp insert_Nil set_append2 set_subset_in)
    apply(rename_tac S2 x)(*strict*)
    apply(erule disjE)
     apply(rename_tac S2 x)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 x)(*strict*)
    apply(erule_tac
      x="x"
      in ballE)
     apply(rename_tac S2 x)(*strict*)
     apply(force)
    apply(rename_tac S2 x)(*strict*)
    apply (metis butLastSimp insert_Nil set_append_contra1)
   apply(rename_tac S2 S2L x)(*strict*)
   apply(clarsimp)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr> # S2 # w' @ [a']) = SSv" for SSv)
    apply(rename_tac S2 x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(clarsimp)
   apply(thin_tac "butlast (S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr> # S2 # w' @ [a']) = S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>], ESplitItem_elem := Some (teB b), ESplitItem_to := B # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some B, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA B), ESplitItem_to = []\<rparr> # S2 # w'")
   apply(rename_tac S2 x w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL # S2 # w' @ [a']) = (S1 @ SL # S2 # w')")
    apply(rename_tac S2 x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac S2 x w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac S2 x w' a' y ya yb)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a' y ya yb)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a' y ya yb)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a' y ya yb)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a' y ya yb)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a' y ya yb)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a' y ya yb)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 x w' a' y ya yb)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 x w' a' y ya yb)(*strict*)
   apply(clarsimp)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplit_produce_or_elim_def)
  apply(rename_tac S2 S2L)(*strict*)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplitItem_def)
   apply(rule conjI)
    apply(rename_tac S2 S2L)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(rule context_conjI)
     apply(rename_tac S2 S2L)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac S2 S2L)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac S2 S2L)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 S2L)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac S2 S2L)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac S2 S2L)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac S2 S2L)(*strict*)
     apply(clarsimp)
    apply(rename_tac S2 S2L)(*strict*)
    apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2L. set (ESplitItem_elim x) \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_ignore x) \<subseteq> cfg_nonterminals G \<and> { xa. (Some xa = ESplitItem_from x)} \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_to x) \<subseteq> cfg_nonterminals G \<and> setA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_nonterminals G \<and> setB (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_events G \<and> set (ESplitItem_prods x) \<subseteq> cfg_productions G \<and> (\<forall>x\<in> set (ESplitItem_elim_prods x). set x \<subseteq> cfg_productions G) \<and> proper_l3_l2_seq (ESplitItem_elim x @ (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_ignore x) \<and> ((ESplitItem_to x = [] \<longrightarrow> filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) = [] \<longrightarrow> ESplitItem_ignore x \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_to x @ ESplitItem_ignore x)) \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
    apply(rename_tac S2 S2L)(*strict*)
    apply(subgoal_tac "S2L=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac S2 S2L)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac S2 S2L)(*strict*)
    apply(erule disjE)
     apply(rename_tac S2 S2L)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2)(*strict*)
     apply(simp add: EValidSplit_final_def)
     apply(clarsimp)
     apply(simp add: EValidSplit_produce_or_elim_def)
     apply(clarsimp)
     apply(simp add: EValidSplit_producing_def)
     apply(subgoal_tac "butlast (S1 @ [SL, S2]) = S1@[SL]")
      apply(rename_tac S2)(*strict*)
      prefer 2
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac S2)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 y)(*strict*)
     apply(subgoal_tac "LR1ProdForm G")
      apply(rename_tac S2 y)(*strict*)
      apply(simp add: LR1ProdForm_def)
      apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
       apply(rename_tac S2 y)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac S2 y)(*strict*)
      apply(clarsimp)
      apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
      apply(erule disjE)
       apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
       apply(clarsimp)
       apply(rename_tac S2 y q1 q2 A1)(*strict*)
       apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
        apply(rename_tac S2 y q1 q2 A1)(*strict*)
        prefer 2
        apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
        apply(force)
       apply(rename_tac S2 y q1 q2 A1)(*strict*)
       apply(clarsimp)
      apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
      apply(clarsimp)
      apply(rename_tac S2 y q1 q2 q3 A1)(*strict*)
      apply(rule proper_l3_l2_seq_replace_first)
      apply(force)
     apply(rename_tac S2 y)(*strict*)
     apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
     apply(clarsimp)
     apply(rename_tac S2 y Ga)(*strict*)
     apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
     apply(force)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 w' a')(*strict*)
    apply(subgoal_tac "LR1ProdForm G")
     apply(rename_tac S2 w' a')(*strict*)
     apply(simp add: LR1ProdForm_def)
     apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac S2 w' a')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac S2 w' a')(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
     apply(erule disjE)
      apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
      apply(clarsimp)
      apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
      apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
       apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
       prefer 2
       apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
       apply(force)
      apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
      apply(clarsimp)
      apply(simp add: proper_l3_l2_seq_def)
     apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 w' a' q1 q2 q3 A1)(*strict*)
     apply(rule proper_l3_l2_seq_replace_first)
     apply(force)
    apply(rename_tac S2 w' a')(*strict*)
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac S2 w' a' Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rename_tac S2 S2L)(*strict*)
   apply(rule conjI)
    apply(rename_tac S2 S2L)(*strict*)
    apply(simp add: EValidSplitItem_elim_def)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac S2 S2L d da)(*strict*)
   apply(simp add: option_to_list_def)
   apply(thin_tac " \<forall>x\<in> set S1 \<union> set S2L. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A])\<rparr> (ESplitItem_prods x) \<lparr>cfg_conf = (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ liftA (ESplitItem_to x)\<rparr> \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem x) \<longrightarrow> (\<forall>i<length (ESplitItem_prods x). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the (ESplitItem_elem x))) \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem x) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods x = []))")
   apply(rename_tac S2 S2L d da)(*strict*)
   apply(case_tac "ESplitItem_from SL")
    apply(rename_tac S2 S2L d da)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac S2 S2L d da)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(simp add: option_to_list_def)
    apply(rename_tac S2 S2L d da)(*strict*)
    apply(force)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA A]\<rparr> SSe \<lparr>cfg_conf = [teB b,teA B]\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
    apply(rename_tac S2 S2L d da a)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?e="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in cfgLM.trans_der_der2)
      apply(rename_tac S2 S2L d da a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
     apply(rename_tac S2 S2L d da a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac S2 S2L d da a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac S2 S2L d da a)(*strict*)
     apply(clarsimp)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac S2 S2L d da a)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(force)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac S2 S2L d da a)(*strict*)
    prefer 2
    apply(rule_tac
      ?v1.0="[]"
      and ?v4.0="liftA (ESplitItem_to SL)"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<lparr>cfg_conf = [teB b, teA B]\<rparr>)"
      in cfgLM_trans_der_concat_extend)
      apply(rename_tac S2 S2L d da a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(force)
     apply(rename_tac S2 S2L d da a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac S2 S2L d da a)(*strict*)
    apply(force)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_append d (derivation_map (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<lparr>cfg_conf = [teB b, teA B]\<rparr>) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA (ESplitItem_to SL)\<rparr>)) (length (ESplitItem_prods SL))"
      in exI)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(rule conjI)
    apply(rename_tac S2 S2L d da a)(*strict*)
    apply(force)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac S2 S2L d da a)(*strict*)
    prefer 2
    apply(rule_tac
      b="b"
      in cfgLM_trans_der_no_terminal_reached)
     apply(rename_tac S2 S2L d da a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
     apply(force)
    apply(rename_tac S2 S2L d da a)(*strict*)
    apply(force)
   apply(rename_tac S2 S2L d da a)(*strict*)
   apply(clarsimp)
   apply(rename_tac S2 S2L d da a i)(*strict*)
   apply(case_tac "i\<le>length (ESplitItem_prods SL)")
    apply(rename_tac S2 S2L d da a i)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(simp add: get_configuration_def derivation_map_def derivation_append_def)
   apply(rename_tac S2 S2L d da a i)(*strict*)
   apply(clarsimp)
  apply(rename_tac S2 S2L)(*strict*)
  apply(simp add: EValidSplitItem_def)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplitItem_belongs_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(rule context_conjI)
    apply(rename_tac S2 S2L)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
     apply(rename_tac S2 S2L)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
   apply(rename_tac S2 S2L)(*strict*)
   apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2L. set (ESplitItem_elim x) \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_ignore x) \<subseteq> cfg_nonterminals G \<and> { xa. (Some xa = ESplitItem_from x)} \<subseteq> cfg_nonterminals G \<and> set (ESplitItem_to x) \<subseteq> cfg_nonterminals G \<and> setA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_nonterminals G \<and> setB (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) \<subseteq> cfg_events G \<and> set (ESplitItem_prods x) \<subseteq> cfg_productions G \<and> (\<forall>x\<in> set (ESplitItem_elim_prods x). set x \<subseteq> cfg_productions G) \<and> proper_l3_l2_seq (ESplitItem_elim x @ (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_ignore x) \<and> ((ESplitItem_to x = [] \<longrightarrow> filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) = [] \<longrightarrow> ESplitItem_ignore x \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_to x @ ESplitItem_ignore x)) \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
   apply(rename_tac S2 S2L)(*strict*)
   apply(subgoal_tac "S2L=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac S2 S2L)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac S2 S2L)(*strict*)
   apply(erule disjE)
    apply(rename_tac S2 S2L)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2)(*strict*)
    apply(simp add: EValidSplit_final_def)
    apply(clarsimp)
    apply(simp add: EValidSplit_produce_or_elim_def)
    apply(clarsimp)
    apply(simp add: EValidSplit_producing_def)
    apply(subgoal_tac "butlast (S1 @ [SL, S2]) = S1@[SL]")
     apply(rename_tac S2)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac S2)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 y)(*strict*)
    apply(subgoal_tac "LR1ProdForm G")
     apply(rename_tac S2 y)(*strict*)
     apply(simp add: LR1ProdForm_def)
     apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
      apply(rename_tac S2 y)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac S2 y)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
     apply(erule disjE)
      apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
      apply(clarsimp)
      apply(rename_tac S2 y q1 q2 A1)(*strict*)
      apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
       apply(rename_tac S2 y q1 q2 A1)(*strict*)
       prefer 2
       apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
       apply(force)
      apply(rename_tac S2 y q1 q2 A1)(*strict*)
      apply(clarsimp)
     apply(rename_tac S2 y ba q1 q2 q3 A1)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 y q1 q2 q3 A1)(*strict*)
     apply(rule proper_l3_l2_seq_replace_first)
     apply(force)
    apply(rename_tac S2 y)(*strict*)
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac S2 y Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rename_tac S2 S2L)(*strict*)
   apply(clarsimp)
   apply(rename_tac S2 w' a')(*strict*)
   apply(subgoal_tac "LR1ProdForm G")
    apply(rename_tac S2 w' a')(*strict*)
    apply(simp add: LR1ProdForm_def)
    apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
     apply(rename_tac S2 w' a')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac S2 w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
    apply(erule disjE)
     apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
     apply(clarsimp)
     apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
     apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
      apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
      prefer 2
      apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
      apply(force)
     apply(rename_tac S2 w' a' q1 q2 A1)(*strict*)
     apply(clarsimp)
     apply(simp add: proper_l3_l2_seq_def)
    apply(rename_tac S2 w' a' ba q1 q2 q3 A1)(*strict*)
    apply(clarsimp)
    apply(rename_tac S2 w' a' q1 q2 q3 A1)(*strict*)
    apply(rule proper_l3_l2_seq_replace_first)
    apply(force)
   apply(rename_tac S2 w' a')(*strict*)
   apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
   apply(clarsimp)
   apply(rename_tac S2 w' a' Ga)(*strict*)
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(force)
  apply(rename_tac S2 S2L)(*strict*)
  apply(rule conjI)
   apply(rename_tac S2 S2L)(*strict*)
   apply(simp add: EValidSplitItem_elim_def)
   apply(simp add: elim_map_def)
  apply(rename_tac S2 S2L)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac S2 S2L d da)(*strict*)
  apply(simp add: option_to_list_def)
  apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2L. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (case ESplitItem_from x of None \<Rightarrow> [] | Some A \<Rightarrow> [A])\<rparr> (ESplitItem_prods x) \<lparr>cfg_conf = (case ESplitItem_elem x of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ liftA (ESplitItem_to x)\<rparr> \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem x) \<longrightarrow> (\<forall>i<length (ESplitItem_prods x). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the (ESplitItem_elem x))) \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem x) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods x = []))")
  apply(rename_tac S2 S2L d da)(*strict*)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA B]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac S2 S2L d da)(*strict*)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac S2 S2L d da)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(clarsimp)
   apply(rename_tac S2 S2L d da)(*strict*)
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr>"
      in ballE)
    apply(rename_tac S2 S2L d da)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac S2 S2L d da)(*strict*)
   apply(clarsimp)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac S2 S2L d da)(*strict*)
  apply(simp add: left_degen_def der1_def sat_refined_def)
  done

lemma Esplit_inst_AX_step_relation_preserves_belongs3: "
       Esplit_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2)
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setA (Esplit_signature S2) = {}
  \<Longrightarrow> ESplitItem_elem SL = Some (teA A)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr> # Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2)"
  apply(subgoal_tac "EValidSplit G (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr>], ESplitItem_elem := Some (teA B)\<rparr>]@S2)")
   apply(case_tac S2)
    apply(simp add: Xstep_gen_def Xstep_mergeL_def Xstep_elem_def Xstep_gen_def Xstep_merge1_def nth_opt_def)
   apply(rename_tac a list)(*strict*)
   apply(simp add: Xstep_gen_def Xstep_mergeL_def Xstep_elem_def Xstep_gen_def Xstep_merge1_def nth_opt_def)
  apply(subgoal_tac "S2=[]")
   prefer 2
   apply(case_tac S2)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "LR1ProdForm G")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac a list Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(simp add: LR1ProdForm_def)
   apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr>"
      in ballE)
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list q1 q2 A1 A2)(*strict*)
   apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL=[]")
    apply(rename_tac a list q1 q2 A1 A2)(*strict*)
    prefer 2
    apply(subgoal_tac "(ESplitItem_to SL = [] \<longrightarrow> filterA (option_to_list (Some (teA (cons_l2   q1 A1)))) = [] \<longrightarrow> ESplitItem_ignore SL \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (option_to_list (Some (teA (cons_l2   q1 A1)))) @ ESplitItem_to SL @ ESplitItem_ignore SL)")
     apply(rename_tac a list q1 q2 A1 A2)(*strict*)
     prefer 2
     apply(subgoal_tac "EValidSplitItem_belongs G SL")
      apply(rename_tac a list q1 q2 A1 A2)(*strict*)
      prefer 2
      apply(simp add: EValidSplit_def EValidSplitItem_def EValidSplit_ValidItem_def)
     apply(rename_tac a list q1 q2 A1 A2)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def)
     apply(force)
    apply(rename_tac a list q1 q2 A1 A2)(*strict*)
    apply(erule impE)
     apply(rename_tac a list q1 q2 A1 A2)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
    apply(rename_tac a list q1 q2 A1 A2)(*strict*)
    apply(simp add: option_to_list_def)
    apply(simp add: proper_l3_l2_seq_def)
    apply(clarsimp)
    apply(rename_tac a list q1 q2 A1 A2 w' q A)(*strict*)
    apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac a list q1 q2 A1 A2 w' q A)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac a list q1 q2 A1 A2 w' q A)(*strict*)
    apply(erule_tac
      P="ESplitItem_to SL @ ESplitItem_ignore SL = []"
      in disjE)
     apply(rename_tac a list q1 q2 A1 A2 w' q A)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list q1 q2 A1 A2 w' q A)(*strict*)
    apply(clarsimp)
    apply(rename_tac a list q1 q2 A1 A2 q A w'a)(*strict*)
    apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
    apply(clarsimp)
    apply(erule_tac
      x="[]"
      in allE)
    apply(force)
   apply(rename_tac a list q1 q2 A1 A2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "EValidSplit_interlineX SL a")
    apply(rename_tac a list q1 q2 A1 A2)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_interline_def)
    apply(clarsimp)
    apply(erule_tac
      x="length S1"
      in allE)
    apply(clarsimp)
    apply(rule_tac
      t="a"
      and s="((S1 @ SL # a # list) ! Suc (length S1))"
      in ssubst)
     apply(rename_tac a list q1 q2 A1 A2)(*strict*)
     apply (metis ConsApp Suc_length concat_asso nth_append_length)
    apply(rename_tac a list q1 q2 A1 A2)(*strict*)
    apply(force)
   apply(rename_tac a list q1 q2 A1 A2)(*strict*)
   apply(simp add: EValidSplit_interlineX_def)
   apply(clarsimp)
   apply(simp add: EValidSplit_def EValidSplit_produce_or_elim_def)
   apply(clarsimp)
   apply(rename_tac a list q1 q2 A1 A2 y)(*strict*)
   apply(simp add: option_to_list_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_def)
  apply(rule conjI)
   apply(rule EValidSplit_interline_preserve)
      apply(force)
     apply(force)
    apply(rename_tac S1' S1L)(*strict*)
    apply(simp add: EValidSplit_interlineX_def)
   apply(rename_tac S2' S2F)(*strict*)
   apply(simp add: EValidSplit_interlineX_def)
  apply(rule conjI)
   apply(simp add: EValidSplit_initial_def)
   apply(clarsimp)
   apply(case_tac S1)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_to_empty_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_final_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_producing_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_produce_or_elim_def)
   apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_def)
  apply(rule conjI)
   apply(thin_tac "\<forall>x\<in> set S1. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
   apply(simp add: EValidSplitItem_belongs_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(simp add: EValidSplit_final_def)
   apply(simp add: proper_l3_l2_seq_def)
   apply(clarsimp)
   apply(rename_tac w' q qa A Aa)(*strict*)
   apply(subgoal_tac "LR1ProdForm G")
    apply(rename_tac w' q qa A Aa)(*strict*)
    apply(simp add: LR1ProdForm_def)
    apply(erule_tac
      x=" \<lparr>prod_lhs = cons_l2 q A, prod_rhs = [teA B]\<rparr>"
      in ballE)
     apply(rename_tac w' q qa A Aa)(*strict*)
     prefer 2
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(rename_tac w' q qa A Aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q qa A Aa q2 A2)(*strict*)
    apply(rule conjI)
     apply(rename_tac w' q qa A Aa q2 A2)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x=" \<lparr>prod_lhs = cons_l2 q A, prod_rhs = [teA (cons_l2   q2 A2)]\<rparr>"
      in ballE)
      apply(rename_tac w' q qa A Aa q2 A2)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w' q qa A Aa q2 A2)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' q qa A Aa q2 A2)(*strict*)
    apply(clarsimp)
    apply(simp add: last_back_state_def)
   apply(rename_tac w' q qa A Aa)(*strict*)
   apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
   apply(clarsimp)
   apply(rename_tac w' q qa A Aa Ga)(*strict*)
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(force)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_elim_def)
  apply(thin_tac "\<forall>x\<in> set S1. EValidSplitItem_belongs G x \<and> EValidSplitItem_elim G x \<and> EValidSplitItem_gen G x")
  apply(clarsimp)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(case_tac "ESplitItem_from SL")
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    apply(rename_tac d)(*strict*)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA A]\<rparr> SSe \<lparr>cfg_conf = [teA B]\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
   apply(rename_tac d a)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in cfgLM.trans_der_der2)
     apply(rename_tac d a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
    apply(rename_tac d a)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="e" for e
      in ballE)
     apply(rename_tac d a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d a)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(force)
  apply(rename_tac d a)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d a)(*strict*)
   prefer 2
   apply(rule_tac
      ?v1.0="[]"
      and ?v4.0="liftA (ESplitItem_to SL)"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr> \<lparr>cfg_conf = [teA B]\<rparr>)"
      in cfgLM_trans_der_concat_extend)
     apply(rename_tac d a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
     apply(force)
    apply(rename_tac d a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d a)(*strict*)
   apply(force)
  apply(rename_tac d a)(*strict*)
  apply(rule_tac
      x="derivation_append d (derivation_map (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr> \<lparr>cfg_conf = [teA B]\<rparr>) (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (ESplitItem_to SL)\<rparr>)) (length (ESplitItem_prods SL))"
      in exI)
  apply(rename_tac d a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d a)(*strict*)
   apply(force)
  apply(rename_tac d a)(*strict*)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac d a i)(*strict*)
  apply(case_tac "i<length (ESplitItem_prods SL)")
   apply(rename_tac d a i)(*strict*)
   apply(simp add: derivation_append_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac "d (Suc i)")
    apply(rename_tac d a i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d a i aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac d a i aa option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d a i option b)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac d a i)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def der2_def)
  apply(clarsimp)
  apply(rename_tac d a)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  done

lemma Esplit_inst_AX_step_relation_preserves_belongs4: "
  Esplit_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ SL # S2)
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setA (Esplit_signature S2) = {}
  \<Longrightarrow> ESplitItem_elem SL = Some (teA A)
  \<Longrightarrow> EValidSplit G (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr> # Xstep_gen [C] (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2)"
  apply(subgoal_tac "EValidSplit G (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>], ESplitItem_elem := Some (teA B), ESplitItem_to := C # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some C, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA C), ESplitItem_to = []\<rparr>]@S2)")
   apply(subgoal_tac "nat_seq 0 0=[0]")
    apply(case_tac S2)
     apply(simp add: Xstep_gen_def Xstep_mergeL_def Xstep_elem_def Xstep_gen_def Xstep_merge1_def nth_opt_def)
    apply(rename_tac a list)(*strict*)
    apply(simp add: Xstep_gen_def Xstep_mergeL_def Xstep_elem_def Xstep_gen_def Xstep_merge1_def nth_opt_def)
   apply (metis natUptTo_n_n)
  apply(simp add: EValidSplit_def)
  apply(rule conjI)
   apply(rule EValidSplit_interline_enlarge)
       apply(force)
      apply(force)
     apply(rename_tac S1' S1L)(*strict*)
     apply(simp add: EValidSplit_interlineX_def)
    apply(rename_tac S2' S2F)(*strict*)
    apply(simp add: EValidSplit_interlineX_def)
   apply(simp add: EValidSplit_interlineX_def option_to_list_def)
  apply(rule conjI)
   apply(simp add: EValidSplit_initial_def)
   apply(clarsimp)
   apply(case_tac S1)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_to_empty_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>], ESplitItem_elem := Some (teA B), ESplitItem_to := C # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some C, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA C), ESplitItem_to = []\<rparr>]) = SSv" for SSv)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>], ESplitItem_elem := Some (teA B), ESplitItem_to := C # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some C, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA C), ESplitItem_to = []\<rparr> # w' @ [a'])=SSv" for SSv)
    apply(rename_tac x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL # w' @ [a']) = SSv" for SSv)
    apply(rename_tac x w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x w' a')(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac x w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac x w' a')(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac x w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac x w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac x w' a')(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_final_def)
   apply(clarsimp)
   apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    prefer 2
    apply(rule case_list)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_producing_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "ESplitItem_from SL")
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "EValidSplitItem_gen G SL")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac x)(*strict*)
    apply(simp add: EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac x d)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac x a)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac x a)(*strict*)
   apply(erule disjE)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast (S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>], ESplitItem_elem := Some (teA B), ESplitItem_to := C # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some C, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA C), ESplitItem_to = []\<rparr>]) = SSv" for SSv)
     apply(rename_tac x a)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac x a)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x a w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>], ESplitItem_elem := Some (teA B), ESplitItem_to := C # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some C, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA C), ESplitItem_to = []\<rparr> # w' @ [a'])=SSv" for SSv)
    apply(rename_tac x a w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x a w' a')(*strict*)
   apply(subgoal_tac "butlast (S1 @ SL # w' @ [a']) = SSv" for SSv)
    apply(rename_tac x a w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x a w' a')(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac x a w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac x a w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac x a w' a')(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac x a w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac x a w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac x a w' a')(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: EValidSplit_produce_or_elim_def)
   apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(clarsimp)
  apply(thin_tac "\<forall>x\<in> set S1 \<union> set S2. EValidSplitItem G x")
  apply(subgoal_tac "\<lparr>cfg_conf=[teA A,teA B,teA C]\<rparr>\<in> cfg_configurations G")
   prefer 2
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = [teA B,teA C]\<rparr>"
      in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(simp add: cfg_configurations_def)
  apply(simp add: EValidSplitItem_def)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_belongs_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(simp add: cfg_configurations_def)
   apply(subgoal_tac "LR1ProdForm G")
    prefer 2
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(simp add: LR1ProdForm_def)
   apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teA B,teA C]\<rparr>"
      in ballE)
    prefer 2
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
   apply(erule disjE)
    apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
    apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
     apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
     prefer 2
     apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
     apply(force)
    apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
    apply(clarsimp)
    apply(simp add: proper_l3_l2_seq_def)
    apply(simp add: only_l3_nonterminals_def only_l3_nonterminals_and_l3_adjacency_def proper_l3_seq_def)
    apply(rule conjI)
     apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1 q2 q3 A1 A2 w' q w1 w2 xA A)(*strict*)
     apply(case_tac w1)
      apply(rename_tac q1 q2 q3 A1 A2 w' q w1 w2 xA A)(*strict*)
      apply(clarsimp)
     apply(rename_tac q1 q2 q3 A1 A2 w' q w1 w2 xA A a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
    apply(rule disjI2)
    apply(simp add: last_back_state_def)
   apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "proper_l3_l2_seq (cons_l3 q3 A1 q4 # ESplitItem_to SL @ ESplitItem_ignore SL)")
    apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
    prefer 2
    apply(rule proper_l3_l2_seq_replace_first)
    apply(force)
   apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
   apply(rule proper_l3_l2_seq_enlarge)
   apply(force)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_elim_def)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(case_tac "ESplitItem_from SL")
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac d)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = [teA A]\<rparr> SSe \<lparr>cfg_conf = [teA B,teA C]\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
    apply(rename_tac d a)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in cfgLM.trans_der_der2)
      apply(rename_tac d a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
     apply(rename_tac d a)(*strict*)
     apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="e" for e
      in ballE)
      apply(rename_tac d a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d a)(*strict*)
     apply(clarsimp)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac d a)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(force)
   apply(rename_tac d a)(*strict*)
   apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac d a)(*strict*)
    prefer 2
    apply(rule_tac
      ?v1.0="[]"
      and ?v4.0="liftA (ESplitItem_to SL)"
      and ?d1.0="d"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA B,teA C]\<rparr> \<lparr>cfg_conf = [teA B,teA C]\<rparr>)"
      in cfgLM_trans_der_concat_extend)
      apply(rename_tac d a)(*strict*)
      apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
      apply(force)
     apply(rename_tac d a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d a)(*strict*)
    apply(force)
   apply(rename_tac d a)(*strict*)
   apply(rule_tac
      x="derivation_append d (derivation_map (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA B,teA C]\<rparr> \<lparr>cfg_conf = [teA B,teA C]\<rparr>) (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (ESplitItem_to SL)\<rparr>)) (length (ESplitItem_prods SL))"
      in exI)
   apply(rename_tac d a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(force)
   apply(rename_tac d a)(*strict*)
   apply(simp add: left_degen_def sat_refined_def)
   apply(clarsimp)
   apply(rename_tac d a i)(*strict*)
   apply(case_tac "i<length (ESplitItem_prods SL)")
    apply(rename_tac d a i)(*strict*)
    apply(simp add: derivation_append_def)
    apply(erule_tac
      x="i"
      in allE)
    apply(case_tac "d (Suc i)")
     apply(rename_tac d a i)(*strict*)
     apply(clarsimp)
    apply(rename_tac d a i aa)(*strict*)
    apply(clarsimp)
    apply(case_tac aa)
    apply(rename_tac d a i aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d a i option b)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac d a i)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def der2_def)
   apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_belongs_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(simp add: cfg_configurations_def)
   apply(subgoal_tac "LR1ProdForm G")
    prefer 2
    apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
    apply(clarsimp)
    apply(rename_tac Ga)(*strict*)
    apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
    apply(force)
   apply(simp add: LR1ProdForm_def)
   apply(erule_tac
      x=" \<lparr>prod_lhs = A, prod_rhs = [teA B,teA C]\<rparr>"
      in ballE)
    prefer 2
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
   apply(erule disjE)
    apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
    apply(subgoal_tac "ESplitItem_to SL @ ESplitItem_ignore SL = []")
     apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
     prefer 2
     apply(rule_tac
      w="[]"
      in l2_in_proper_l3_l2_seq_at_end)
     apply(force)
    apply(rename_tac q1 q2 q3 A1 A2)(*strict*)
    apply(clarsimp)
    apply(simp add: proper_l3_l2_seq_def)
    apply(rule disjI1)
    apply(simp add: last_back_state_def)
   apply(rename_tac q1 q2 q3 q4 A1 A2)(*strict*)
   apply(clarsimp)
   apply(rule proper_l3_l2_seq_replace_first)
   apply(force)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_elim_def)
   apply(simp add: elim_map_def)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA C]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac d)(*strict*)
    apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def valid_cfg_def cfg_configurations_def)
  apply(rename_tac d)(*strict*)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac i)
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac d i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat)(*strict*)
  apply(simp add: der1_def)
  done

lemma Esplit_inst_AX_step_relation_preserves_belongs: "
\<forall>G. Esplit_TSstructure G \<longrightarrow>
        (\<forall>c1 e c2.
            Esplit_step_relation G c1 e c2 \<longrightarrow>
            c1 \<in> Esplit_configurations G \<longrightarrow>
            e \<in> Esplit_step_labels G \<and> c2 \<in> Esplit_configurations G)"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: Esplit_step_relation_def Esplit_step_labels_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: Esplit_step_labels_def)
  apply(simp add: Esplit_configurations_def Esplit_step_relation_def Esplit_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G e S1 SL S2)(*strict*)
  apply(subgoal_tac "\<forall>p\<in> cfg_productions G. prod_rhs p = [] \<or> (\<exists>b A B. p = \<lparr>prod_lhs = A, prod_rhs = [teB b, teA B]\<rparr> \<or> p = \<lparr>prod_lhs = A, prod_rhs = [teA B]\<rparr> \<or> (\<exists>C. p = \<lparr>prod_lhs = A, prod_rhs = [teA B, teA C]\<rparr>))")
   apply(rename_tac G e S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_TSstructure_def split_TSstructure_def LR1ProdFormSimp_def)
  apply(rename_tac G e S1 SL S2)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac G e S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e S1 SL S2)(*strict*)
  apply(erule disjE)
   apply(rename_tac G e S1 SL S2)(*strict*)
   apply(rule Esplit_inst_AX_step_relation_preserves_belongs1)
        apply(rename_tac G e S1 SL S2)(*strict*)
        apply(force)
       apply(rename_tac G e S1 SL S2)(*strict*)
       apply(force)
      apply(rename_tac G e S1 SL S2)(*strict*)
      apply(force)
     apply(rename_tac G e S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac G e S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac G e S1 SL S2)(*strict*)
   apply(force)
  apply(rename_tac G e S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e S1 SL S2 b A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac G e S1 SL S2 b A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac G S1 SL S2 b A B)(*strict*)
   apply(rule Esplit_inst_AX_step_relation_preserves_belongs2)
       apply(rename_tac G S1 SL S2 b A B)(*strict*)
       apply(force)
      apply(rename_tac G S1 SL S2 b A B)(*strict*)
      apply(force)
     apply(rename_tac G S1 SL S2 b A B)(*strict*)
     apply(force)
    apply(rename_tac G S1 SL S2 b A B)(*strict*)
    apply(force)
   apply(rename_tac G S1 SL S2 b A B)(*strict*)
   apply(force)
  apply(rename_tac G e S1 SL S2 b A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e S1 SL S2 A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac G e S1 SL S2 A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac G S1 SL S2 A B)(*strict*)
   apply(rule Esplit_inst_AX_step_relation_preserves_belongs3)
       apply(rename_tac G S1 SL S2 A B)(*strict*)
       apply(force)
      apply(rename_tac G S1 SL S2 A B)(*strict*)
      apply(force)
     apply(rename_tac G S1 SL S2 A B)(*strict*)
     apply(force)
    apply(rename_tac G S1 SL S2 A B)(*strict*)
    apply(force)
   apply(rename_tac G S1 SL S2 A B)(*strict*)
   apply(force)
  apply(rename_tac G e S1 SL S2 A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac G S1 SL S2 A B C)(*strict*)
  apply(rule Esplit_inst_AX_step_relation_preserves_belongs4)
      apply(rename_tac G S1 SL S2 A B C)(*strict*)
      apply(force)
     apply(rename_tac G S1 SL S2 A B C)(*strict*)
     apply(force)
    apply(rename_tac G S1 SL S2 A B C)(*strict*)
    apply(force)
   apply(rename_tac G S1 SL S2 A B C)(*strict*)
   apply(force)
  apply(rename_tac G S1 SL S2 A B C)(*strict*)
  apply(force)
  done

interpretation "Esplit" : ATS_Language0
  (* TSstructure *)
  "Esplit_TSstructure"
  (* configurations *)
  "Esplit_configurations"
  (* initial_configurations *)
  "Esplit_initial_configurations"
  (* step_labels *)
  "Esplit_step_labels"
  (* step_relation *)
  "Esplit_step_relation"
  (* effects *)
  "Esplit_effects"
  (* marking_condition *)
  "Esplit_marking_condition"
  (* marked_effect *)
  "Esplit_marked_effect"
  (* unmarked_effect *)
  "Esplit_unmarked_effect"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: Esplit_inst_AX_initial_configuration_belongs )
  apply(simp add: Esplit_inst_AX_step_relation_preserves_belongs )
  done

lemma EValidSplit_Esplit_signature_length: "
  EValidSplit G (S@S')
  \<Longrightarrow> length S = length (Esplit_signature S)
  \<or> (length S = Suc(length (Esplit_signature S)) \<and> S'=[])"
  apply(induct S arbitrary: S' rule: rev_induct)
   apply(rename_tac S')(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_def Esplit_signature_def)
  apply(rename_tac x xs S')(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="x#S'"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: EValidSplit_def Esplit_signature_def)
  apply(simp add: option_to_list_def)
  apply(case_tac x)
  apply(rename_tac x xs S' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_to)(*strict*)
  apply(rename_tac el f i ep p e t)
  apply(rename_tac x xs S' el f i ep p e t)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs S' el f i ep p e t)(*strict*)
  apply(case_tac e)
   apply(rename_tac xs S' el f i ep p e t)(*strict*)
   prefer 2
   apply(rename_tac xs S' el f i ep p e t a)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs S' el f i ep p e t)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs S' el f i ep p t)(*strict*)
  apply(subgoal_tac "S'=[] \<or> (\<exists>w' a'. S'=w'@[a'])")
   apply(rename_tac xs S' el f i ep p t)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac xs S' el f i ep p t)(*strict*)
  apply(erule disjE)
   apply(rename_tac xs S' el f i ep p t)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs S' el f i ep p t)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs el f i ep p t w' a')(*strict*)
  apply(simp add: EValidSplit_produce_or_elim_def EValidSplit_producing_def EValidSplit_ValidItem_def)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>ESplitItem_elim = el, ESplitItem_from = f, ESplitItem_ignore = i, ESplitItem_elim_prods = ep, ESplitItem_prods = p, ESplitItem_elem = None, ESplitItem_to = t\<rparr>"
      and P="\<lambda>e. (\<exists>y. ESplitItem_from e = Some y) \<and> (\<exists>y. ESplitItem_elem e = Some y)"
      in ballE)
   apply(rename_tac xs el f i ep p t w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac xs el f i ep p t w' a')(*strict*)
  apply(subgoal_tac "\<lparr>ESplitItem_elim = el, ESplitItem_from = f, ESplitItem_ignore = i, ESplitItem_elim_prods = ep, ESplitItem_prods = p, ESplitItem_elem = None, ESplitItem_to = t\<rparr> \<in> set (butlast (xs @ \<lparr>ESplitItem_elim = el, ESplitItem_from = f, ESplitItem_ignore = i, ESplitItem_elim_prods = ep, ESplitItem_prods = p, ESplitItem_elem = None, ESplitItem_to = t\<rparr> # w' @ [a']))")
   apply(rename_tac xs el f i ep p t w' a')(*strict*)
   apply(force)
  apply(rename_tac xs el f i ep p t w' a')(*strict*)
  apply (metis ConsApp append_Cons butlast_snoc_2 set_bi_append set_subset_in)
  done

lemma Esplit_signature_append: "
  Esplit_signature (w@v) = Esplit_signature w @ Esplit_signature v"
  apply(simp add: Esplit_signature_def)
  apply(rule foldl_first)
  done

lemma ESplit_cfgRM_step_can_be_simulated: "
  Esplit_TSstructure G
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> Esplit_signature S = w
  \<Longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf=w\<rparr> e \<lparr>cfg_conf=w'\<rparr>
  \<Longrightarrow> \<exists>S'. EValidSplit G S' \<and> Esplit_signature S' = w' \<and> Esplit_step_relation G S e S'"
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = r")
   apply(rename_tac l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac l l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e)
  apply(rename_tac l l' prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac l l' A w)(*strict*)
  apply(clarsimp)
  apply(simp add: Esplit_step_relation_def)
  apply(subgoal_tac "\<exists>S1 SL S2. \<exists>S'. EValidSplit G S' \<and> Esplit_signature S' = l @ w @ liftB l' \<and> (S = S1 @ SL # S2 \<and> setA (Esplit_signature S2) = {} \<and> ESplitItem_elem SL = Some (teA A) \<and> S' = S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2)")
   apply(rename_tac l l' A w)(*strict*)
   apply(erule exE)+
   apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
   apply(rule_tac
      x="S'"
      in exI)
   apply(rule conjI)
    apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
    apply(force)
   apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
   apply(rule conjI)
    apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
    apply(force)
   apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
   apply(force)
  apply(rename_tac l l' A w)(*strict*)
  apply(subgoal_tac "\<exists>S1 SL S2 S'. Esplit_signature S' = l @ w @ liftB l' \<and> S = S1 @ SL # S2 \<and> setA (Esplit_signature S2) = {} \<and> ESplitItem_elem SL = Some (teA A) \<and> S' = S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2")
   apply(rename_tac l l' A w)(*strict*)
   apply(erule exE)+
   apply(rename_tac l l' A w S1 SL S2 S')(*strict*)
   apply(rule_tac
      x="S1"
      in exI)
   apply(rule_tac
      x="SL"
      in exI)
   apply(rule_tac
      x="S2"
      in exI)
   apply(rule_tac
      x="S'"
      in exI)
   apply(clarsimp)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(subgoal_tac "(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2) \<in> Esplit_configurations G")
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    apply(simp add: Esplit_configurations_def)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(rule_tac
      ?c1.0="S1@SL#S2"
      and e="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      in Esplit.AX_step_relation_preserves_belongsC)
     apply(rename_tac l l' A w S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    apply(simp add: Esplit_step_relation_def)
    apply(rule_tac
      x="take (length l) (S1@SL#S2)"
      in exI)
    apply(rule_tac
      x="(S1@SL#S2)!(length l)"
      in exI)
    apply(rule_tac
      x="drop (Suc(length l)) (S1@SL#S2)"
      in exI)
    apply(rule_tac
      t="take (length l) (S1@SL#S2) @ (S1@SL#S2) ! length l # drop (Suc (length l)) (S1@SL#S2)"
      and s="(S1@SL#S2)"
      in subst)
     apply(rename_tac l l' A w S1 SL S2)(*strict*)
     apply(rule id_take_nth_drop)
     apply(subgoal_tac "length ((S1@SL#S2)) = length (Esplit_signature (S1@SL#S2)) \<or> (length (S1@SL#S2) = Suc(length (Esplit_signature (S1@SL#S2))) \<and> []=[])")
      apply(rename_tac l l' A w S1 SL S2)(*strict*)
      prefer 2
      apply(rule EValidSplit_Esplit_signature_length)
      apply(force)
     apply(rename_tac l l' A w S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    apply(subgoal_tac "length S1=length l")
     apply(rename_tac l l' A w S1 SL S2)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="(S1 @ SL # S2) ! length l"
      and s="SL"
      in ssubst)
      apply(rename_tac l l' A w S1 SL S2)(*strict*)
      apply (metis nth_append_length)
     apply(rename_tac l l' A w S1 SL S2)(*strict*)
     apply(clarsimp)
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    prefer 2
    apply(simp add: Esplit_configurations_def)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(thin_tac "Esplit_signature (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2) = l @ w @ liftB l'")
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(subgoal_tac "length S1 = length (Esplit_signature S1) \<or> (length S1 = Suc(length (Esplit_signature S1)) \<and> SL # S2=[])")
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    prefer 2
    apply(rule EValidSplit_Esplit_signature_length)
    apply(force)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(subgoal_tac "length (S1@[SL]) = length (Esplit_signature (S1@[SL])) \<or> (length (S1@[SL]) = Suc(length (Esplit_signature (S1@[SL]))) \<and> S2=[])")
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    prefer 2
    apply(rule EValidSplit_Esplit_signature_length)
    apply(force)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(thin_tac "EValidSplit G (S1 @ SL # S2)")
   apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G")
   apply(thin_tac "Esplit_TSstructure G")
   apply(erule disjE)
    apply(rename_tac l l' A w S1 SL S2)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac l l' A S1 SL)(*strict*)
    apply(simp add: Esplit_signature_append)
    apply(simp add: Esplit_signature_def option_to_list_def)
    apply(subgoal_tac "l'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
     apply(rename_tac l l' A S1 SL)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac l l' A S1 SL)(*strict*)
    apply(erule disjE)
     apply(rename_tac l l' A S1 SL)(*strict*)
     apply(clarsimp)
    apply(rename_tac l l' A S1 SL)(*strict*)
    apply(clarsimp)
    apply(rename_tac l A S1 SL w' a')(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(rename_tac l l' A S1 SL S2)(*strict*)
   apply(simp add: Esplit_signature_append)
   apply(subgoal_tac "Esplit_signature (SL # S2) = Esplit_signature [SL] @ Esplit_signature S2")
    apply(rename_tac l l' A S1 SL S2)(*strict*)
    prefer 2
    apply(rule_tac
      t="SL#S2"
      and s="[SL]@S2"
      in ssubst)
     apply(rename_tac l l' A S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac l l' A S1 SL S2)(*strict*)
    apply(rule Esplit_signature_append)
   apply(rename_tac l l' A S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(thin_tac "Esplit_signature (SL # S2) = Esplit_signature [SL] @ Esplit_signature S2")
   apply(subgoal_tac "Esplit_signature [SL] = [teA A]")
    apply(rename_tac l l' A S1 SL S2)(*strict*)
    prefer 2
    apply(simp (no_asm) add: Esplit_signature_def option_to_list_def)
    apply(force)
   apply(rename_tac l l' A S1 SL S2)(*strict*)
   apply(subgoal_tac "Esplit_signature S1 @ [teA A] @ Esplit_signature S2 = l @ teA A # liftB l'")
    apply(rename_tac l l' A S1 SL S2)(*strict*)
    prefer 2
    apply(rule_tac
      t="Esplit_signature S1 @ [teA A] @ Esplit_signature S2"
      and s="Esplit_signature S1 @ Esplit_signature [SL] @ Esplit_signature S2"
      in ssubst)
     apply(rename_tac l l' A S1 SL S2)(*strict*)
     apply (metis)
    apply(rename_tac l l' A S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac l l' A S1 SL S2)(*strict*)
   apply(thin_tac "Esplit_signature S1 @ Esplit_signature [SL] @ Esplit_signature S2 = l @ teA A # liftB l'")
   apply(rename_tac l l' A S1 SL S2)(*strict*)
   apply(thin_tac "Esplit_signature [SL] = [teA A]")
   apply(thin_tac "Suc 0 = length (Esplit_signature [SL])")
   apply(thin_tac "ESplitItem_elem SL = Some (teA A)")
   apply(clarsimp)
   apply(rename_tac l l' A S1 S2)(*strict*)
   apply (metis setA_liftB append_Cons append_Nil equal_simp_triv)
  apply(rename_tac l l' A w)(*strict*)
  apply(subgoal_tac "length S = length (Esplit_signature S) \<or> (length S = Suc(length (Esplit_signature S)) \<and> []=[])")
   apply(rename_tac l l' A w)(*strict*)
   prefer 2
   apply(rule EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac l l' A w)(*strict*)
  apply(rule_tac
      x="take (length l) S"
      in exI)
  apply(rule_tac
      x="S!(length l)"
      in exI)
  apply(rule_tac
      x="drop (Suc(length l)) S"
      in exI)
  apply(rule_tac
      t="take (length l) S @ S ! length l # drop (Suc (length l)) S"
      and s="S"
      in subst)
   apply(rename_tac l l' A w)(*strict*)
   apply(rule id_take_nth_drop)
   apply(force)
  apply(rename_tac l l' A w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="min (length S) (length l)"
      and s="length l"
      in ssubst)
   apply(rename_tac l l' A w)(*strict*)
   apply(force)
  apply(rename_tac l l' A w)(*strict*)
  apply(subgoal_tac "\<exists>S1 SL S2. length S1 = length l \<and> S1@[SL]@S2 = S")
   apply(rename_tac l l' A w)(*strict*)
   prefer 2
   apply(rule_tac
      x="take (length l) S"
      in exI)
   apply(rule_tac
      x="S!((length l))"
      in exI)
   apply(rule_tac
      x="drop (Suc(length l)) S"
      in exI)
   apply(rule conjI)
    apply(rename_tac l l' A w)(*strict*)
    apply(force)
   apply(rename_tac l l' A w)(*strict*)
   apply(rule sym)
   apply(clarsimp)
   apply(rule id_take_nth_drop)
   apply(force)
  apply(rename_tac l l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac l l' A w S1 SL S2)(*strict*)
  apply(rule_tac
      t="(S1 @ SL # S2) ! length l"
      and s="SL"
      in ssubst)
   apply(rule_tac
      t="(S1 @ SL # S2) ! length l"
      in ssubst)
    apply(rule lists_rest.nth_append_2_prime_prime)
    apply(force)
   apply(force)
  apply(rename_tac l l' A w S1 SL S2)(*strict*)
  apply(simp add: Esplit_signature_append)
  apply(subgoal_tac "length S1 = length (Esplit_signature S1) \<or> (length S1 = Suc(length (Esplit_signature S1)) \<and> (SL#S2)=[])")
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(rule EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac l l' A w S1 SL S2)(*strict*)
  apply(erule_tac
      P="length S1 = length (Esplit_signature S1)"
      in disjE)
   apply(rename_tac l l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac l l' A w S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(subgoal_tac "length (S1@[SL]) = length (Esplit_signature (S1@[SL])) \<or> (length (S1@[SL]) = Suc(length (Esplit_signature (S1@[SL]))) \<and> S2=[])")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(rule EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(erule_tac
      P="length (S1 @ [SL]) = length (Esplit_signature (S1 @ [SL]))"
      in disjE)
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac l' A w S1 SL)(*strict*)
   apply(simp add: nth_opt_def)
   apply(subgoal_tac "option_to_list (ESplitItem_elem SL) = [teA A]")
    apply(rename_tac l' A w S1 SL)(*strict*)
    prefer 2
    apply(simp add: Esplit_signature_def)
   apply(rename_tac l' A w S1 SL)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "False")
    apply(rename_tac l' A w S1 SL)(*strict*)
    apply(clarsimp)
   apply(rename_tac l' A w S1 SL)(*strict*)
   apply(simp add: Esplit_signature_def)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(simp add: Esplit_signature_append)
  apply(subgoal_tac "Esplit_signature (SL # S2) = Esplit_signature [SL] @ Esplit_signature S2")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(rule_tac
      t="SL#S2"
      and s="[SL]@S2"
      in ssubst)
    apply(rename_tac l' A w S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   apply(simp only: Esplit_signature_append)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Esplit_signature [SL] = [teA A]")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(case_tac "Esplit_signature [SL]")
    apply(rename_tac l' A w S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac l' A w S1 SL S2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(thin_tac "Esplit_signature (SL # S2) = teA A # liftB l'")
  apply(subgoal_tac "option_to_list (ESplitItem_elem SL) = [teA A]")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_elem SL")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(rule conjI)
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(rule setA_liftB)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(subgoal_tac "LR1ProdForm G")
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_TSstructure_def F2LR1input_def F2LR1inputx_def)
   apply(clarsimp)
   apply(rename_tac l' A w S1 SL S2 Ga)(*strict*)
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(force)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(simp add: LR1ProdForm_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      in ballE)
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(erule_tac
      P="prod_rhs \<lparr>prod_lhs = A, prod_rhs = w\<rparr> = []"
      in disjE)
   apply(rename_tac l' A w S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' A S1 SL S2)(*strict*)
   apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
   apply(case_tac S2)
    apply(rename_tac l' A S1 SL S2)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' A S1 SL)(*strict*)
    apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply(rename_tac l' A S1 SL S2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' A S1 SL a list)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply (metis List.map.compositionality option_to_list_def foldl_first)
  apply(rename_tac l' A w S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
  apply(subgoal_tac "nat_seq 0 0=[0]")
   apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
  apply(erule_tac
      P="A = cons_l2 q1 A1 \<and> w = [teB b, teA (cons_l2   q2 A1)]"
      in disjE)
   apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL S2 b q1 q2 A1)(*strict*)
   apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
   apply(case_tac S2)
    apply(rename_tac l' S1 SL S2 b q1 q2 A1)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' S1 SL b q1 q2 A1)(*strict*)
    apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply(rename_tac l' S1 SL S2 b q1 q2 A1 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL b q1 q2 A1 a list)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply (metis List.map.compositionality option_to_list_def foldl_first)
  apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
  apply(erule_tac
      P="A = cons_l3 q1 A1 q2 \<and> w = [teB b, teA (cons_l3   q3 A1 q2)]"
      in disjE)
   apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL S2 b q1 q2 q3 A1)(*strict*)
   apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
   apply(case_tac S2)
    apply(rename_tac l' S1 SL S2 b q1 q2 q3 A1)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' S1 SL b q1 q2 q3 A1)(*strict*)
    apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply(rename_tac l' S1 SL S2 b q1 q2 q3 A1 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL b q1 q2 q3 A1 a list)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply (metis List.map.compositionality option_to_list_def foldl_first)
  apply(rename_tac l' A w S1 SL S2 b q1 q2 q3 q4 A1)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' A w S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
  apply(erule_tac
      P="A = cons_l2 q1 A1 \<and> w = [teA (cons_l2   q2 A2)]"
      in disjE)
   apply(rename_tac l' A w S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL S2 q1 q2 A1 A2)(*strict*)
   apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
   apply(case_tac S2)
    apply(rename_tac l' S1 SL S2 q1 q2 A1 A2)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' S1 SL q1 q2 A1 A2)(*strict*)
    apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply(rename_tac l' S1 SL S2 q1 q2 A1 A2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL q1 q2 A1 A2 a list)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply (metis List.map.compositionality option_to_list_def foldl_first)
  apply(rename_tac l' A w S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
  apply(erule_tac
      P="A = cons_l2 q1 A1 \<and> w = [teA (cons_l3   q2 A2 q3), teA (cons_l2   q3 A1)]"
      in disjE)
   apply(rename_tac l' A w S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL S2 q1 q2 q3 A1 A2)(*strict*)
   apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
   apply(case_tac S2)
    apply(rename_tac l' S1 SL S2 q1 q2 q3 A1 A2)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' S1 SL q1 q2 q3 A1 A2)(*strict*)
    apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply(rename_tac l' S1 SL S2 q1 q2 q3 A1 A2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL q1 q2 q3 A1 A2 a list)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
   apply (metis List.map.compositionality option_to_list_def foldl_first)
  apply(rename_tac l' A w S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
  apply(simp add: Xstep_mergeL_def Xstep_gen_def nth_opt_def)
  apply(case_tac S2)
   apply(rename_tac l' S1 SL S2 q1 q2 q3 q4 A1 A2)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' S1 SL q1 q2 q3 q4 A1 A2)(*strict*)
   apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
  apply(rename_tac l' S1 SL S2 q1 q2 q3 q4 A1 A2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' S1 SL q1 q2 q3 q4 A1 A2 a list)(*strict*)
  apply(simp add: Xstep_elem_def Xstep_merge1_toWasEliminated_def Esplit_signature_def option_to_list_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_mergeL_def Xstep_gen_def nth_opt_def Xstep_merge1_def)
  apply (metis List.map.compositionality option_to_list_def foldl_first)
  done

theorem cfgRM_derivation_to_Esplit_derivation: "
  Esplit_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n = Some (pair e \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> \<exists>d2 S. Esplit.derivation_initial G d2 \<and> d2 n = Some (pair e S) \<and> Esplit_signature S = w \<and> get_labels d2 n = get_labels d1 n"
  apply(induct n arbitrary: e w)
   apply(rename_tac e w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 [\<lparr>ESplitItem_elim=[], ESplitItem_from=Some(cfg_initial G), ESplitItem_ignore=[], ESplitItem_elim_prods=[], ESplitItem_prods=[], ESplitItem_elem=Some(teA (cfg_initial G)), ESplitItem_to=[]\<rparr>]"
      in exI)
   apply(rule conjI)
    apply(rename_tac e w)(*strict*)
    apply(rule Esplit.derivation_initialI)
     apply(rename_tac e w)(*strict*)
     apply(rule Esplit.der1_is_derivation)
    apply(rename_tac e w)(*strict*)
    apply(clarsimp)
    apply(rename_tac e w c)(*strict*)
    apply(simp add: der1_def)
    apply(simp add: Esplit_initial_configurations_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac e w)(*strict*)
   apply(rule_tac
      x="[\<lparr>ESplitItem_elim=[], ESplitItem_from=Some(cfg_initial G), ESplitItem_ignore=[], ESplitItem_elim_prods=[], ESplitItem_prods=[], ESplitItem_elem=Some(teA (cfg_initial G)), ESplitItem_to=[]\<rparr>]"
      in exI)
   apply(rule conjI)
    apply(rename_tac e w)(*strict*)
    apply(simp add: der1_def)
    apply(simp add: cfgRM.derivation_initial_def)
   apply(rename_tac e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac e w)(*strict*)
    apply(simp add: Esplit_signature_def cfg_initial_configurations_def)
    apply(simp add: option_to_list_def)
    apply(simp add: cfgRM.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(simp add: Esplit_signature_def cfg_initial_configurations_def)
   apply(rename_tac e w)(*strict*)
   apply(simp add: get_labels_def der1_def get_labels_def)
   apply(clarsimp)
   apply(rename_tac e w x)(*strict*)
   apply(subgoal_tac "Suc 0\<le>x \<and> x\<le>0")
    apply(rename_tac e w x)(*strict*)
    apply(force)
   apply(rename_tac e w x)(*strict*)
   apply (metis le_0_eq less_le_not_le nat_seq_in_interval zero_less_Suc)
  apply(rename_tac n e w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac n e w)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n e w)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e w)(*strict*)
    apply(force)
   apply(rename_tac n e w)(*strict*)
   apply(force)
  apply(rename_tac n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w e1 e2 c1)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n e1 e2 c1 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n e1 e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n e1 l r A w)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="l @ teA A # r"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n e1 l r A w d2 S)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = r")
   apply(rename_tac n e1 l r A w d2 S)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n e1 l r A w d2 S)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 l A w d2 S l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(rename_tac r)
  apply(rename_tac n e1 l A w d2 S r)(*strict*)
  apply(subgoal_tac "\<exists>S'. EValidSplit G S' \<and> Esplit_signature S' = l @ w @ liftB r \<and> Esplit_step_relation G S \<lparr>prod_lhs = A, prod_rhs = w\<rparr> S'")
   apply(rename_tac n e1 l A w d2 S r)(*strict*)
   prefer 2
   apply(rule ESplit_cfgRM_step_can_be_simulated)
      apply(rename_tac n e1 l A w d2 S r)(*strict*)
      apply(force)
     apply(rename_tac n e1 l A w d2 S r)(*strict*)
     apply(rule_tac
      t="EValidSplit G S"
      and s="S \<in> Esplit_configurations G"
      in ssubst)
      apply(rename_tac n e1 l A w d2 S r)(*strict*)
      apply(simp add: Esplit_configurations_def)
     apply(rename_tac n e1 l A w d2 S r)(*strict*)
     apply(rule Esplit.belongs_configurations)
      apply(rename_tac n e1 l A w d2 S r)(*strict*)
      apply(rule Esplit.derivation_initial_belongs)
       apply(rename_tac n e1 l A w d2 S r)(*strict*)
       apply(force)
      apply(rename_tac n e1 l A w d2 S r)(*strict*)
      apply(force)
     apply(rename_tac n e1 l A w d2 S r)(*strict*)
     apply(force)
    apply(rename_tac n e1 l A w d2 S r)(*strict*)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule_tac
      x="l"
      in exI)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(rename_tac n e1 l A w d2 S r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(rule_tac
      x="derivation_append d2 (der2 S \<lparr>prod_lhs = A, prod_rhs = w\<rparr> S') n"
      in exI)
  apply(rule conjI)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(rule Esplit.derivation_append_preserves_derivation_initial)
     apply(rename_tac n e1 l A w d2 S r S')(*strict*)
     apply(force)
    apply(rename_tac n e1 l A w d2 S r S')(*strict*)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(rule Esplit.derivation_append_preserves_derivation)
     apply(rename_tac n e1 l A w d2 S r S')(*strict*)
     apply(simp add: Esplit.derivation_initial_def)
    apply(rename_tac n e1 l A w d2 S r S')(*strict*)
    apply(rule Esplit.der2_is_derivation)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(rule_tac
      x="S'"
      in exI)
  apply(rule conjI)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Suc n"
      and s="n+Suc 0"
      in ssubst)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(force)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append d2 (der2 S \<lparr>prod_lhs = A, prod_rhs = w\<rparr> S') n) (n + Suc 0)"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(rule Esplit.get_labels_concat2)
       apply(rename_tac n e1 l A w d2 S r S')(*strict*)
       apply(force)
      apply(rename_tac n e1 l A w d2 S r S')(*strict*)
      apply(simp add: Esplit.derivation_initial_def)
     apply(rename_tac n e1 l A w d2 S r S')(*strict*)
     apply(rule Esplit.der2_is_derivation)
     apply(force)
    apply(rename_tac n e1 l A w d2 S r S')(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def der2_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc 0)=[Suc 0]")
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - Suc 0" for SSn)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSn + 1 - Suc 0" for SSn)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac n e1 l A w d2 S r S')(*strict*)
  apply(simp add: get_labels_def)
  apply(rule listEqI)
   apply(rename_tac n e1 l A w d2 S r S')(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   apply(force)
  apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
     apply(force)
    apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   apply(clarsimp)
   apply(fold get_label_def)
   apply(rule_tac
      t="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n) @ [Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>]) ! i"
      and s="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n) ) ! i"
      in ssubst)
    apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
  apply(rule_tac
      t="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n) @ [Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>]) ! i"
      and s="([Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>]) ! (i-length(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n)))"
      in ssubst)
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "i=n")
   apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n e1 l A w d2 S r S' i)(*strict*)
  apply(clarsimp)
  done

lemma Esplit_signature_length_max: "
  length (Esplit_signature S) \<le> length S"
  apply(induct S)
   apply(simp add: Esplit_signature_def)
  apply(rename_tac a S)(*strict*)
  apply(clarsimp)
  apply(simp add: Esplit_signature_def)
  apply(rule_tac
      t="foldl (@) (option_to_list (ESplitItem_elem a)) (map (option_to_list \<circ> ESplitItem_elem) S)"
      and s="x" for x
      in ssubst)
   apply(rename_tac a S)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a S)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_elem a")
   apply(rename_tac a S)(*strict*)
   apply(clarsimp)
  apply(rename_tac a S aa)(*strict*)
  apply(clarsimp)
  done

lemma Esplit_signature_notwhere_None: "
  length S = length (Esplit_signature S)
  \<Longrightarrow> i<length S
  \<Longrightarrow> ESplitItem_elem (S ! i) \<noteq> None"
  apply(induct S arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a S i)(*strict*)
  apply(subgoal_tac "length (Esplit_signature S) \<le> length S")
   apply(rename_tac a S i)(*strict*)
   prefer 2
   apply(rule Esplit_signature_length_max)
  apply(rename_tac a S i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac a S i)(*strict*)
   apply(clarsimp)
   apply(rename_tac a S)(*strict*)
   apply(case_tac "ESplitItem_elem a")
    apply(rename_tac a S)(*strict*)
    apply(clarsimp)
    apply(simp add: Esplit_signature_def option_to_list_def)
   apply(rename_tac a S aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a S i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a S nat)(*strict*)
  apply(case_tac "ESplitItem_elem a")
   apply(rename_tac a S nat)(*strict*)
   apply(simp add: Esplit_signature_def option_to_list_def)
  apply(rename_tac a S nat aa)(*strict*)
  apply(simp add: Esplit_signature_def option_to_list_def)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a S nat aa)(*strict*)
   apply(subgoal_tac "length (foldl (@) [aa] (map (option_to_list \<circ> ESplitItem_elem) S))= Suc(length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S))) ")
    apply(rename_tac a S nat aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a S nat aa)(*strict*)
   apply (metis ConsApp foldl_append_initial_pullout length_Suc length_rev map_map rev.simps(2))
  apply(rename_tac a S nat aa)(*strict*)
  apply(force)
  done

lemma Esplit_signature_take_eq: "
  length S = length v
  \<Longrightarrow> v = Esplit_signature S
  \<Longrightarrow> n \<le> length v
  \<Longrightarrow> Esplit_signature (take n S) = take n v"
  apply(induct n)
   apply(clarsimp)
   apply(simp add: Esplit_signature_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(simp add: Esplit_signature_def)
  apply(rule_tac
      t="S"
      and s="take n S @ S!n # (drop (Suc n) S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis ConsApp Esplit_signature_def Nat.lessI nth_take_drop_split xt1(8))
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="min (length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S))) n"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="foldl (@) (foldl (@) [] (map (\<lambda>a. option_to_list (ESplitItem_elem a)) (take n S)) @ option_to_list (ESplitItem_elem (S ! n))) (map (\<lambda>a. option_to_list (ESplitItem_elem a)) (drop (Suc n) S))"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="min (Suc n) n"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "ESplitItem_elem (S ! n) \<noteq> None")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule Esplit_signature_notwhere_None)
    apply(rename_tac n)(*strict*)
    apply(simp add: Esplit_signature_def)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      t="foldl (@) [] (map (\<lambda>a. case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) (take n S))"
      and s="take n (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S))"
      in subst)
   apply(rename_tac n y)(*strict*)
   apply(rule_tac
      t="(\<lambda>a. case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A])"
      and s="option_to_list \<circ> ESplitItem_elem"
      in subst)
    apply(rename_tac n y)(*strict*)
    apply(rule ext)
    apply(rename_tac n y a)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem a")
     apply(rename_tac n y a)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
    apply(rename_tac n y a aa)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rename_tac n y)(*strict*)
   apply(rule sym)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="min (Suc n) n"
      and s="n"
      in ssubst)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(force)
  done

lemma Esplit_signature_take_eq_prime: "
  EValidSplit G S
  \<Longrightarrow> n\<le>length (Esplit_signature S)
  \<Longrightarrow> Esplit_signature (take n S) = take n (Esplit_signature S)"
  apply(case_tac "length S=length (Esplit_signature S)")
   apply (metis Esplit_signature_take_eq kPrefix_def)
  apply(subgoal_tac "length (Esplit_signature SSS) \<le> length SSS" for SSS)
   prefer 2
   apply(rule_tac
      S="S"
      in Esplit_signature_length_max)
  apply(rule_tac
      xs="S"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (Esplit_signature (ys @ [y])) < Suc (length (Esplit_signature ys))")
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Esplit_signature (ys @ [y])=SSX" for SSX)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule Esplit_signature_append)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply (metis Esplit_signature_take_eq kPrefix_def )
  done

lemma Esplit_signature_take_prefix_closureise: "
  length S = length v
  \<Longrightarrow> v = Esplit_signature S
  \<Longrightarrow> n < length v
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (v ! n)"
  apply(subgoal_tac "Esplit_signature (take n S) = take n v")
   prefer 2
   apply(rule Esplit_signature_take_eq)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "Esplit_signature (take (Suc n) S) = take (Suc n) v")
   prefer 2
   apply(rule Esplit_signature_take_eq)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "ESplitItem_elem (S ! n) \<noteq> None")
   prefer 2
   apply(rule Esplit_signature_notwhere_None)
    apply(simp add: Esplit_signature_def)
   apply(force)
  apply(subgoal_tac "take (Suc n) v = take n v @ [v!n]")
   prefer 2
   apply (metis take_n_vs_take_Suc_n)
  apply(subgoal_tac "take (Suc n) S = take n S @ [S!n]")
   prefer 2
   apply (metis take_n_vs_take_Suc_n)
  apply(simp add: Esplit_signature_append)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "[y] = [Esplit_signature S ! n]")
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t="[Esplit_signature S ! n]"
      and s="Esplit_signature [S ! n]"
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(simp (no_asm) add: Esplit_signature_def)
  apply(rule_tac
      t="ESplitItem_elem (S ! n)"
      and s="Some y"
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma Esplit_signature_take_prefix_closureise2: "
  length (Esplit_signature w) = length w
  \<Longrightarrow> n<length w
  \<Longrightarrow> ESplitItem_elem (w!n) = Some ((Esplit_signature w)!n)"
  apply(rule_tac
      t="ESplitItem_elem (w!n)"
      in ssubst)
   apply(rule Esplit_signature_take_prefix_closureise)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Esplit_signature_distrib_drop: "
  length (Esplit_signature w) = length w
  \<Longrightarrow> Esplit_signature (drop n w) = drop n (Esplit_signature w)"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac a w nat)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(case_tac "ESplitItem_elem a")
    apply(rename_tac a w nat)(*strict*)
    apply (metis Esplit_signature_notwhere_None length_Suc_conv nth_Cons_0 zero_less_Suc)
   apply(rename_tac a w nat aa)(*strict*)
   apply(thin_tac "Esplit_signature (drop nat w) = drop nat (Esplit_signature w)")
   apply(thin_tac "length (Esplit_signature (a # w)) = Suc (length w)")
   apply(simp add: Esplit_signature_def)
   apply(rule_tac
      t="foldl (@) (option_to_list (Some aa)) (map (option_to_list \<circ> ESplitItem_elem) w)"
      in ssubst)
    apply(rename_tac a w nat aa)(*strict*)
    apply(rule foldl_first)
   apply(rename_tac a w nat aa)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      t="option_to_list \<circ> ESplitItem_elem"
      and s="(\<lambda>a. case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A])"
      in ssubst)
    apply(rename_tac a w nat aa)(*strict*)
    apply(rule ext)
    apply(rename_tac a w nat aa ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa ab)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac a w nat aa)(*strict*)
   apply(force)
  apply(rename_tac a w nat)(*strict*)
  apply(subgoal_tac "ESplitItem_elem ((a#w)!0) = Some ((Esplit_signature SSw)!0)" for SSw)
   apply(rename_tac a w nat)(*strict*)
   prefer 2
   apply(rule Esplit_signature_take_prefix_closureise2)
    apply(rename_tac a w nat)(*strict*)
    apply(force)
   apply(rename_tac a w nat)(*strict*)
   apply(force)
  apply(rename_tac a w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(subgoal_tac "length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) (a # w))) = Suc(length (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) w)))")
   apply(rename_tac a w)(*strict*)
   apply(simp only: Esplit_signature_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) (option_to_list (Some (Esplit_signature (a # w) ! 0))) (map (option_to_list \<circ> ESplitItem_elem) w)"
      in ssubst)
   apply(rename_tac a w)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w)(*strict*)
  apply(subgoal_tac "length (option_to_list (Some (Esplit_signature (a # w) ! 0))) = Suc 0")
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="\<lambda>a. option_to_list (ESplitItem_elem a)"
      and s="option_to_list \<circ> ESplitItem_elem"
      in ssubst)
    apply(rename_tac a w)(*strict*)
    apply(rule ext)
    apply(rename_tac a w aa)(*strict*)
    apply(force)
   apply(rename_tac a w)(*strict*)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma Esplit_signature_drop_eq_prime: "
  EValidSplit G S
  \<Longrightarrow> n\<le>length (Esplit_signature S)
  \<Longrightarrow> Esplit_signature (drop n S) = drop n (Esplit_signature S)"
  apply(case_tac "length S=length (Esplit_signature S)")
   apply (metis Esplit_signature_distrib_drop)
  apply(subgoal_tac "length (Esplit_signature SSS) \<le> length SSS" for SSS)
   prefer 2
   apply(rule_tac
      S="S"
      in Esplit_signature_length_max)
  apply(rule_tac
      xs="S"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (Esplit_signature (ys @ [y])) < Suc (length (Esplit_signature ys))")
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Esplit_signature (ys @ [y])=SSX" for SSX)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule Esplit_signature_append)
  apply(rename_tac ys y)(*strict*)
  apply(subgoal_tac "Esplit_signature (drop n ys @ [y]) = SSX" for SSX)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule Esplit_signature_append)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply (metis Esplit_signature_distrib_drop)
  done

lemma EValidSplit_take_prefix: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> Esplit_signature S = v @ teB b # x
  \<Longrightarrow> \<exists>S1 S2. S=S1@S2 \<and>
  Esplit_signature S1 = v @ [teB b]
  \<and> length S1 = Suc(length v)
  \<and> Esplit_signature S2 = x"
  apply(rule_tac
      x="take (Suc(length v)) S"
      in exI)
  apply(rule_tac
      x="drop (Suc(length v)) S"
      in exI)
  apply(rule conjI)
   apply (metis append_take_drop_id)
  apply(subgoal_tac "length (Esplit_signature SSS) \<le> length SSS" for SSS)
   prefer 2
   apply(rule_tac
      S="S"
      in Esplit_signature_length_max)
  apply(rule conjI)
   apply(rule_tac
      t="Esplit_signature (take (Suc (length v)) S)"
      in ssubst)
    apply(rule Esplit_signature_take_eq_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="Esplit_signature (drop (Suc (length v)) S)"
      in ssubst)
   apply(rule Esplit_signature_drop_eq_prime)
    apply(force)
   apply(force)
  apply(force)
  done

lemma EValidSplit_DERIVED_terminal_produce_produces_to: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplitItem_gen G S
  \<Longrightarrow> ESplitItem_from S = Some A
  \<Longrightarrow> ESplitItem_elem S = Some (teB b)
  \<Longrightarrow> ESplitItem_to S = []
  \<Longrightarrow> Q"
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "ESplitItem_prods S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac d)(*strict*)
  apply(erule disjE)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length w') = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d w' a')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d w' a' e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length w')"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d w' a' e)(*strict*)
     apply(force)
    apply(rename_tac d w' a' e)(*strict*)
    apply(force)
   apply(rename_tac d w' a' e)(*strict*)
   apply(force)
  apply(rename_tac d w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "CFGtermLeft G")
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(simp add: CFGtermLeft_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftA (option_to_list (Some A))\<rparr>"
      in allE)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule impE)
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 c1 c2 l r)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac d w' a' e1 e2 c1 c2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac d w' a' e1 e2 c1 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 c1 c2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(simp add: get_configuration_def)
  apply(case_tac c1)
  apply(rename_tac d w' a' e1 e2 c1 c2 r l' cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d w' a' e1 e2 c1 c2 r l' cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 r l')(*strict*)
  apply(erule impE)
   apply(rename_tac d w' a' e1 e2 r l')(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[A]"
      in exI)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 r l' w1 w2)(*strict*)
  apply(subgoal_tac "l'=w1")
   apply(rename_tac d w' a' e1 e2 r l' w1 w2)(*strict*)
   prefer 2
   apply (metis initial_liftB_strings_coincide)
  apply(rename_tac d w' a' e1 e2 r l' w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 r w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac d w' a' e1 e2 r w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 r w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
  apply(erule_tac
      x="length w'"
      in allE)
  apply(clarsimp)
  apply(case_tac w1)
   apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
   prefer 2
   apply(rename_tac d w' a' e1 e2 w1 list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 w1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 list)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 e2 list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac d w' a' e1 e2 list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w' a' e1 e2 list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 list ba Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 e2 list ba Aa B)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 list ba Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 e2 list ba Aa B)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 list ba Aa B)(*strict*)
  apply(clarsimp)
  done

lemma EValidSplit_DERIVED_l3_produce_produces_to: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplitItem_gen G S
  \<Longrightarrow> ESplitItem_from S = Some A
  \<Longrightarrow> ESplitItem_elem S = Some (teA (cons_l3   q1 B q2))
  \<Longrightarrow> ESplitItem_to S = []
  \<Longrightarrow> ESplitItem_prods S \<noteq> []
  \<Longrightarrow> Q"
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "ESplitItem_prods S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac d)(*strict*)
  apply(erule disjE)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length w') = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d w' a')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d w' a' e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length w')"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d w' a' e)(*strict*)
     apply(force)
    apply(rename_tac d w' a' e)(*strict*)
    apply(force)
   apply(rename_tac d w' a' e)(*strict*)
   apply(force)
  apply(rename_tac d w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "LR1ProdForm G")
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(simp add: F2LR1inputx_def)
   apply(force)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2=(w'@[a'])!length w'")
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac d w' a' e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 c1 c2)(*strict*)
  apply(simp add: LR1ProdForm_def)
  apply(erule_tac
      x="a'"
      in ballE)
   apply(rename_tac d w' a' e1 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac d w' a' e1 c1 c2)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 c1 c2)(*strict*)
   apply(simp add: left_degen_def sat_refined_def)
   apply(erule_tac
      x="length w'"
      in allE)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 q4 A1)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 q4 A1)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac d w' a' e1 c1 c2 b q1a q2a A1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a A1 l r)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a A1 l r cfg_confa)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a A1 l r cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 b q1a q2a A1 l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 q4 A1)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 q4 A1)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 A1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a q3 A1 l r)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a q3 A1 l r cfg_confa)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d w' e1 c1 c2 b q1a q2a q3 A1 l r cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 b q1a q2a q3 A1 l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac d w' a' e1 c1 c2 b q1a q2a q3 q4 A1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac d w' a' e1 c1 c2 q1a q2a A1 A2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 c1 c2 q1a q2a A1 A2 l r)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d w' e1 c1 c2 q1a q2a A1 A2 l r cfg_confa)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d w' e1 c1 c2 q1a q2a A1 A2 l r cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 q1a q2a A1 A2 l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(case_tac l)
    apply(rename_tac d w' e1 q1a q2a A1 A2 l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w' e1 q1a q2a A1 A2 l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
  apply(erule disjE)
   apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 A1 A2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 c1 c2 q1a q2a q3 A1 A2 l r)(*strict*)
   apply(case_tac c1)
   apply(rename_tac d w' e1 c1 c2 q1a q2a q3 A1 A2 l r cfg_confa)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d w' e1 c1 c2 q1a q2a q3 A1 A2 l r cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' e1 q1a q2a q3 A1 A2 l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac d w' a' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' e1 c1 c2 q1a q2a q3 q4 A1 A2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w' e1 c1 c2 q1a q2a q3 q4 A1 A2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d w' e1 c1 c2 q1a q2a q3 q4 A1 A2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d w' e1 c1 c2 q1a q2a q3 q4 A1 A2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' e1 q1a q2a q3 q4 A1 A2 l r)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  done

lemma trans_der_list_construct_elimininating_derivation_prime: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S1@S @ S2)
  \<Longrightarrow> length (Esplit_signature S) = length S
  \<Longrightarrow> \<exists>ds \<pi>s fw. cfgLM.trans_der_list G ds
  (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s
  (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)"
  apply(rule trans_der_list_construct_elimininating_derivation)
    apply(simp add: split_TSstructure_def)
   apply(simp add: split_TSstructure_def)
  apply(simp add: Esplit_signature_def cfg_configurations_def)
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule setA_foldl_elem)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(erule_tac
      x="y"
      in ballE)
    apply(rename_tac x y)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem y")
     apply(rename_tac x y)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac x y a)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(case_tac a)
     apply(rename_tac x y a aa)(*strict*)
     prefer 2
     apply(rename_tac x y a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac x y a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule setB_foldl_elem)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="y"
      in ballE)
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_elem y")
    apply(rename_tac x y)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac x y a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac a)
    apply(rename_tac x y a aa)(*strict*)
    prefer 2
    apply(rename_tac x y a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac x y a aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(force)
  done

lemma EValidSplit_construct_derivation: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S @ S')
  \<Longrightarrow> length (Esplit_signature S) = length S
  \<Longrightarrow> n<length S
  \<Longrightarrow> cfgLM.trans_der_list G ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)
  \<Longrightarrow> \<exists>\<pi> d.
  let S = S ! n in
  cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (ESplitItem_elim S @ option_to_list (ESplitItem_from S) @ (ESplitItem_ignore S))\<rparr>"
  apply(induct n)
   apply(clarsimp)
   apply(case_tac S)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac SH ST)
   apply(rename_tac SH ST)(*strict*)
   apply(subgoal_tac "EValidSplit_initial G (SH # ST @ S')")
    apply(rename_tac SH ST)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(rename_tac SH ST)(*strict*)
   apply(simp add: EValidSplit_initial_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac SH ST)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
    apply(simp add: option_to_list_def)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac SH ST)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac SH ST)(*strict*)
    apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac SH ST)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(simp add: option_to_list_def)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac SH ST)(*strict*)
    apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac SH ST)(*strict*)
   apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(simp add: Let_def)
  apply(rule_tac
      t="ESplitItem_elim (S ! Suc n) @ option_to_list (ESplitItem_from (S ! Suc n)) @ ESplitItem_ignore (S ! Suc n)"
      and s="ESplitItem_to ((S @ S') ! n) @ ESplitItem_ignore ((S @ S') ! n)"
      in ssubst)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(subgoal_tac "EValidSplit_interlineX ((S @ S') ! n) ((S @ S') ! Suc n)")
    apply(rename_tac n \<pi> d)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_interline_def)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(simp add: EValidSplit_interlineX_def)
   apply(rule_tac
      t="ESplitItem_to ((S @ S') ! n) @ ESplitItem_ignore ((S @ S') ! n)"
      and s="ESplitItem_elim ((S @ S') ! Suc n) @ option_to_list (ESplitItem_from ((S @ S') ! Suc n)) @ ESplitItem_ignore ((S @ S') ! Suc n)"
      in ssubst)
    apply(rename_tac n \<pi> d)(*strict*)
    apply(force)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(thin_tac "ESplitItem_elim ((S @ S') ! Suc n) @ option_to_list (ESplitItem_from ((S @ S') ! Suc n)) @ ESplitItem_ignore ((S @ S') ! Suc n) = ESplitItem_to ((S @ S') ! n) @ ESplitItem_ignore ((S @ S') ! n)")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(rule_tac
      t="(S@S')!Suc n"
      and s="S!Suc n"
      in ssubst)
    apply(rename_tac n \<pi> d)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(force)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(rule_tac
      t="(S@S')!n"
      and s="S! n"
      in ssubst)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(subgoal_tac "\<exists>\<pi> d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (ESplitItem_elim (S ! n) @ option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr> \<pi> \<lparr>cfg_conf = liftB (fw!n) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))\<rparr>")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(clarsimp)
   apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
   apply(rule_tac
      x="\<pi>@\<pi>'"
      in exI)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?v1.0="foldl (@) [] (take n fw)"
      and ?v4.0="[]"
      and ?d1.0="d"
      and ?d2.0="da"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
     apply(force)
    apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
    apply(force)
   apply(rename_tac n \<pi> d \<pi>' da)(*strict*)
   apply(clarsimp)
   apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(subgoal_tac "liftB (foldl (@) [] (take (Suc n) fw)) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)) = liftB (foldl (@) [] (take n fw)) @ liftB (fw ! n) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))")
    apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
    apply(clarsimp)
   apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="liftB (foldl (@) [] (take n fw)) @ liftB (fw ! n)"
      and s="liftB (foldl (@) [] (take n fw) @ fw ! n)"
      in ssubst)
    apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
   apply(rule_tac
      f="liftB"
      in arg_cong)
   apply(subgoal_tac "n<length fw")
    apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_list_def)
   apply(rename_tac n \<pi> d \<pi>' da db)(*strict*)
   apply(rule sym)
   apply(rule foldl_tail)
   apply(force)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (ESplitItem_elim (S ! n) @ option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr>")
  apply(rename_tac n \<pi> d)(*strict*)
  apply(subgoal_tac "\<exists>\<pi> d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr> \<pi> \<lparr>cfg_conf = liftB (fw ! n) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))\<rparr>")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(thin_tac "cfgLM.trans_der_list G ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (ESplitItem_elim (S ! n))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S!n))) \<lparr>cfg_conf = []\<rparr>")
    apply(rename_tac n \<pi> d)(*strict*)
    prefer 2
    apply(subgoal_tac "EValidSplitItem_elim G (S ! n)")
     apply(rename_tac n \<pi> d)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac n \<pi> d)(*strict*)
    apply(simp add: EValidSplitItem_elim_def)
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftA SSws\<rparr> (foldl (@) [] SSrenPIs) \<lparr>cfg_conf = []\<rparr>" for SSG SSws SSrenPIs)
     apply(rename_tac n)(*strict*)
     prefer 2
     apply(rule elim_map_to_trans_der)
        apply(rename_tac n)(*strict*)
        apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
        apply(force)
       apply(rename_tac n)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac n)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(clarsimp)
   apply(rename_tac n \<pi> d da)(*strict*)
   apply(rule_tac
      x="(foldl (@) [] (ESplitItem_elim_prods (S ! n)))@\<pi>"
      in exI)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1 @ SSw2\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv2\<rparr>" for SSG SSw1 SSw2 SSrenPI10 SSrenPI20 SSv1 SSv2)
    apply(rename_tac n \<pi> d da)(*strict*)
    prefer 2
    apply(rule_tac
      ?v1.0="[]"
      and ?d1.0="d"
      and ?d2.0="da"
      and G="G"
      in cfgLM_trans_der_biextend_prime)
      apply(rename_tac n \<pi> d da)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac n \<pi> d da)(*strict*)
     apply(force)
    apply(rename_tac n \<pi> d da)(*strict*)
    apply(force)
   apply(rename_tac n \<pi> d da)(*strict*)
   apply(clarsimp)
   apply(rename_tac n \<pi> d da db)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(subgoal_tac "\<exists>\<pi> d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr> \<pi> \<lparr>cfg_conf = option_to_list(ESplitItem_elem (S!n)) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))\<rparr>")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(subgoal_tac "\<exists>d \<pi>. cfgLM.trans_der G d \<lparr>cfg_conf = option_to_list(ESplitItem_elem (S ! n))\<rparr> \<pi> \<lparr>cfg_conf = liftB (fw!n)\<rparr>")
    apply(rename_tac n \<pi> d)(*strict*)
    apply(thin_tac "cfgLM.trans_der_list G ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)")
    apply(rename_tac n \<pi> d)(*strict*)
    apply(clarsimp)
    apply(rename_tac n \<pi> d da \<pi>')(*strict*)
    apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
     apply(rename_tac n \<pi> d da \<pi>')(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and ?v1.0="[]"
      and ?v4.0="liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))"
      and ?d1.0="da"
      and ?d2.0="d"
      in cfgLM_trans_der_concat_extend_prime)
       apply(rename_tac n \<pi> d da \<pi>')(*strict*)
       apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
       apply(force)
      apply(rename_tac n \<pi> d da \<pi>')(*strict*)
      apply(force)
     apply(rename_tac n \<pi> d da \<pi>')(*strict*)
     apply(force)
    apply(rename_tac n \<pi> d da \<pi>')(*strict*)
    apply(clarsimp)
    apply(rename_tac n \<pi> d da \<pi>' db)(*strict*)
    apply(rule_tac
      x="(\<pi> @ \<pi>')"
      in exI)
    apply(rule_tac
      x="db"
      in exI)
    apply(simp add: liftA_commutes_over_concat)
   apply(rename_tac n \<pi> d)(*strict*)
   apply(thin_tac "\<exists>\<pi> d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr> \<pi> \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S ! n)) @ liftA (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n))\<rparr>")
   apply(rename_tac n \<pi> d)(*strict*)
   apply(rule_tac
      x="ds!n"
      in exI)
   apply(rule_tac
      x="\<pi>s!n"
      in exI)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(simp add: cfgLM.trans_der_list_def)
   apply(clarsimp)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      t="option_to_list (ESplitItem_elem (S ! n))"
      and s="[Esplit_signature S ! n]"
      in ssubst)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "ESplitItem_elem (S ! n) = Some (SSv ! SSn)" for SSv SSn)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule Esplit_signature_take_prefix_closureise)
      apply(rename_tac n)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(thin_tac "cfgLM.trans_der_list G ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)")
  apply(rename_tac n \<pi> d)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S ! n)")
   apply(rename_tac n \<pi> d)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="S ! n"
      in ballE)
    apply(rename_tac n)(*strict*)
    apply(simp add: EValidSplitItem_def)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n \<pi> d)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac n d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="liftA(ESplitItem_ignore (S ! n))"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac n d)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac n d)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplitItem_belongs G (S ! n)")
     apply(rename_tac n d)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
      x="S ! n"
      in ballE)
      apply(rename_tac n d)(*strict*)
      apply(simp add: EValidSplitItem_def)
     apply(rename_tac n d)(*strict*)
     apply(force)
    apply(rename_tac n d)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
    apply(clarsimp)
    apply(rule_tac
      t="setB (liftA (ESplitItem_ignore (S ! n)))"
      and s="{}"
      in ssubst)
     apply(rename_tac n d)(*strict*)
     apply (metis List.set_simps(1) setB_liftA)
    apply(rename_tac n d)(*strict*)
    apply(rule_tac
      t="setA (liftA (ESplitItem_ignore (S ! n)))"
      and s=" (set (ESplitItem_ignore (S ! n)))"
      in ssubst)
     apply(rename_tac n d)(*strict*)
     apply (metis setA_liftA)
    apply(rename_tac n d)(*strict*)
    apply(force)
   apply(rename_tac n d)(*strict*)
   apply(force)
  apply(rename_tac n d)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d da)(*strict*)
  apply(rule_tac
      x="(ESplitItem_prods (S ! n))"
      in exI)
  apply(rule_tac
      x="da"
      in exI)
  apply(simp add: liftA_commutes_over_concat)
  done

lemma Esplit_signature_belongs_setA: "
  EValidSplit G (S1 @ S1')
  \<Longrightarrow> setA (Esplit_signature S1) \<subseteq> cfg_nonterminals G"
  apply(simp add: Esplit_signature_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule setA_foldl_elem)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(thin_tac "x \<in> setA (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S1))")
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_elem y")
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac x y a aa)(*strict*)
   prefer 2
   apply(rename_tac x y a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y aa)(*strict*)
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="y"
      in ballE)
   apply(rename_tac y aa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y aa)(*strict*)
  apply(simp add: EValidSplitItem_def EValidSplitItem_belongs_def option_to_list_def)
  done

lemma Esplit_signature_belongs_setB: "
  EValidSplit G (S1 @ S1')
  \<Longrightarrow> setB (Esplit_signature S1) \<subseteq> cfg_events G"
  apply(simp add: Esplit_signature_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule setB_foldl_elem)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(thin_tac "x \<in> setB (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S1))")
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_elem y")
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac x y a aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y b)(*strict*)
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="y"
      in ballE)
   apply(rename_tac y b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y b)(*strict*)
  apply(simp add: EValidSplitItem_def EValidSplitItem_belongs_def option_to_list_def)
  done

lemma e_derivation_at_tail_exists: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> ESplitItem_elem ((S1@S1') ! (length v)) = Some (teB b)
  \<Longrightarrow> i\<le>length v
  \<Longrightarrow> Si = (S1@S1') ! i
  \<Longrightarrow> Sn = (S1@S1') ! n
  \<Longrightarrow> n=length v
  \<Longrightarrow> e_from_i = option_to_list(ESplitItem_from Si)
  \<Longrightarrow> e_ignore_i = ESplitItem_ignore Si
  \<Longrightarrow> e_prods_i = ESplitItem_prods Si
  \<Longrightarrow> e_to_n = ESplitItem_to Sn
  \<Longrightarrow> e_ignore_n = ESplitItem_ignore Sn
  \<Longrightarrow> e_\<pi> = (e_prods_i @ \<pi>s!i) @ (foldl (@) [] (map (\<lambda>x.
  foldl (@) [] (ESplitItem_elim_prods ((S1@S1') ! x))
  @ ESplitItem_prods ((S1@S1') ! x)
  @ \<pi>s!x) (nat_seq (Suc i) n)))
  \<Longrightarrow> \<alpha> = foldl (@) [] (drop i (take n fw))
  \<Longrightarrow> \<exists>e_d. cfgLMMP G e_d (liftA(e_from_i@e_ignore_i)) e_\<pi> (liftB (\<alpha>@[b])) (liftA(e_to_n@e_ignore_n))"
  apply(clarsimp)
  apply(subgoal_tac "length (Esplit_signature S1) = length S1")
   prefer 2
   apply(metis)
  apply(simp add: Let_def)
  apply(subgoal_tac "length S1 = Suc(length v)")
   prefer 2
   apply (metis length_Suc)
  apply(clarsimp)
  apply(subgoal_tac "length(nat_seq 0 (length v)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length v) ! (length v) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(induct "(length v)-i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_from ((S1 @ S1') ! length v)")
    apply(subgoal_tac "False")
     apply(force)
    apply(simp add: EValidSplit_def EValidSplit_producing_def)
    apply(clarsimp)
    apply(erule_tac
      x="(S1@S1')!length v"
      in ballE)
     apply(clarsimp)
    apply(subgoal_tac "(S1 @ S1') ! length v \<in> set (butlast (S1 @ S1'))")
     apply(force)
    apply(thin_tac "(S1 @ S1') ! length v \<notin> set (butlast (S1 @ S1'))")
    apply(subgoal_tac "S1'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
     apply(simp add: EValidSplit_final_def)
     apply(clarsimp)
     apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      prefer 2
      apply(rule case_list)
     apply(erule disjE)
      apply(clarsimp)
     apply(clarsimp)
     apply(rename_tac w' a')(*strict*)
     apply(simp add: EValidSplit_produce_or_elim_def)
     apply(clarsimp)
     apply(subgoal_tac "(w' @ [a']) ! length v = a'")
      apply(rename_tac w' a')(*strict*)
      prefer 2
      apply (metis nth_append_length)
     apply(rename_tac w' a')(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def EValidSplitItem_gen_def)
     apply(clarsimp)
     apply(rename_tac w' a' d)(*strict*)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
      apply(rename_tac w' a' d)(*strict*)
      prefer 2
      apply(rule_tac cfgLM_trans_der_from_empty)
      apply(force)
     apply(rename_tac w' a' d)(*strict*)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(rule_tac
      t="butlast (S1 @ w' @ [a'])"
      in ssubst)
     apply(rename_tac w' a')(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(rule_tac
      t="(S1 @ w' @ [a']) ! length v"
      and s="(S1 @ w') ! length v"
      in ssubst)
     apply(rename_tac w' a')(*strict*)
     apply(rule_tac
      t="S1 @ w' @ [a']"
      and s="(S1 @ w') @ [a']"
      in ssubst)
      apply(rename_tac w' a')(*strict*)
      apply(force)
     apply(rename_tac w' a')(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(rule nth_mem)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "(S1 @ S1') ! length v = S1 ! length v ")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "nat_seq (Suc (length v)) (length v) = []")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply (metis Nat.lessI nat_seqEmpty)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(thin_tac "nat_seq (Suc (length v)) (length v) = []")
   apply(subgoal_tac "\<pi>s!length v=[]")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(simp add: cfgLMTDL_def)
    apply(simp add: cfgLM.trans_der_list_def)
    apply(clarsimp)
    apply(erule_tac
      x="length v"
      in allE)
    apply(erule impE)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac a e)(*strict*)
    apply(subgoal_tac "Esplit_signature S1 ! length v = teB b")
     apply(rename_tac a e)(*strict*)
     apply(clarsimp)
     apply(case_tac "\<pi>s ! length v")
      apply(rename_tac a e)(*strict*)
      apply(clarsimp)
     apply(rename_tac a e aa list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. (ds!length v) 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
      apply(rename_tac a e aa list)(*strict*)
      prefer 2
      apply(rule_tac
      m="length (aa # list)"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac a e aa list)(*strict*)
        apply(force)
       apply(rename_tac a e aa list)(*strict*)
       apply(force)
      apply(rename_tac a e aa list)(*strict*)
      apply(force)
     apply(rename_tac a e aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac a e aa list e2 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac a e aa list e2 c2 l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac a e aa list e2 c2 l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac a e aa list e2 c2 l r ab lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac a e)(*strict*)
    apply (metis nth_append_2_prime_prime nth_first)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      x="S1!length v"
      in ballE)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac a d)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
    apply(rename_tac a d)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="liftA(ESplitItem_ignore (S1 ! (length v)))"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
      apply(rename_tac a d)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac a d)(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
     apply(clarsimp)
     apply(rule_tac
      t="setB (liftA (ESplitItem_ignore (S1 ! length v)))"
      and s="{}"
      in ssubst)
      apply(rename_tac a d)(*strict*)
      apply (metis List.set_simps(1) setB_liftA)
     apply(rename_tac a d)(*strict*)
     apply(rule_tac
      t="setA (liftA (ESplitItem_ignore (S1 ! length v)))"
      and s=" (set (ESplitItem_ignore (S1 ! length v)))"
      in ssubst)
      apply(rename_tac a d)(*strict*)
      apply (metis setA_liftA)
     apply(rename_tac a d)(*strict*)
     apply(force)
    apply(rename_tac a d)(*strict*)
    apply(force)
   apply(rename_tac a d)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(simp add: cfgLMMP_def cfgLMMPX_def)
   apply(rule conjI)
    apply(rename_tac a d da)(*strict*)
    apply(simp add: liftA_commutes_over_concat option_to_list_def)
   apply(rename_tac a d da)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d da \<pi>' db c)(*strict*)
   apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (ESplitItem_ignore (S1 ! length v))\<rparr> (ESplitItem_prods (S1 ! length v)) \<lparr>cfg_conf = option_to_list (Some (teB b)) @ liftA (ESplitItem_to (S1 ! length v)) @ liftA (ESplitItem_ignore (S1 ! length v))\<rparr>")
   apply(rename_tac a d da \<pi>' db c)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(rename_tac a d \<pi>' db c)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d \<pi>' db c ca)(*strict*)
   apply(subgoal_tac "length \<pi>' < length (ESplitItem_prods (S1 ! length v))")
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    prefer 2
    apply(rule_tac
      t="ESplitItem_prods (S1 ! length v)"
      and s="\<pi>' @ ca"
      in ssubst)
     apply(rename_tac a d \<pi>' db c ca)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    apply(subgoal_tac "ca=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac a d \<pi>' db c ca)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    apply(erule disjE)
     apply(rename_tac a d \<pi>' db c ca)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    apply(erule exE)+
    apply(rename_tac a d \<pi>' db c ca w' a')(*strict*)
    apply(rule_tac
      t="ca"
      and s="w'@[a']"
      in ssubst)
     apply(rename_tac a d \<pi>' db c ca w' a')(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca w' a')(*strict*)
    apply(simp (no_asm))
   apply(rename_tac a d \<pi>' db c ca)(*strict*)
   apply(subgoal_tac "\<exists>v1. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a))\<rparr> (\<pi>') \<lparr>cfg_conf = v1\<rparr>")
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
    apply(case_tac "\<exists>v. v1=teB b#v")
     apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
     apply(clarsimp)
     apply(rename_tac a d \<pi>' db c ca va)(*strict*)
     apply(erule_tac
      x="length \<pi>'"
      in allE)
     apply(erule_tac
      P="length \<pi>' < length (ESplitItem_prods (S1 ! length v))"
      in impE)
      apply(rename_tac a d \<pi>' db c ca va)(*strict*)
      prefer 2
      apply(simp add: cfgLM.trans_der_def)
      apply(clarsimp)
      apply(rename_tac a d \<pi>' db c ca va e ea eb)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac a d \<pi>' db c ca va)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
    apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
     apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
     prefer 2
     apply(rule_tac
      ?w2.0="liftA(ESplitItem_ignore (S1 ! length v))"
      and ?v1.0="teB b # c"
      and ?d1.0="db"
      and ?d2.0="d"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
       apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
      prefer 2
      apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a))\<rparr> (ESplitItem_prods (S1 ! length v)) \<lparr>cfg_conf = option_to_list (Some (teB b)) @ liftA (ESplitItem_to (S1 ! length v))\<rparr>")
      apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
      apply(force)
     apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
     apply(simp add: liftA_commutes_over_concat option_to_list_def)
    apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
    apply(clarsimp)
    apply(case_tac v1)
     apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
     prefer 2
     apply(rename_tac a d \<pi>' db c ca v1 aa list)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca v1)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    apply(case_tac "ESplitItem_ignore (S1 ! length v)")
     apply(rename_tac a d \<pi>' db c ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac a d \<pi>' db c ca aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a d \<pi>' db c ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (length \<pi>') = Some (pair e c)")
    apply(rename_tac a d \<pi>' db c ca)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac a d \<pi>' db c ca e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length(ESplitItem_prods (S1 ! length v))"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac a d \<pi>' db c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac a d \<pi>' db c ca e ea)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca e ea)(*strict*)
    apply(force)
   apply(rename_tac a d \<pi>' db c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d \<pi>' db c ca e cb)(*strict*)
   apply(rule_tac
      x="cfg_conf cb"
      in exI)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
   apply(rule_tac
      m="length(ESplitItem_prods (S1 ! length v))-length \<pi>'"
      and v="map Some (drop(length \<pi>')(ESplitItem_prods (S1 ! length v)))"
      in get_labels_drop_tail)
    apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="ESplitItem_prods (S1 ! length v)"
      and s="\<pi>' @ ca"
      in ssubst)
     apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
    apply(rule_tac
      t="drop (length \<pi>') (\<pi>' @ ca)"
      and s="ca"
      in ssubst)
     apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac a d \<pi>' db c ca e cb ea eb)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d)(*strict*)
  apply(case_tac "i=length v")
   apply(rename_tac x i e_d)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "i<length v")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i<length fw")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=(liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i)))\<rparr> ((ESplitItem_prods ((S1 @ S1') ! i)) @ \<pi>s ! i @ (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! (Suc i))))) \<lparr>cfg_conf=liftB ((fw!i))@(liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i)))\<rparr> ")
   apply(rename_tac x i e_d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d d)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac x i e_d d)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and ?v1.0="fw ! i"
      and ?v4.0="[]"
      and ?d1.0="d"
      and ?d2.0="e_d"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac x i e_d d)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac x i e_d d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d d)(*strict*)
    apply(simp add: cfgLMMP_def)
    apply(force)
   apply(rename_tac x i e_d d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d d da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(simp (no_asm) only: cfgLMMP_def)
   apply(rule conjI)
    apply(rename_tac x i e_d d da)(*strict*)
    apply(rule_tac
      t="ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))"
      and s="(ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))))"
      in ssubst)
     apply(rename_tac x i e_d d da)(*strict*)
     prefer 2
     apply(rule_tac
      t="liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b])"
      and s="liftB (fw ! i) @ liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])"
      in ssubst)
      apply(rename_tac x i e_d d da)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(rule_tac
      t="liftB (fw ! i) @ liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])"
      and s="liftB (fw ! i @ foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])"
      in ssubst)
      apply(rename_tac x i e_d d da)(*strict*)
      apply(simp add: liftB_commutes_over_concat)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(rule_tac
      f="liftB"
      in arg_cong)
     apply(clarsimp)
     apply(rule_tac
      t="drop i (take (length v) fw)"
      and s="fw! i#drop (Suc i) (take (length v) fw)"
      in ssubst)
      apply(rename_tac x i e_d d da)(*strict*)
      prefer 2
      apply (metis eq_Nil_appendI foldl_Cons foldl_first)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(rule e_derivation_at_tail_exists_hlp1)
       apply(rename_tac x i e_d d da)(*strict*)
       apply(clarsimp)
      apply(rename_tac x i e_d d da)(*strict*)
      apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
    apply(rename_tac x i e_d d da)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc i) (length v)"
      and s="Suc i#nat_seq (Suc (Suc i)) (length v)"
      in ssubst)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(rule nat_seq_pullout)
     apply(clarsimp)
    apply(rename_tac x i e_d d da)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="foldl (@) (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
      in ssubst)
     apply(rename_tac x i e_d d da)(*strict*)
     apply(rule foldl_first)
    apply(rename_tac x i e_d d da)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d d da)(*strict*)
   apply(simp add: cfgLMMPX_def)
   apply(clarsimp)
   apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
   apply(case_tac "prefix \<pi>' (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))")
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    apply(thin_tac "strict_prefix \<pi>' (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v))))")
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (fw ! i) @ liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) @ liftA (ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v))\<rparr>")
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(thin_tac "cfgLMMP G e_d (liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))) (ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v)))")
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(subgoal_tac "length \<pi>' \<le> length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))")
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     prefer 2
     apply(rule_tac
      t="ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))"
      and s="\<pi>' @ ca"
      in ssubst)
      apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
      apply(force)
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     apply(subgoal_tac "ca=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     apply(erule disjE)
      apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     apply(erule exE)+
     apply(rename_tac x i e_d d da \<pi>' db c ca w' a')(*strict*)
     apply(rule_tac
      t="ca"
      and s="w'@[a']"
      in ssubst)
      apply(rename_tac x i e_d d da \<pi>' db c ca w' a')(*strict*)
      apply(force)
     apply(rename_tac x i e_d d da \<pi>' db c ca w' a')(*strict*)
     apply(simp (no_asm))
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(subgoal_tac "\<exists>v1. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (\<pi>') \<lparr>cfg_conf = v1\<rparr>")
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
     apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
      apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
      prefer 2
      apply(rule_tac
      ?w2.0="[]"
      and ?d1.0="d"
      and ?d2.0="db"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
        apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca v1)(*strict*)
     apply(clarsimp)
     apply(rename_tac x i d \<pi>' db c ca)(*strict*)
     apply(subgoal_tac "prefix (foldl (@) [] (drop i (take (length v) fw)) @ [b]) (fw ! i)")
      apply(rename_tac x i d \<pi>' db c ca)(*strict*)
      apply(simp add: prefix_def)
      apply(clarsimp)
      apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
      apply(subgoal_tac "foldl (@) [] (drop i (take (length v) fw)) @ b # cb \<noteq> fw ! i")
       apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
       apply(force)
      apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
      apply(thin_tac "foldl (@) [] (drop i (take (length v) fw)) @ b # cb = fw ! i")
      apply(rule_tac
      t="drop i (take (length v) fw)"
      and s="fw!i#(drop (Suc i) (take (length v) fw))"
      in ssubst)
       apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
       apply(rule e_derivation_at_tail_exists_hlp1)
         apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
         apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
        apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
        apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
       apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
       apply(force)
      apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
      apply(simp (no_asm))
      apply(rule_tac
      t="foldl (@) (fw!i) (drop (Suc i) (take (length v) fw))"
      in ssubst)
       apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
       apply(rule foldl_first)
      apply(rename_tac x i d \<pi>' db c ca cb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
     apply(clarsimp)
     apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
     apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
      apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      and i="length \<pi>'"
      and j="length(ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))-length \<pi>'"
      in cfgLM.derivation_monotonically_inc)
           apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
           apply(simp add: split_TSstructure_def)
           apply(force)
          apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
          apply(force)
         apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
         apply(force)
        apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
        apply(force)
       apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
       apply(force)
      apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca e ea eb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x i d \<pi>' db c ca e ea eb w)(*strict*)
     apply(simp add: cfg_get_history_def)
     apply(subgoal_tac "maxTermPrefix (liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b]) @ c) = (foldl (@) [] (drop i (take (length v) fw)) @ [b]) @ maxTermPrefix c")
      apply(rename_tac x i d \<pi>' db c ca e ea eb w)(*strict*)
      apply(subgoal_tac "maxTermPrefix (liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))) = fw ! i")
       apply(rename_tac x i d \<pi>' db c ca e ea eb w)(*strict*)
       apply(simp add: prefix_def)
       apply(rule_tac
      x="maxTermPrefix c@w"
      in exI)
       apply(force)
      apply(rename_tac x i d \<pi>' db c ca e ea eb w)(*strict*)
      apply (metis ConsApp maxTermPrefix_pull_out add_Suc_right add_Suc_shift append_Cons append_Nil2 concat_asso diff_diff_cancel diff_le_self le_add_diff_inverse less_imp_le_nat list.inject maxTermPrefix_leading_terminal maxTermPrefix_shift)
     apply(rename_tac x i d \<pi>' db c ca e ea eb w)(*strict*)
     apply (metis Cons_eq_appendI append_Nil concat_asso maxTermPrefix_shift)
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (length \<pi>') = Some (pair e c)")
     apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac x i e_d d da \<pi>' db c ca e ea)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      m="length(ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))"
      in cfgLM.pre_some_position_is_some_position)
       apply(rename_tac x i e_d d da \<pi>' db c ca e ea)(*strict*)
       apply(force)
      apply(rename_tac x i e_d d da \<pi>' db c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac x i e_d d da \<pi>' db c ca e ea)(*strict*)
     apply(force)
    apply(rename_tac x i e_d d da \<pi>' db c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i d \<pi>' db c ca e cb)(*strict*)
    apply(rule_tac
      x="cfg_conf cb"
      in exI)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
    apply(rule_tac
      m="length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))-length \<pi>'"
      and v="map Some (drop(length \<pi>')(ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))))"
      in get_labels_drop_tail)
     apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(rule_tac
      t="length \<pi>' + (length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) - length \<pi>')"
      and s="length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))"
      in ssubst)
      apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(rule_tac
      t="get_labels d (length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))))"
      and s="map Some (ESplitItem_prods ((S1 @ S1') ! i)) @ map Some (\<pi>s ! i) @ map Some (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))"
      in ssubst)
      apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(rule_tac
      t="map Some (ESplitItem_prods ((S1 @ S1') ! i)) @ map Some (\<pi>s ! i) @ map Some (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))"
      and s="map Some (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))"
      in ssubst)
      apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(rule_tac
      t="ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))"
      and s="\<pi>'@ca"
      in ssubst)
      apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac x i d \<pi>' db c ca e cb ea eb)(*strict*)
    apply(force)
   apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
   apply(subgoal_tac "((ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) @ ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) = (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v))))")
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc i) (length v)"
      and s="Suc i#nat_seq (Suc (Suc i)) (length v)"
      in ssubst)
     apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
     apply(rule nat_seq_pullout)
     apply(clarsimp)
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="foldl (@) (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
      in ssubst)
     apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
     apply(rule foldl_first)
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
   apply(subgoal_tac "\<exists>y. SSv@y=SSw \<and> strict_prefix y SSx" for SSw SSv SSx)
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    prefer 2
    apply(rule_tac
      x="ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
      in strict_prefix_prefix_alt)
     apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
   apply(thin_tac "\<not> \<pi>' \<sqsubseteq> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))")
   apply(thin_tac "strict_prefix \<pi>' (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v))))")
   apply(rename_tac x i e_d d da \<pi>' db c)(*strict*)
   apply(clarsimp)
    (*
  e_d:\<pi>2: (from@ignore)(Suc i) \<Longrightarrow> tail@[b]@rest
  d:\<pi>1: (from@ignore)i \<Longrightarrow> front@(from@ignore)(Suc i)
  da:\<pi>1@\<pi>2: (from@ignore)(Suc i) \<Longrightarrow> front tail[b]@rest
  db:\<pi>1@y: (from@ignore)i \<Longrightarrow> front tail[b]@c
#
  db!\<pi>1 = e_d!0
  e_d and (skip db \<pi>1) are similar but the latter is too fast.
*)
   apply(rename_tac x i e_d d da db c y)(*strict*)
   apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) \<lparr>cfg_conf = liftB (fw ! i) @ liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) @ liftA (ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v))\<rparr>")
   apply(rename_tac x i e_d d da db c y)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=(liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i)))\<rparr> y \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) @ c\<rparr>")
    apply(rename_tac x i e_d d da db c y)(*strict*)
    apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))\<rparr>")
    apply(rename_tac x i e_d d da db c y)(*strict*)
    apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ y) \<lparr>cfg_conf = liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b]) @ c\<rparr>")
    apply(rename_tac x i e_d d da db c y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i e_d c y d)(*strict*)
    apply(simp only: cfgLMMP_def cfgLMMPX_def)
    apply(erule conjE)+
    apply(erule_tac
      x="y"
      in allE)
    apply(erule impE)
     apply(rename_tac x i e_d c y d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d c y d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d d da db c y)(*strict*)
   apply(thin_tac "cfgLMMP G e_d (liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))) (ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v)))")
   apply(rename_tac x i e_d d da db c y)(*strict*)
   apply(subgoal_tac "\<exists>e c. db (length (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))) = Some (pair e c)")
    apply(rename_tac x i e_d d da db c y)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac x i e_d d da db c y e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length((ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ y))"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac x i e_d d da db c y e ea)(*strict*)
      apply(force)
     apply(rename_tac x i e_d d da db c y e ea)(*strict*)
     apply(force)
    apply(rename_tac x i e_d d da db c y e ea)(*strict*)
    apply(force)
   apply(rename_tac x i e_d d da db c y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i d db c y e ca)(*strict*)
   apply(case_tac ca)
   apply(rename_tac x i d db c y e ca cfg_conf)(*strict*)
   apply(rename_tac w)
   apply(rename_tac x i d db c y e ca w)(*strict*)
   apply(subgoal_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> ((ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))) \<lparr>cfg_conf = w\<rparr>")
    apply(rename_tac x i d db c y e ca w)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac x i d db c y e w ea eb)(*strict*)
    apply(rule_tac
      m="length y"
      and v="map Some y"
      in get_labels_drop_tail)
     apply(rename_tac x i d db c y e w ea eb)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="get_labels db (length (ESplitItem_prods ((S1 @ S1') ! i)) + (length (\<pi>s ! i) + length (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))) + length y)"
      and s="map Some (ESplitItem_prods ((S1 @ S1') ! i)) @ map Some (\<pi>s ! i) @ map Some (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) @ map Some y"
      in ssubst)
      apply(rename_tac x i d db c y e w ea eb)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x i d db c y e w ea eb)(*strict*)
     apply(rule_tac
      t="length (ESplitItem_prods ((S1 @ S1') ! i)) + (length (\<pi>s ! i) + length (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)))) + length y"
      and s="length (ESplitItem_prods ((S1 @ S1') ! i)) + (length (\<pi>s ! i) + (length (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) + length y))"
      in ssubst)
      apply(rename_tac x i d db c y e w ea eb)(*strict*)
      apply(force)
     apply(rename_tac x i d db c y e w ea eb)(*strict*)
     apply(force)
    apply(rename_tac x i d db c y e w ea eb)(*strict*)
    apply(force)
   apply(rename_tac x i d db c y e ca w)(*strict*)
   apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
    apply(rename_tac x i d db c y e ca w)(*strict*)
    prefer 2
    apply(rule_tac
      \<pi>="ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))"
      and ?w2.0="[]"
      and ?v1.0="SSX"
      and ?d1.0="db"
      and ?d2.0="d" for SSX
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
      apply(rename_tac x i d db c y e ca w)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac x i d db c y e ca w)(*strict*)
     apply(force)
    apply(rename_tac x i d db c y e ca w)(*strict*)
    apply(force)
   apply(rename_tac x i d db c y e ca w)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i d db c y e)(*strict*)
   apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))\<rparr>")
   apply(rename_tac x i d db c y e)(*strict*)
   apply(thin_tac "strict_prefix y (ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))))")
   apply(rename_tac x i d db c y e)(*strict*)
   apply(thin_tac "db (length (ESplitItem_prods ((S1 @ S1') ! i)) + (length (\<pi>s ! i) + length (foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))))) = Some (pair e \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))\<rparr>)")
   apply(rename_tac x i d db c y e)(*strict*)
   apply(subgoal_tac "foldl (@) [] (drop i (take (length v) fw)) = fw ! i@foldl (@) [] (drop (Suc i) (take (length v) fw))")
    apply(rename_tac x i d db c y e)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i db c y)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d SSci SSrenPI20 SScn" for SSG SSci SSrenPI20 SScn)
     apply(rename_tac x i db c y)(*strict*)
     prefer 2
     apply(rule_tac
      ci="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))\<rparr>"
      and ?\<pi>1.0="ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))"
      and d="db"
      in cfgLM_derivation_drop)
       apply(rename_tac x i db c y)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac x i db c y)(*strict*)
      apply(force)
     apply(rename_tac x i db c y)(*strict*)
     apply(force)
    apply(rename_tac x i db c y)(*strict*)
    apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i)) @ y) \<lparr>cfg_conf = liftB (fw ! i @ foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) @ c\<rparr>")
    apply(rename_tac x i db c y)(*strict*)
    apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ ESplitItem_ignore ((S1 @ S1') ! i))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))\<rparr>")
    apply(rename_tac x i db c y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i c y d)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=SSv\<rparr> y \<lparr>cfg_conf=SSw\<rparr>" for SSv SSw)
     apply(rename_tac x i c y d)(*strict*)
     prefer 2
     apply(rule_tac
      v="liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))"
      and \<alpha>="fw ! i"
      and d="d"
      and w="liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) @ c"
      in cfgLM_drop_terminal_prefix)
      apply(rename_tac x i c y d)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac x i c y d)(*strict*)
     apply(simp add: liftB_commutes_over_concat)
    apply(rename_tac x i c y d)(*strict*)
    apply(force)
   apply(rename_tac x i d db c y e)(*strict*)
   apply(rule_tac
      t="drop i (take (length v) fw)"
      and s="fw!i#drop (Suc i) (take (length v) fw)"
      in ssubst)
    apply(rename_tac x i d db c y e)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac x i db c y)(*strict*)
    apply(rule foldl_first)
   apply(rename_tac x i d db c y e)(*strict*)
   apply(rule e_derivation_at_tail_exists_hlp1)
     apply(rename_tac x i d db c y e)(*strict*)
     apply(force)
    apply(rename_tac x i d db c y e)(*strict*)
    apply(force)
   apply(rename_tac x i d db c y e)(*strict*)
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(thin_tac "cfgLMMP G e_d (liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ ESplitItem_ignore ((S1 @ S1') ! Suc i))) (ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v)))")
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "(S1@S1')!i = S1!i")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "(S1@S1')!Suc i = S1!Suc i")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "EValidSplitItem G (S1!i)")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i e_d)(*strict*)
  apply(subgoal_tac "EValidSplitItem G (S1!(Suc i))")
   apply(rename_tac x i e_d)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i e_d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i)(*strict*)
  apply(subgoal_tac "\<exists>da. cfgLM.trans_der G da \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S1 ! i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>")
   apply(rename_tac x i)(*strict*)
   prefer 2
   apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac x i d da)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i da)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S1 ! i)))@(liftA(ESplitItem_ignore (S1 ! i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))@(liftA(ESplitItem_ignore (S1 ! i)))\<rparr>")
   apply(rename_tac x i da)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSw1' SSw2)
    apply(rename_tac x i da)(*strict*)
    prefer 2
    apply(rule_tac
      ?w2.0="liftA(ESplitItem_ignore (S1 ! i))"
      in cfgLM_trans_der_context_prime2)
      apply(rename_tac x i da)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac x i da)(*strict*)
     apply(thin_tac "EValidSplitItem G (S1 ! Suc i)")
     apply(simp add: EValidSplitItem_def EValidSplitItem_belongs_def)
     apply(clarsimp)
     apply(simp add: cfg_configurations_def)
     apply(rule_tac
      t="setA (liftA (ESplitItem_ignore (S1 ! i)))"
      and s="(set (ESplitItem_ignore (S1 ! i)))"
      in ssubst)
      apply(rename_tac x i da)(*strict*)
      apply (metis setA_liftA)
     apply(rename_tac x i da)(*strict*)
     apply(rule_tac
      t="setB (liftA (ESplitItem_ignore (S1 ! i)))"
      and s="{}"
      in ssubst)
      apply(rename_tac x i da)(*strict*)
      apply (metis setB_liftA)
     apply(rename_tac x i da)(*strict*)
     apply(force)
    apply(rename_tac x i da)(*strict*)
    apply(force)
   apply(rename_tac x i da)(*strict*)
   apply(force)
  apply(rename_tac x i da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S1 ! i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>")
  apply(rename_tac x i da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (\<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))\<rparr>")
   apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d da)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
  apply(rename_tac x i d da)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and ?v1.0="[]"
    and ?v4.0="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in cfgLM_trans_der_concat_extend_prime)
    apply(rename_tac x i d da)(*strict*)
    apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac x i d da)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(force)
  apply(rename_tac x i d da)(*strict*)
  apply(force)
  apply(rename_tac x i d da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S1 ! i))) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr>")
  apply(rename_tac x i d da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (\<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))\<rparr>")
  apply(rename_tac x i d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(rule_tac
    x="d"
    in exI)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac x i d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S1 ! i))) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (\<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d da)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac x i d da)(*strict*)
   prefer 2
   apply(rule_tac
    G="G"
    and ?v1.0="[]"
    and ?v4.0="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac x i d da)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac x i d da)(*strict*)
    apply(clarsimp)
    prefer 2
    apply(force)
   apply(rename_tac x i d da)(*strict*)
   apply(force)
  apply(rename_tac x i d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(thin_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr> (\<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i) @ option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
   apply(rename_tac x i d)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_interline_def)
   apply(rename_tac x i)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i d)(*strict*)
   apply(erule_tac
    x="i"
    in allE)
   apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(rule_tac
    x="d"
    in exI)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (ESplitItem_elim (S1 ! Suc i))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = []\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac x i d)(*strict*)
   prefer 2
   apply(rule_tac
    G="G"
    and v="fw ! i"
    and ?w2.0="liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i))"
    and ?d1.0="d"
    in cfgLM_trans_der_context_prime)
     apply(rename_tac x i d)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac x i d)(*strict*)
    apply(subgoal_tac "EValidSplitItem_belongs G (S1 ! (Suc i))")
     apply(rename_tac x i d)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
    x="S1 ! (Suc i)"
    in ballE)
      apply(rename_tac x i d)(*strict*)
      apply(simp add: EValidSplitItem_def)
     apply(rename_tac x i d)(*strict*)
     apply(force)
    apply(rename_tac x i d)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply(simp add: setBConcat)
    apply(rule_tac
    t="setB (liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i)))"
    and s="{}"
    in ssubst)
     apply(rename_tac x i d)(*strict*)
     apply (metis List.set_simps(1) setB_liftA)
    apply(rename_tac x i d)(*strict*)
    apply(rule_tac
    t="setA (liftB (fw ! i))"
    and s="{}"
    in ssubst)
     apply(rename_tac x i d)(*strict*)
     apply (metis List.set_simps(1) setA_liftB)
    apply(rename_tac x i d)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    t="setA (liftA (option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i)))"
    and s="set ((option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i)))"
    in ssubst)
     apply(rename_tac x i d)(*strict*)
     apply (metis setA_liftA)
    apply(rename_tac x i d)(*strict*)
    apply(rule conjI)
     apply(rename_tac x i d)(*strict*)
     apply(clarsimp)
    apply(rename_tac x i d)(*strict*)
    apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
    apply(clarsimp)
    apply(rename_tac x i d xa)(*strict*)
    apply(erule_tac
    x="i"
    in allE)
    apply(clarsimp)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac x i d xa e ea)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB (fw ! i)\<rparr> \<in> cfg_configurations G")
     apply(rename_tac x i d xa e ea)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(clarsimp)
     apply(force)
    apply(rename_tac x i d xa e ea)(*strict*)
    apply(rule_tac
    d="ds!i"
    in cfgLM.belongs_configurations)
     apply(rename_tac x i d xa e ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x i d xa e ea)(*strict*)
    apply(force)
   apply(rename_tac x i d)(*strict*)
   apply(force)
  apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d da)(*strict*)
  apply(rule_tac
    x="da"
    in exI)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac x i d)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="S1 ! (Suc i)"
    in ballE)
  apply(rename_tac x i)(*strict*)
  apply(simp add: EValidSplitItem_def)
  apply(simp add: EValidSplitItem_elim_def)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftA SSws\<rparr> (foldl (@) [] SSrenPIs) \<lparr>cfg_conf = []\<rparr>" for SSG SSws SSrenPIs)
   apply(rename_tac x i)(*strict*)
   prefer 2
   apply(rule elim_map_to_trans_der)
      apply(rename_tac x i)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac x i)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac x i)(*strict*)
    apply(force)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  apply(rename_tac x i d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S1 ! i))\<rparr> (\<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
  apply(rename_tac x i d)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and v="[]"
    and ?w2.0="liftA (ESplitItem_to (S1 ! i)) @ liftA (ESplitItem_ignore (S1 ! i))"
    and ?d1.0="d"
    in cfgLM_trans_der_context_prime)
    apply(rename_tac x i d)(*strict*)
    apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
    apply(force)
   apply(rename_tac x i d)(*strict*)
   apply(subgoal_tac "EValidSplitItem_belongs G (S1 ! i)")
    apply(rename_tac x i d)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(clarsimp)
    apply(erule_tac
    x="S1 ! i"
    in ballE)
     apply(rename_tac x i d)(*strict*)
     apply(simp add: EValidSplitItem_def)
    apply(rename_tac x i d)(*strict*)
    apply(force)
   apply(rename_tac x i d)(*strict*)
   apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
   apply(simp add: setBConcat)
   apply(rule_tac
    t="setA (liftA (ESplitItem_to (S1 ! i)))"
    and s="set ((ESplitItem_to (S1 ! i)))"
    in ssubst)
    apply(rename_tac x i d)(*strict*)
    apply (metis setA_liftA)
   apply(rename_tac x i d)(*strict*)
   apply(rule_tac
    t="setA (liftA (ESplitItem_ignore (S1 ! i)))"
    and s="set ((ESplitItem_ignore (S1 ! i)))"
    in ssubst)
    apply(rename_tac x i d)(*strict*)
    apply (metis setA_liftA)
   apply(rename_tac x i d)(*strict*)
   apply(rule_tac
    t="setB (liftA (ESplitItem_to (S1 ! i)))"
    and s="{}"
    in ssubst)
    apply(rename_tac x i d)(*strict*)
    apply (metis setB_liftA)
   apply(rename_tac x i d)(*strict*)
   apply(rule_tac
    t="setB (liftA (ESplitItem_ignore (S1 ! i)))"
    and s="{}"
    in ssubst)
    apply(rename_tac x i d)(*strict*)
    apply (metis setB_liftA)
   apply(rename_tac x i d)(*strict*)
   apply(force)
  apply(rename_tac x i d)(*strict*)
  apply(force)
  apply(rename_tac x i d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i d)(*strict*)
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="i"
    in allE)
  apply(clarsimp)
  apply(rule_tac
    x="ds!i"
    in exI)
  apply(rule_tac
    t="option_to_list (ESplitItem_elem (S1 ! i))"
    and s="[Esplit_signature S1 ! i]"
    in ssubst)
  apply(rename_tac x i)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
    t="ESplitItem_elem (S1 ! i)"
    and s="Some (SSv ! i)" for SSv
    in ssubst)
  apply(rename_tac x i)(*strict*)
  apply(rule Esplit_signature_take_prefix_closureise)
   apply(rename_tac x i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  apply(rename_tac x i)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma ESplitItem_to_not_empty_on_generating_line: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S @ S')
  \<Longrightarrow> ESplitItem_elem ((S @ S') ! n) = Some (teB b)
  \<Longrightarrow> n<length S
  \<Longrightarrow> ESplitItem_to (S ! n) \<noteq> []"
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(clarsimp)
  apply(erule_tac
      x="S!n"
      in ballE)
   prefer 2
   apply(force)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(subgoal_tac "ESplitItem_elem (S ! n) = Some (teB b)")
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule_tac
      t="S!n"
      and s="(S@S')!n"
      in subst)
    apply(rename_tac d)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs="ESplitItem_prods (S ! n)"
      in rev_cases)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac "ESplitItem_from (S ! n)")
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ys y)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="length ys"
      and kleene_starT="False"
      and END="True"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac d ys y)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac d ys y)(*strict*)
    apply(force)
   apply(rename_tac d ys y)(*strict*)
   apply(force)
  apply(rename_tac d ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e ci)(*strict*)
  apply(erule_tac
      x="length ys"
      in allE)
  apply(clarsimp)
  apply(case_tac ci)
  apply(rename_tac d ys y e ci cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e cfg_confa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac d ys y e cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d ys y e w)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac w)
   apply(rename_tac d ys y e w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ys y e)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac d ys y e w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac d ys y e a list aa)(*strict*)
   prefer 2
   apply(rename_tac d ys y e a list ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ys y e list ba)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d ys y e list ba l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d ys y e list ba l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y e list ba l r a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y e a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e list aa)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac d ys y e list aa)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac d ys y e list aa)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftA (case ESplitItem_from (S ! n) of None \<Rightarrow> [] | Some A \<Rightarrow> [A])\<rparr>"
      in allE)
  apply(rename_tac d ys y e list aa)(*strict*)
  apply(erule_tac
      x="ys"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = teA aa # list\<rparr>"
      in allE)
  apply(erule_tac
      P="cfgLMTD G d \<lparr>cfg_conf = liftA (case ESplitItem_from (S ! n) of None \<Rightarrow> [] | Some A \<Rightarrow> [A])\<rparr> ys \<lparr>cfg_conf = teA aa # list\<rparr>"
      in impE)
   apply(rename_tac d ys y e list aa)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some y]"
      in get_labels_drop_tail)
    apply(rename_tac d ys y e list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y e list aa)(*strict*)
   apply(force)
  apply(rename_tac d ys y e list aa)(*strict*)
  apply(erule_tac
      P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = liftA (case ESplitItem_from (S ! n) of None \<Rightarrow> [] | Some A \<Rightarrow> [A])\<rparr> = liftB w1 @ liftA w2"
      in impE)
   apply(rename_tac d ys y e list aa)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(case_tac "ESplitItem_from (S ! n)")
    apply(rename_tac d ys y e list aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac d ys y e list aa a)(*strict*)
   apply(rule_tac
      x="[X]" for X
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d ys y e list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e list aa w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac d ys y e list aa w1 w2)(*strict*)
   prefer 2
   apply(rename_tac d ys y e list aa w1 w2 a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y e list aa w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e list aa w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac d ys y e list aa w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y e list aa w2 a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e a lista)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac d ys y e a lista)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac d ys y e a lista)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="y"
      in ballE)
   apply(rename_tac d ys y e a lista)(*strict*)
   prefer 2
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac d ys y e a lista)(*strict*)
  apply(erule disjE)
   apply(rename_tac d ys y e a lista)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d ys y e a lista l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d ys y e a lista l r)(*strict*)
    prefer 2
    apply(rename_tac d ys y e a lista l r aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y e a lista l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ys y e lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac d ys y e lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y e lista a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y e a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys y e a lista ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac d ys y e a lista ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ys e a lista ba A B)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac d ys y e a lista ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac d ys y e a lista ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ys e a lista A B)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d ys e a lista A B l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d ys e a lista A B l r)(*strict*)
    prefer 2
    apply(rename_tac d ys e a lista A B l r aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys e a lista A B l r)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ys y e a lista ba A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ys e a lista A B C)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  done

lemma EValidSplit_continuation_not_empty: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S@S')
  \<Longrightarrow> length S = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S
  \<Longrightarrow> ESplitItem_elem ((S@S') ! (length v)) = Some (teB b)
  \<Longrightarrow> S'=[]
  \<Longrightarrow> Q"
  apply(clarsimp)
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_final_def)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(rule_tac
      xs="S"
      in rev_cases)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(erule_tac
      x="y"
      in ballE)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac ys y d)(*strict*)
  apply(subgoal_tac "(ys @ [y]) ! length v = y")
   apply(rename_tac ys y d)(*strict*)
   prefer 2
   apply (metis last_nth3 Suc_length last_snoc)
  apply(rename_tac ys y d)(*strict*)
  apply(rule_tac
      xs="ESplitItem_prods y"
      in rev_cases)
   apply(rename_tac ys y d)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac "ESplitItem_from y")
    apply(rename_tac ys y d)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y d a)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ys y d ysa ya)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="length ysa"
      and kleene_starT="False"
      and END="True"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac ys y d ysa ya)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac ys y d ysa ya)(*strict*)
    apply(force)
   apply(rename_tac ys y d ysa ya)(*strict*)
   apply(force)
  apply(rename_tac ys y d ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e ci)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e ci l r)(*strict*)
  apply(simp add: option_to_list_def)
  apply(erule_tac
      x="length ysa"
      in allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac l)
   apply(rename_tac ys y d ysa ya e ci l r)(*strict*)
   prefer 2
   apply(rename_tac ys y d ysa ya e ci l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e ci l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e ci r)(*strict*)
  apply(case_tac ci)
  apply(rename_tac ys y d ysa ya e ci r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(simp add: LR1ProdFormSimp_def)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from y")
   apply(rename_tac ys y d ysa ya e r)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    apply(rename_tac ys y d ysa ya e r)(*strict*)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(rename_tac ys y d ysa ya e r)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r a)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac ys y d ysa ya e r a)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ys y d ysa ya e r a)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA a]\<rparr>"
      in allE)
  apply(erule_tac
      x="ysa"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = teA (prod_lhs ya) # r\<rparr>"
      in allE)
  apply(erule impE)
   apply(rename_tac ys y d ysa ya e r a)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some ya]"
      in get_labels_drop_tail)
    apply(rename_tac ys y d ysa ya e r a)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y d ysa ya e r a)(*strict*)
   apply(force)
  apply(rename_tac ys y d ysa ya e r a)(*strict*)
  apply(erule impE)
   apply(rename_tac ys y d ysa ya e r a)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[X]" for X
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac ys y d ysa ya e r a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r a w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac ys y d ysa ya e r a w1 w2)(*strict*)
   prefer 2
   apply(rename_tac ys y d ysa ya e r a w1 w2 aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r a w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r a w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac ys y d ysa ya e r a w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e r a w2 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e a list)(*strict*)
  apply(erule_tac
      x="ya"
      in ballE)
   apply(rename_tac ys y d ysa ya e a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ys y d ysa ya e a list)(*strict*)
  apply(erule disjE)
   apply(rename_tac ys y d ysa ya e a list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac ys y d ysa ya e a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y d ysa ya e a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y d ysa ya e a list ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ys y d ysa ya e a list ba A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e a list ba A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ys y d ysa ya e a list ba A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y d ysa ya e a list ba A B)(*strict*)
  apply(clarsimp)
  done

lemma Esplit_signature_Cons: "
  Esplit_signature (w # v) = Esplit_signature [w] @ Esplit_signature v"
  apply (metis ConsApp Esplit_signature_append)
  done

lemma cfgRM_derivation_to_Esplit_derivation_hlp: "
  n<length w
  \<Longrightarrow>ESplitItem_elem (w!n) = Some (teA A)
  \<Longrightarrow> setA
         (foldl (@) (case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A])
           (map (option_to_list \<circ> ESplitItem_elem) w)) =
        {}
  \<Longrightarrow> Q"
  apply(subgoal_tac "foldl (@) (case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) (map (option_to_list \<circ> ESplitItem_elem) w) = SSX" for SSX)
   prefer 2
   apply(rule foldl_first)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(clarsimp)
  apply(thin_tac "foldl (@) (case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) (map (option_to_list \<circ> ESplitItem_elem) w) = (case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) w)")
  apply(thin_tac "setA (case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) = {}")
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule setA_empty_foldl)
   apply(force)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  done

lemma Xstep_gen_length: "
  LR1ProdFormSimp G
  \<Longrightarrow> \<lparr>prod_lhs=A,prod_rhs=r\<rparr> \<in> cfg_productions G
  \<Longrightarrow> length(Xstep_gen (filterA (tl r)) w) = length r - Suc 0"
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs=A,prod_rhs=r\<rparr>"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: Xstep_gen_def)
  apply(clarsimp)
  apply(rename_tac b Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac b B)(*strict*)
   apply(simp add: Xstep_gen_def)
   apply (metis Suc_length append_Nil list.size(3) natUptTo_n_n)
  apply(rename_tac b Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac B)(*strict*)
   apply(simp add: Xstep_gen_def)
  apply(rename_tac b Aa B)(*strict*)
  apply(clarsimp)
  apply(rename_tac B C)(*strict*)
  apply(simp add: Xstep_gen_def)
  apply (metis Suc_length append_Nil list.size(3) natUptTo_n_n)
  done

theorem Esplit_derivation_enforces_EValidSplitExt_no_elim_before_nonterminal: "
  Esplit_TSstructure G
  \<Longrightarrow> F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e S)
  \<Longrightarrow> k<length S
  \<Longrightarrow> ESplitItem_elem (S!k) = Some (teA A)
  \<Longrightarrow> i\<le>k
  \<Longrightarrow> ESplitItem_elim (S!i) = []"
  apply(induct n arbitrary: e S k i A)
   apply(rename_tac e S k i A)(*strict*)
   apply(simp add: Esplit.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac S k i A)(*strict*)
   apply(simp add: Esplit_initial_configurations_def)
  apply(rename_tac n e S k i A)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e S k i A)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="n"
      and m="Suc n"
      in Esplit.step_detail_before_some_position)
     apply(rename_tac n e S k i A)(*strict*)
     apply(rule Esplit.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e S k i A)(*strict*)
    apply(force)
   apply(rename_tac n e S k i A)(*strict*)
   apply(force)
  apply(rename_tac n e S k i A)(*strict*)
  apply(clarsimp)
  apply(rename_tac n S k i A e1 e2 c1)(*strict*)
  apply(simp add: Esplit_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="S1 @ SL # S2"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac "i<length S1")
   apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
   apply(rule_tac
      t="(S1 @ Xstep_mergeL (Xstep_elem SL e2 # Xstep_gen (filterA (tl (prod_rhs e2))) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2) ! i"
      in ssubst)
    apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
   apply(erule_tac
      x="length S1"
      in meta_allE)
   apply(erule_tac
      x="i"
      in meta_allE)
   apply(clarsimp)
   apply(case_tac e2)
   apply(rename_tac n k i A e1 e2 S1 SL S2 prod_lhsa prod_rhsa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i A e1 S1 SL S2 prod_lhs prod_rhs)(*strict*)
   apply(erule_tac
      x="prod_lhs"
      in meta_allE)
   apply(clarsimp)
   apply(rule_tac
      t="S1!i"
      and s="(S1 @ SL # S2) ! i"
      in subst)
    apply(rename_tac n k i A e1 S1 SL S2 prod_lhs prod_rhs)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n k i A e1 S1 SL S2 prod_lhs prod_rhs)(*strict*)
   apply(force)
  apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
  apply(subgoal_tac "EValidSplit G (S1 @ SL # S2)")
   apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
    prefer 2
    apply(rule_tac
      i="n"
      in Esplit.belongs_configurations)
     apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
     apply(rule Esplit.derivation_initial_belongs)
      apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
      apply(force)
     apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
   apply(simp add: Esplit_configurations_def)
  apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
  apply(case_tac S2)
   apply(rename_tac n k i A e1 e2 S1 SL S2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i A e1 e2 S1 SL)(*strict*)
   apply(case_tac e2)
   apply(rename_tac n k i A e1 e2 S1 SL prod_lhsa prod_rhsa)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac n k i Aa e1 e2 S1 SL A w)(*strict*)
   apply(rule prop_of_nth_append)
     apply(rename_tac n k i Aa e1 e2 S1 SL A w)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 e2 S1 SL A w ia)(*strict*)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(erule_tac
      x="ia"
      in meta_allE)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
    apply(rule_tac
      t="S1!ia"
      and s="(S1@[SL])!ia"
      in subst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 e2 S1 SL A w ia)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_mergeL_def)
   apply(rule conjI)
    apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
     apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
     apply(clarsimp)
     apply(rename_tac n k i Aa e1 S1 SL A w)(*strict*)
     apply(subgoal_tac "i=length S1")
      apply(rename_tac n k i Aa e1 S1 SL A w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL A w)(*strict*)
     apply(clarsimp)
     apply(rename_tac n k Aa e1 S1 SL A w)(*strict*)
     apply(simp add: Xstep_merge1_def)
     apply(rule conjI)
      apply(rename_tac n k Aa e1 S1 SL A w)(*strict*)
      apply(clarsimp)
      apply(simp add: Xstep_merge1_toWasNotEliminated_def Xstep_elem_def)
      apply(erule_tac
      x="length S1"
      in meta_allE)
      apply(erule_tac
      x="length S1"
      in meta_allE)
      apply(clarsimp)
     apply(rename_tac n k Aa e1 S1 SL A w)(*strict*)
     apply(clarsimp)
     apply(simp add: Xstep_merge1_toWasEliminated_def EmptyESplitItem_def Xstep_elem_def strict_prefix_def)
     apply(clarsimp)
     apply(erule_tac
      x="length S1"
      in meta_allE)
     apply(erule_tac
      x="length S1"
      in meta_allE)
     apply(clarsimp)
     apply(case_tac w)
      apply(rename_tac n k Aa e1 S1 SL A w)(*strict*)
      prefer 2
      apply(rename_tac n k Aa e1 S1 SL A w a list)(*strict*)
      apply(simp add: nth_opt_def)
     apply(rename_tac n k Aa e1 S1 SL A w)(*strict*)
     apply(clarsimp)
     apply(rename_tac n k Aa e1 S1 SL A)(*strict*)
     apply(subgoal_tac "k= length S1")
      apply(rename_tac n k Aa e1 S1 SL A)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n k Aa e1 S1 SL A)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w ia a)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w a)(*strict*)
    apply(simp add: Xstep_elem_def)
    apply(case_tac w)
     apply(rename_tac n k i Aa e1 S1 SL A w a)(*strict*)
     apply(simp add: nth_opt_def)
    apply(rename_tac n k i Aa e1 S1 SL A w a aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A a aa list)(*strict*)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
   apply(clarsimp)
   apply(rule prop_of_nth_Cons)
     apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia)(*strict*)
    apply(simp add: Xstep_elem_def)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
   apply(clarsimp)
   apply(rule prop_of_nth_append)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      xs="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in rev_cases)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_gen_def)
    apply(case_tac "filterA (tl w) = []")
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(nat_seq 0 (length (filterA (tl w)) - Suc 0)) = SSX" for SSX)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(rule_tac
      t="ys ! ic"
      and s="(ys@[y])!ic"
      in subst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(rule_tac
      t="ys @ [y]"
      and s="map (\<lambda>n. \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (filterA (tl w) ! n), ESplitItem_ignore = drop (Suc n) (filterA (tl w)) @ ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (filterA (tl w) ! n)), ESplitItem_to = []\<rparr>) (nat_seq 0 (length (filterA (tl w)) - Suc 0))"
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(rule nth_map)
     apply(clarsimp)
     apply(rule_tac
      t="length (filterA (tl w))"
      and s="length(map (\<lambda>n. \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (filterA (tl w) ! n), ESplitItem_ignore = drop (Suc n) (filterA (tl w)) @ ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (filterA (tl w) ! n)), ESplitItem_to = []\<rparr>) (nat_seq 0 (length (filterA (tl w)) - Suc 0)))"
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
      apply(clarsimp)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(rule_tac
      t="map (\<lambda>n. \<lparr>ESplitItem_elim = [], ESplitItem_from = Some (filterA (tl w) ! n), ESplitItem_ignore = drop (Suc n) (filterA (tl w)) @ ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA (filterA (tl w) ! n)), ESplitItem_to = []\<rparr>) (nat_seq 0 (length (filterA (tl w)) - Suc 0))"
      and s="ys @ [y]"
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic)(*strict*)
   apply(case_tac ic)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic)(*strict*)
    prefer 2
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic nat)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic nat)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
    apply(subgoal_tac "Suc nat < Suc 0")
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
    apply(rule_tac
      t="Suc 0"
      and s="length (case ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))])"
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
     apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
      apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
      apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
       apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
       apply(force)
      apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat a)(*strict*)
     apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="Some a" for a
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat a)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat a)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib ic)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
   apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
    apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
    apply(simp (no_asm))
    apply(simp add: EmptyESplitItem_def)
    apply(simp add: Xstep_merge1_def Xstep_merge1_toWasNotEliminated_def Xstep_merge1_toWasEliminated_def)
    apply(subgoal_tac "ESplitItem_elim (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) = [] \<and> option_to_list (ESplitItem_from (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))) = []")
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
    apply(simp add: Xstep_gen_def)
    apply(case_tac "filterA (tl w) = []")
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
     prefer 2
     apply(rule_tac
      n="0"
      and m="length (filterA (tl w)) - Suc 0"
      in nat_seq_drop_last2)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib a)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_gen_def)
   apply(case_tac "filterA (tl w) = []")
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib a)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n k i Aa e1 S1 SL A w ia ib a)(*strict*)
    prefer 2
    apply(rule_tac
      n="0"
      and m="length (filterA (tl w)) - Suc 0"
      in nat_seq_drop_last2)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL A w ia ib a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n k i A e1 e2 S1 SL S2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i A e1 e2 S1 SL a list)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n k i A e1 e2 S1 SL a list prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n k i Aa e1 e2 S1 SL a list A w)(*strict*)
  apply(subgoal_tac "k < length S1 + (length (Xstep_mergeL (Xstep_elem SL e2 # Xstep_gen (filterA (tl (prod_rhs e2))) (ESplitItem_to SL @ ESplitItem_ignore SL)) None))")
   apply(rename_tac n k i Aa e1 e2 S1 SL a list A w)(*strict*)
   prefer 2
   apply(case_tac "k < length S1 + length (Xstep_mergeL (Xstep_elem SL e2 # Xstep_gen (filterA (tl (prod_rhs e2))) (ESplitItem_to SL @ ESplitItem_ignore SL)) None)")
    apply(rename_tac n k i Aa e1 e2 S1 SL a list A w)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 e2 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(subgoal_tac "length S1 + length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) None) \<le> k")
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(case_tac "length S1 + length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) None) = k")
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n i Aa e1 S1 SL a list A w)(*strict*)
    apply(simp add: Xstep_mergeL_def nth_opt_def)
    apply(case_tac "ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
     apply(rename_tac n i Aa e1 S1 SL a list A w)(*strict*)
     prefer 2
     apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(subgoal_tac "ESplitItem_elem (((case Some aa of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) @ list) ! length (case Some aa of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))])) = Some (teA Aa)")
      apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
      prefer 2
      apply(rule_tac
      t="Some aa"
      and s="ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      in subst)
       apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
       apply(force)
      apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
      apply(force)
     apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(thin_tac "ESplitItem_elem (((case ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) @ list) ! length (case ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))])) = Some (teA Aa)")
     apply(rename_tac n i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(clarsimp)
     apply(simp add: Esplit_signature_def option_to_list_def)
     apply (metis ConsApp suffixes_setA_1 suffixes_intro2 emptyE foldl_append_initial_pullout map_map)
    apply(rename_tac n i Aa e1 S1 SL a list A w)(*strict*)
    apply(clarsimp)
    apply(case_tac list)
     apply(rename_tac n i Aa e1 S1 SL a list A w)(*strict*)
     apply(clarsimp)
    apply(rename_tac n i Aa e1 S1 SL a list A w aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
    apply(simp add: Esplit_signature_def option_to_list_def)
    apply(thin_tac "d (Suc n) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) (S1 @ (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) @ Xstep_merge1 (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a # aa # lista))")
    apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
    apply(thin_tac "\<And>k i A. k < Suc (Suc (Suc (length S1 + length lista))) \<Longrightarrow> ESplitItem_elem ((S1 @ SL # a # aa # lista) ! k) = Some (teA A) \<Longrightarrow> i \<le> k \<Longrightarrow> ESplitItem_elim ((S1 @ SL # a # aa # lista) ! i) = [] ")
    apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
    apply(thin_tac "ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) = None")
    apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
    apply(subgoal_tac "foldl (@) ((case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ [teA Aa]) (map (option_to_list \<circ> ESplitItem_elem) lista) = SSX" for SSX)
     apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
     prefer 2
     apply(rule foldl_first)
    apply(rename_tac n i Aa e1 S1 SL a A w aa lista)(*strict*)
    apply(clarsimp)
    apply(simp add: setAConcat)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(subgoal_tac "length S1 + length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) None) < k")
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt (a # list) 0) @ list) ! k = list!(SSn)" for SSn)
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    prefer 2
    apply(rule_tac
      t="S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt (a # list) 0) @ list"
      and s="(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt (a # list) 0)) @ list"
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    apply(rule nth_append_2)
    apply(clarsimp)
    apply(simp add: nth_opt_def)
    apply(simp add: Xstep_mergeL_def)
    apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     apply(clarsimp)
     apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
      apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
      apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
       apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
       apply(force)
      apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
      apply(clarsimp)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="Some SSX" for SSX
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
    apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="Some SSX" for SSX
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(simp add: Esplit_signature_def option_to_list_def)
   apply(rule cfgRM_derivation_to_Esplit_derivation_hlp)
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(simp add: nth_opt_def)
   apply(thin_tac "(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some a) @ list) ! k = list ! (k - (length S1 + length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (Some a))))")
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(simp add: Xstep_mergeL_def)
   apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="Some SSX" for SSX
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="None"
      in ssubst)
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
   apply(rule_tac
      t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      and s="Some SSX" for SSX
      in ssubst)
    apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w aa ab)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 e2 S1 SL a list A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
  apply(rule_tac
      t="(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt (a # list) 0) @ list) ! i"
      in ssubst)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
  apply(thin_tac "k < length S1 + (length (Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt (a # list) 0)) + length list)")
  apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
  apply(simp add: Xstep_mergeL_def nth_opt_def)
  apply(rule conjI)
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_merge1_def)
    apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_elem_def strict_prefix_def)
    apply(case_tac w)
     apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
     prefer 2
     apply(rename_tac n k i Aa e1 S1 SL a list A w aa lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac n k i Aa e1 S1 SL a list A aa lista)(*strict*)
     apply(simp add: nth_opt_def)
    apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(rule conjI)
     apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
     apply(clarsimp)
     apply(rename_tac n k i Aa e1 S1 SL a list A c)(*strict*)
     apply(erule_tac
      x="length S1"
      in meta_allE)
     apply(erule_tac
      x="length S1"
      in meta_allE)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(erule_tac
      x="length S1"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "ESplitItem_elem ((S1 @ (if False then Xstep_merge1_toWasNotEliminated (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>) a else Xstep_merge1_toWasEliminated (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>) a) # list) ! k) = Some (teA Aa)")
     apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
     prefer 2
     apply(rule_tac
      t="False"
      and s="\<exists>c. c \<noteq> [] \<and> ESplitItem_elim a @ c = ESplitItem_to SL"
      in ssubst)
      apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
      apply(force)
     apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(thin_tac "ESplitItem_elem ((S1 @ (if \<exists>c. c \<noteq> [] \<and> ESplitItem_elim a @ c = ESplitItem_to SL then Xstep_merge1_toWasNotEliminated (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>) a else Xstep_merge1_toWasEliminated (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>) a) # list) ! k) = Some (teA Aa)")
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_elem_def strict_prefix_def)
    apply(subgoal_tac "False")
     apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(case_tac "k=length S1")
     apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
     apply(clarsimp)
     apply(rename_tac n Aa e1 S1 SL a list A)(*strict*)
     apply(simp add: Esplit_signature_def option_to_list_def)
     apply(subgoal_tac "foldl (@) [teA Aa] (map (option_to_list \<circ> ESplitItem_elem) list) = SSX" for SSX)
      apply(rename_tac n Aa e1 S1 SL a list A)(*strict*)
      prefer 2
      apply(rule foldl_first)
     apply(rename_tac n Aa e1 S1 SL a list A)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w aa)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_elem_def strict_prefix_def)
   apply(erule_tac
      x="length S1"
      in meta_allE)
   apply(erule_tac
      x="length S1"
      in meta_allE)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
  apply(clarsimp)
  apply(case_tac "i-length S1")
   apply(rename_tac n k i Aa e1 S1 SL a list A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k Aa e1 S1 SL a list A w)(*strict*)
   apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_merge1_toWasNotEliminated_def EmptyESplitItem_def Xstep_elem_def strict_prefix_def)
   apply(erule_tac
      x="length S1"
      in meta_allE)
   apply(erule_tac
      x="length S1"
      in meta_allE)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "i-length S1")
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(subgoal_tac "length (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) =SSX" for SSX)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   prefer 2
   apply(rule Xstep_gen_length)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(case_tac "nat < length ((butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))))")
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(rule_tac
      t="(butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) @ (case ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) @ list) ! nat"
      and s="(butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) ! nat"
      in ssubst)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      xs="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in rev_cases)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="ys ! nat"
      and s="(ys@[y])!nat"
      in subst)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
   apply(rule_tac
      t="ys @ [y]"
      and s="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in ssubst)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
   apply(simp add: Xstep_gen_def)
   apply(case_tac "filterA (tl w) = []")
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
   apply(case_tac w)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat ys y aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa lista ab listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa ab listb)(*strict*)
   apply(case_tac ab)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa ab listb ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
    prefer 2
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa ab listb b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb b)(*strict*)
    apply(subgoal_tac "LR1ProdFormSimp G")
     apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb b)(*strict*)
     prefer 2
     apply(simp add: split_TSstructure_def)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb b)(*strict*)
    apply(simp add: LR1ProdFormSimp_def)
    apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = aa # teB b # listb\<rparr>"
      in ballE)
     apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb b)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb b)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
   apply(subgoal_tac "LR1ProdFormSimp G")
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = aa # teA ac # listb\<rparr>"
      in ballE)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac b Ab B)(*strict*)
   apply(subgoal_tac "nat_seq 0 0 = [0]")
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac b Ab B)(*strict*)
    apply(erule disjE)
     apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac b Ab B)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac b Ab B)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat ys y aa listb ac b Ab B)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(rule_tac
      t="(butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) @ (case ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) @ list) ! nat"
      and s="((case ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) @ list) ! SSX" for SSX
      in ssubst)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(rule_tac u="butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))" in nth_append_2_prime)
     apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="length (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))"
      and s="length w-Suc 0"
      in ssubst)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))")
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(subgoal_tac "k < length S1 + (length w - Suc 0 + length (case None of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    prefer 2
    apply(rule_tac
      t="None"
      and s="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      in subst)
     apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(thin_tac "k < length S1 + (length w - Suc 0 + length (case ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(rule_tac
      s="None"
      and t="ESplitItem_elem (last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)))"
      in subst)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_def)
   apply(rule conjI)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_merge1_toWasNotEliminated_def)
    apply(simp add: Xstep_gen_def)
    apply(case_tac "filterA (tl w) = []")
     apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
     prefer 2
     apply(rule_tac
      n="0"
      and m="length (filterA (tl w)) - Suc 0"
      in nat_seq_drop_last2)
     apply(force)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_toWasEliminated_def)
   apply(subgoal_tac "False")
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(simp add: Xstep_gen_def)
   apply(case_tac "filterA (tl w) = []")
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
    prefer 2
    apply(rule_tac
      n="0"
      and m="length (filterA (tl w)) - Suc 0"
      in nat_seq_drop_last2)
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
  apply(case_tac "filterA (tl w) = []")
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa ab lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ab lista)(*strict*)
   apply(simp add: Xstep_gen_def)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
  apply(rule_tac
      xs="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in rev_cases)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa ys y)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A w nat aa ys y ab lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab lista)(*strict*)
  apply(case_tac lista)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab lista ac listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab ac listb)(*strict*)
  apply(case_tac ac)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab ac listb ad)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
   apply(subgoal_tac "listb=[]")
    apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
    apply(clarsimp)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat aa y ab ad)(*strict*)
    apply(simp add: Xstep_gen_def)
    apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
   apply(subgoal_tac "LR1ProdFormSimp G")
    apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = ab # teA ad # listb\<rparr>"
      in ballE)
    apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad)(*strict*)
   apply(clarsimp)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb ad b Ab B)(*strict*)
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab ac listb b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb b)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb b)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb b)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = ab # teB b # listb\<rparr>"
      in ballE)
   apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n k i Aa e1 S1 SL a list A nat aa ys y ab listb b)(*strict*)
  apply(clarsimp)
  done

lemma Esplit_signature_single_not_empty_setA: "
  ESplitItem_elem a = Some (teA Aa)
  \<Longrightarrow> setA (Esplit_signature [a]) = {}
  \<Longrightarrow> Q"
  apply(simp add: Esplit_signature_def option_to_list_def)
  done

lemma Esplit_signature_Cons_not_empty_setA: "
  ESplitItem_elem a = Some (teA Aa)
  \<Longrightarrow> setA (Esplit_signature (a # list)) = {}
  \<Longrightarrow> Q"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      w="a"
      and v="list"
      in Esplit_signature_Cons)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(clarsimp)
  apply(thin_tac "Esplit_signature (a # list) = Esplit_signature [a] @ Esplit_signature list")
  apply(thin_tac "setA (Esplit_signature list) = {}")
  apply(rule Esplit_signature_single_not_empty_setA)
   apply(force)
  apply(force)
  done

lemma Esplit_signature_Cons_not_empty_setA2: "
  ESplitItem_elem (list ! k) = Some (teA Aa)
  \<Longrightarrow> setA (Esplit_signature (a # list)) = {}
  \<Longrightarrow> k<length list
  \<Longrightarrow> Q"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      w="a"
      and v="list"
      in Esplit_signature_Cons)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(clarsimp)
  apply(thin_tac "Esplit_signature (a # list) = Esplit_signature [a] @ Esplit_signature list")
  apply(thin_tac "setA (Esplit_signature [a]) = {}")
  apply(simp add: Esplit_signature_def option_to_list_def)
  apply(subgoal_tac "setA (foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) list)) \<noteq> {}")
   apply(force)
  apply(rule_tac
      t="list"
      and s="take k list @ [list!k] @ drop(Suc k) list"
      in ssubst)
   apply (metis ConsApp id_take_nth_drop take_drop_rev2)
  apply(simp add: foldl_distrib_append)
  apply(simp add: Esplit_signature_def option_to_list_def)
  apply(rule_tac
      t="foldl (@) (foldl (@) [] (map (\<lambda>a. case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) (take k list)) @ [teA Aa]) (map (\<lambda>a. case ESplitItem_elem a of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) (drop (Suc k) list))"
      in ssubst)
   apply(rule foldl_first)
  apply(simp add: foldl_distrib_append)
  apply(simp add: setAConcat)
  done

theorem Esplit_derivation_enforces_EValidSplitExt_no_pop_in_prods_before_nonterminal: "
  Esplit_TSstructure G
  \<Longrightarrow> F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e S)
  \<Longrightarrow> k<length S
  \<Longrightarrow> ESplitItem_elem (S!k) = Some (teA A)
  \<Longrightarrow> i\<le>k
  \<Longrightarrow> j < length (ESplitItem_prods (S!i))
  \<Longrightarrow> prod_rhs (ESplitItem_prods (S!i)!j) \<noteq> []"
  apply(induct n arbitrary: e S k A i j)
   apply(rename_tac e S k A i j)(*strict*)
   apply(simp add: Esplit.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac S k A i j)(*strict*)
   apply(simp add: Esplit_initial_configurations_def)
  apply(rename_tac n e S k A i j)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e S k A i j)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="n"
      and m="Suc n"
      in Esplit.step_detail_before_some_position)
     apply(rename_tac n e S k A i j)(*strict*)
     apply(rule Esplit.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e S k A i j)(*strict*)
    apply(force)
   apply(rename_tac n e S k A i j)(*strict*)
   apply(force)
  apply(rename_tac n e S k A i j)(*strict*)
  apply(clarsimp)
  apply(rename_tac n S k A i j e1 e2 c1)(*strict*)
  apply(simp add: Esplit_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n k A i j e1 e2 S1 SL S2)(*strict*)
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
  apply(rename_tac n k A i j e1 e2 S1 SL S2 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n k Aa i j e1 e2 S1 SL S2 A w)(*strict*)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
  apply(thin_tac "Esplit.derivation_initial G d")
  apply(thin_tac "d (Suc n) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2))")
  apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
  apply(thin_tac "d n = Some (pair e1 (S1 @ SL # S2))")
  apply(case_tac "i<length S1")
   apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
   apply(erule_tac
      x="i"
      in meta_allE)
   apply(erule_tac
      x="j"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   apply(subgoal_tac "(S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2) ! i = S1!i")
    apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   apply(subgoal_tac "(S1 @ SL # S2) ! i = SSX" for SSX)
    apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   apply(force)
  apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
  apply(subgoal_tac "length S1\<le>i")
   apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n k Aa i j e1 S1 SL S2 A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
  apply(case_tac "i=length S1")
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   apply(erule_tac
      x="i"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL S2 A w)(*strict*)
   apply(case_tac S2)
    apply(rename_tac k Aa j S1 SL S2 A w)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A w)(*strict*)
    apply(simp add: nth_opt_def)
    apply(simp add: Xstep_mergeL_def)
    apply(case_tac "Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)")
     apply(rename_tac k Aa j S1 SL A w)(*strict*)
     apply(subgoal_tac "k < length S1 + (length (if True then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if True then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
      apply(rename_tac k Aa j S1 SL A w)(*strict*)
      prefer 2
      apply(rule_tac
      t="True"
      and s="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = []"
      in ssubst)
       apply(rename_tac k Aa j S1 SL A w)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A w)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A w)(*strict*)
     apply(thin_tac "k < length S1 + (length (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
     apply(rename_tac k Aa j S1 SL A w)(*strict*)
     apply(clarsimp)
     apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
      apply(rename_tac k Aa j S1 SL A w)(*strict*)
      apply(clarsimp)
      apply(simp add: Xstep_elem_def)
      apply(case_tac w)
       apply(rename_tac k Aa j S1 SL A w)(*strict*)
       prefer 2
       apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
       apply(simp add: nth_opt_def)
      apply(rename_tac k Aa j S1 SL A w)(*strict*)
      apply(clarsimp)
      apply(rename_tac k Aa j S1 SL A)(*strict*)
      apply(simp add: nth_opt_def)
      apply(simp add: Xstep_merge1_def EmptyESplitItem_def)
      apply(case_tac "strict_prefix [] (ESplitItem_to SL)")
       apply(rename_tac k Aa j S1 SL A)(*strict*)
       apply(clarsimp)
       apply(simp add: Xstep_merge1_toWasNotEliminated_def)
       apply(case_tac "k=length S1")
        apply(rename_tac k Aa j S1 SL A)(*strict*)
        apply(clarsimp)
       apply(rename_tac k Aa j S1 SL A)(*strict*)
       apply(subgoal_tac "k<length S1")
        apply(rename_tac k Aa j S1 SL A)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac k Aa j S1 SL A)(*strict*)
       apply(clarsimp)
      apply(rename_tac k Aa j S1 SL A)(*strict*)
      apply(clarsimp)
      apply(simp add: Xstep_merge1_toWasEliminated_def)
     apply(rename_tac k Aa j S1 SL A w a)(*strict*)
     apply(clarsimp)
     apply(simp add: Xstep_elem_def)
     apply(case_tac w)
      apply(rename_tac k Aa j S1 SL A w a)(*strict*)
      apply(simp add: nth_opt_def)
     apply(rename_tac k Aa j S1 SL A w a aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a aa list)(*strict*)
     apply(simp add: nth_opt_def)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      prefer 2
      apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
      apply(simp add: Xstep_gen_def)
      apply(clarsimp)
      apply(rename_tac k Aa j S1 SL A a aa lista)(*strict*)
      apply(case_tac aa)
       apply(rename_tac k Aa j S1 SL A a aa lista ab)(*strict*)
       apply(clarsimp)
       apply(rename_tac k Aa j S1 SL A a lista ab)(*strict*)
       apply(rule nat_seq_not_empty)
        apply(rename_tac k Aa j S1 SL A a lista ab)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac k Aa j S1 SL A a lista ab)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a aa lista b)(*strict*)
      apply(clarsimp)
      apply(rename_tac k Aa j S1 SL A a lista b)(*strict*)
      apply(rule LR1_terminal_only_at_front_in_prods)
       apply(rename_tac k Aa j S1 SL A a lista b)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a lista b)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a)(*strict*)
     apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = []")
     apply(case_tac "j=length (ESplitItem_prods SL)")
      apply(rename_tac k Aa j S1 SL A a)(*strict*)
      apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a)(*strict*)
     apply(subgoal_tac "j<length (ESplitItem_prods SL)")
      apply(rename_tac k Aa j S1 SL A a)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac k Aa j S1 SL A a)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      x="j"
      in meta_allE)
     apply(clarsimp)
     apply(subgoal_tac "(ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a]\<rparr>]) ! j=SSX" for SSX)
      apply(rename_tac k Aa j S1 SL A a)(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length(Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) = SSX" for SSX)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     prefer 2
     apply(rule Xstep_gen_length)
      apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(case_tac w)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(subgoal_tac "a#list=[]")
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(rule_tac
      t="a#list"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in ssubst)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(rule_tac
      t="[]"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in subst)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = a # list")
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(case_tac lista)
     apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa lista ab listb)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
    apply(subgoal_tac "listb=[]")
     apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
     prefer 2
     apply(rule LR1_at_most_two_symbols)
      apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a aa ab)(*strict*)
    apply(case_tac ab)
     apply(rename_tac k Aa j S1 SL A a aa ab ac)(*strict*)
     prefer 2
     apply(rename_tac k Aa j S1 SL A a aa ab b)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a aa b)(*strict*)
     apply(simp add: Xstep_gen_def)
    apply(rename_tac k Aa j S1 SL A a aa ab ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a aa ac)(*strict*)
    apply(simp add: Xstep_gen_def)
    apply(subgoal_tac "nat_seq 0 0 = [0]")
     apply(rename_tac k Aa j S1 SL A a aa ac)(*strict*)
     prefer 2
     apply (metis natUptTo_n_n)
    apply(rename_tac k Aa j S1 SL A a aa ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
    apply(simp add: Xstep_elem_def)
    apply(simp add: Xstep_gen_def)
    apply(case_tac "j=length (ESplitItem_prods SL)")
     apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
     apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
    apply(subgoal_tac "j<length (ESplitItem_prods SL)")
     apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="j"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "(ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>]) ! j = SSX" for SSX)
     apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac k Aa j S1 SL A aa ac)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa j S1 SL S2 A w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_mergeL_def)
   apply(subgoal_tac "length(Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) = SSX" for SSX)
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    prefer 2
    apply(rule Xstep_gen_length)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
   apply(case_tac "Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)")
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(subgoal_tac "k < length S1 + (length (if True then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if True then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) + length list)")
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     prefer 2
     apply(rule_tac
      t="True"
      and s="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = []"
      in ssubst)
      apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(thin_tac "k < length S1 + (length (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) a] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)), a]) + length list)")
    apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(clarsimp)
     apply(simp add: Xstep_elem_def)
     apply(case_tac w)
      apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
      prefer 2
      apply(rename_tac k Aa j S1 SL A w a list aa lista)(*strict*)
      apply(simp add: nth_opt_def)
     apply(rename_tac k Aa j S1 SL A w a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(simp add: nth_opt_def)
     apply(simp add: Xstep_merge1_def EmptyESplitItem_def)
     apply(case_tac "strict_prefix (ESplitItem_elim a) (ESplitItem_to SL)")
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(clarsimp)
      apply(simp add: Xstep_merge1_toWasNotEliminated_def)
      apply(case_tac "k=length S1")
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       apply(clarsimp)
       apply(rename_tac Aa j SL A a list)(*strict*)
       apply(thin_tac "Esplit_TSstructure G")
       apply(thin_tac "F2LR1inputx G G'")
       apply(thin_tac "split_TSstructure G")
       apply(thin_tac "j < Suc (length (ESplitItem_prods SL) + (length (foldl (@) [] (ESplitItem_elim_prods a)) + length (ESplitItem_prods a)))")
       apply(thin_tac "prod_rhs ((ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a) ! j) = []")
       apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = []\<rparr> \<in> cfg_productions G")
       apply(thin_tac "ESplitItem_elem SL = Some (teA A)")
       apply(thin_tac "\<And>j. j < length (ESplitItem_prods SL) \<Longrightarrow> prod_rhs (ESplitItem_prods SL ! j) \<noteq> []")
       apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = []")
       apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = []")
       apply(thin_tac "strict_prefix (ESplitItem_elim a) (ESplitItem_to SL)")
       apply(rule Esplit_signature_Cons_not_empty_setA)
        apply(rename_tac Aa j SL A a list)(*strict*)
        apply(force)
       apply(rename_tac Aa j SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(subgoal_tac "length S1<k")
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = list!SSX" for SSX)
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       prefer 2
       apply(rule nth_append_2_prime)
         apply(rename_tac k Aa j S1 SL A a list)(*strict*)
         apply(force)
        apply(rename_tac k Aa j S1 SL A a list)(*strict*)
        apply(force)
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(clarsimp)
      apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = list ! (k - Suc (length S1))")
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(rule Esplit_signature_Cons_not_empty_setA2)
        apply(rename_tac k Aa j S1 SL A a list)(*strict*)
        apply(force)
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(clarsimp)
     apply(simp add: Xstep_merge1_toWasEliminated_def)
     apply(case_tac "k=length S1")
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac Aa j SL A a list)(*strict*)
      apply(rule Esplit_signature_Cons_not_empty_setA)
       apply(rename_tac Aa j SL A a list)(*strict*)
       apply(force)
      apply(rename_tac Aa j SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(subgoal_tac "length S1<k")
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = list!SSX" for SSX)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      prefer 2
      apply(rule nth_append_2_prime)
        apply(rename_tac k Aa j S1 SL A a list)(*strict*)
        apply(force)
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = list ! (k - Suc (length S1))")
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(rule Esplit_signature_Cons_not_empty_setA2)
       apply(rename_tac k Aa j S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A w a list aa)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_elem_def)
    apply(case_tac w)
     apply(rename_tac k Aa j S1 SL A w a list aa)(*strict*)
     apply(simp add: nth_opt_def)
    apply(rename_tac k Aa j S1 SL A w a list aa ab lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa ab lista)(*strict*)
    apply(simp add: nth_opt_def)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(case_tac lista)
     apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
     prefer 2
     apply(rename_tac k Aa j S1 SL A a list aa lista ab listb)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list aa ab listb)(*strict*)
     apply(simp add: Xstep_gen_def)
     apply(case_tac ab)
      apply(rename_tac k Aa j S1 SL A a list aa ab listb ac)(*strict*)
      apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list aa ab listb b)(*strict*)
     apply(clarsimp)
     apply(rename_tac k Aa j S1 SL A a list aa listb b)(*strict*)
     apply(rule LR1_terminal_only_at_front_in_prods)
      apply(rename_tac k Aa j S1 SL A a list aa listb b)(*strict*)
      apply(force)
     apply(rename_tac k Aa j S1 SL A a list aa listb b)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
    apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = []")
    apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = []")
    apply(case_tac "j=length (ESplitItem_prods SL)")
     apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
    apply(subgoal_tac "j<length (ESplitItem_prods SL)")
     apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="j"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "(ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa]\<rparr>]) ! j=SSX" for SSX)
     apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa)(*strict*)
    apply(force)
   apply(rename_tac k Aa j S1 SL A w a list aa lista)(*strict*)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac k Aa j S1 SL A w a list aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(subgoal_tac "aa#lista=[]")
     apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(rule_tac
      t="aa#lista"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in ssubst)
     apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(rule_tac
      t="[]"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in subst)
     apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
     apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = aa # lista")
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac k Aa j S1 SL A w a list aa lista ab listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list aa lista ab listb)(*strict*)
   apply(case_tac listb)
    apply(rename_tac k Aa j S1 SL A a list aa lista ab listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list aa lista ab listb ac listc)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list aa lista ab ac listc)(*strict*)
   apply(subgoal_tac "listc=[]")
    apply(rename_tac k Aa j S1 SL A a list aa lista ab ac listc)(*strict*)
    prefer 2
    apply(rule LR1_at_most_two_symbols)
     apply(rename_tac k Aa j S1 SL A a list aa lista ab ac listc)(*strict*)
     apply(force)
    apply(rename_tac k Aa j S1 SL A a list aa lista ab ac listc)(*strict*)
    apply(force)
   apply(rename_tac k Aa j S1 SL A a list aa lista ab ac listc)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list aa ab ac)(*strict*)
   apply(case_tac ac)
    apply(rename_tac k Aa j S1 SL A a list aa ab ac ad)(*strict*)
    prefer 2
    apply(rename_tac k Aa j S1 SL A a list aa ab ac b)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa j S1 SL A a list aa ab b)(*strict*)
    apply(simp add: Xstep_gen_def)
   apply(rename_tac k Aa j S1 SL A a list aa ab ac ad)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list aa ab ad)(*strict*)
   apply(simp add: Xstep_gen_def)
   apply(subgoal_tac "nat_seq 0 0 = [0]")
    apply(rename_tac k Aa j S1 SL A a list aa ab ad)(*strict*)
    prefer 2
    apply (metis natUptTo_n_n)
   apply(rename_tac k Aa j S1 SL A a list aa ab ad)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
   apply(simp add: Xstep_elem_def)
   apply(simp add: Xstep_gen_def)
   apply(case_tac "j=length (ESplitItem_prods SL)")
    apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
   apply(subgoal_tac "j<length (ESplitItem_prods SL)")
    apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="j"
      in meta_allE)
   apply(clarsimp)
   apply(subgoal_tac "(ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [ab, teA ad]\<rparr>]) ! j = SSX" for SSX)
    apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac k Aa j S1 SL A a list ab ad)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
  apply(subgoal_tac "length S1<i")
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac k Aa i j S1 SL S2 A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL S2 A)(*strict*)
   apply(simp add: Xstep_mergeL_def)
   apply(simp add: Xstep_gen_def)
   apply(case_tac S2)
    apply(rename_tac k Aa i j S1 SL S2 A)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa i j S1 SL A)(*strict*)
    apply(simp add: nth_opt_def)
    apply(simp add: Xstep_gen_def)
    apply(simp add: Xstep_elem_def)
    apply(simp add: nth_opt_def)
   apply(rename_tac k Aa i j S1 SL S2 A a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_merge1_def)
   apply(case_tac "strict_prefix (ESplitItem_elim a) (ESplitItem_to (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>))")
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_merge1_toWasNotEliminated_def Xstep_elem_def)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = list!SSX" for SSX)
     apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(clarsimp)
    apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = list ! (k - Suc (length S1))")
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(rule Esplit_signature_Cons_not_empty_setA2)
      apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_elem_def)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = list!SSX" for SSX)
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = list ! (k - Suc (length S1))")
   apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
   apply(rule Esplit_signature_Cons_not_empty_setA2)
     apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a list)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL S2 A w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac k Aa i j S1 SL S2 A a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL S2 A a)(*strict*)
   apply(simp add: Xstep_mergeL_def)
   apply(simp add: Xstep_gen_def)
   apply(case_tac S2)
    apply(rename_tac k Aa i j S1 SL S2 A a)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa i j S1 SL A a)(*strict*)
    apply(simp add: nth_opt_def)
    apply(simp add: Xstep_gen_def)
    apply(simp add: Xstep_elem_def)
    apply(simp add: nth_opt_def)
   apply(rename_tac k Aa i j S1 SL S2 A a aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a]\<rparr>], ESplitItem_elem := nth_opt [a] 0\<rparr> # aa # list) ! k = (aa#list)!SSX" for SSX)
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a]\<rparr>], ESplitItem_elem := nth_opt [a] 0\<rparr> # aa # list) ! k = (aa # list) ! (k - Suc (length S1))")
   apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
   apply(case_tac "k-Suc(length S1)")
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    apply(clarsimp)
    apply(rule Esplit_signature_Cons_not_empty_setA)
     apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a aa list nat)(*strict*)
   apply(clarsimp)
   apply(rule Esplit_signature_Cons_not_empty_setA2)
     apply(rename_tac k Aa i j S1 SL A a aa list nat)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a aa list nat)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a aa list nat)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL S2 A a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A a aa lista)(*strict*)
  apply(subgoal_tac "lista=[]")
   apply(rename_tac k Aa i j S1 SL S2 A a aa lista)(*strict*)
   prefer 2
   apply(rule LR1_at_most_two_symbols)
    apply(rename_tac k Aa i j S1 SL S2 A a aa lista)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL S2 A a aa lista)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL S2 A a aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A a aa)(*strict*)
  apply(case_tac aa)
   apply(rename_tac k Aa i j S1 SL S2 A a aa ab)(*strict*)
   prefer 2
   apply(rename_tac k Aa i j S1 SL S2 A a aa b)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL S2 A a b)(*strict*)
   apply(rule LR1_terminal_only_at_front_in_prods)
    apply(rename_tac k Aa i j S1 SL S2 A a b)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL S2 A a b)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL S2 A a aa ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A a ab)(*strict*)
  apply(simp add: Xstep_mergeL_def)
  apply(simp add: Xstep_gen_def)
  apply(subgoal_tac "nat_seq 0 0 = [0]")
   apply(rename_tac k Aa i j S1 SL S2 A a ab)(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac k Aa i j S1 SL S2 A a ab)(*strict*)
  apply(case_tac S2)
   apply(rename_tac k Aa i j S1 SL S2 A a ab)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(subgoal_tac "(S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA ab]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := ab # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ab, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ab), ESplitItem_to = []\<rparr>]) ! k = [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA ab]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := ab # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ab, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ab), ESplitItem_to = []\<rparr>] ! SSX" for SSX)
    apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a ab)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a)(*strict*)
   apply(subgoal_tac "k=Suc(length S1)")
    apply(rename_tac k Aa i j S1 SL A a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa i j S1 SL A a)(*strict*)
   apply(subgoal_tac "(S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA Aa]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := Aa # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some Aa, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA Aa), ESplitItem_to = []\<rparr>]) ! i = [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA Aa]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := Aa # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some Aa, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA Aa), ESplitItem_to = []\<rparr>]!SSX" for SSX)
    apply(rename_tac Aa i j S1 SL A a)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac Aa i j S1 SL A a)(*strict*)
      apply(force)
     apply(rename_tac Aa i j S1 SL A a)(*strict*)
     apply(force)
    apply(rename_tac Aa i j S1 SL A a)(*strict*)
    apply(force)
   apply(rename_tac Aa i j S1 SL A a)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL S2 A a ab aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
  apply(simp add: nth_opt_def)
  apply(simp add: Xstep_gen_def)
  apply(simp add: Xstep_elem_def)
  apply(simp add: nth_opt_def)
  apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA ab]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := ab # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ab, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ab), ESplitItem_to = []\<rparr> # aa # list) ! k = (SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA ab]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := ab # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ab, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ab), ESplitItem_to = []\<rparr> # aa # list)!SSX" for SSX)
   apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
   prefer 2
   apply(rule nth_append_2_prime)
     apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
  apply(case_tac "k-length S1")
   apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL A a ab aa list nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac k Aa i j S1 SL A a ab aa list nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
   apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA Aa]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := Aa # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some Aa, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA Aa), ESplitItem_to = []\<rparr> # aa # list) ! i = (SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [a, teA Aa]\<rparr>], ESplitItem_elem := Some a, ESplitItem_to := Aa # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some Aa, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA Aa), ESplitItem_to = []\<rparr> # aa # list)!SSX" for SSX)
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i j S1 SL A a aa list nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac ka k Aa i j S1 SL A a aa list nata)(*strict*)
  apply(case_tac nata)
   apply(rename_tac k Aa i j S1 SL A a ab aa list nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
   apply(rule Esplit_signature_Cons_not_empty_setA)
    apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a ab aa list)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL A a ab aa list nata nat)(*strict*)
  apply(rule Esplit_signature_Cons_not_empty_setA2)
    apply(rename_tac k Aa i j S1 SL A a ab aa list nata nat)(*strict*)
    apply(force)
   apply(rename_tac k Aa i j S1 SL A a ab aa list nata nat)(*strict*)
   apply(force)
  apply(rename_tac k Aa i j S1 SL A a ab aa list nata nat)(*strict*)
  apply(force)
  done

lemma Esplit_signature_split: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit_signature S = w @ v
  \<Longrightarrow> (\<forall>x. strict_prefix x S \<longrightarrow> length (Esplit_signature x) = length x )
  \<Longrightarrow> length (Esplit_signature S) = length S \<or> Suc(length (Esplit_signature S)) = length S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> \<exists>Sw Sv SL. length Sw = length w \<and> Esplit_signature Sw = w \<and> Esplit_signature Sv = v \<and> length Sv = length v \<and> Esplit_signature SL = []
  \<and> length SL \<le> Suc 0 \<and> S = Sw@Sv@SL"
  apply(induct w arbitrary: v S)
   apply(rename_tac v S)(*strict*)
   apply(clarsimp)
   apply(rename_tac S)(*strict*)
   apply(rule conjI)
    apply(rename_tac S)(*strict*)
    apply(simp add: Esplit_signature_def)
   apply(rename_tac S)(*strict*)
   apply(erule disjE)
    apply(rename_tac S)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="S"
      in exI)
    apply(clarsimp)
    apply(simp add: Esplit_signature_def)
   apply(rename_tac S)(*strict*)
   apply(rule_tac
      x="butlast S"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      xs="S"
      in rev_cases)
    apply(rename_tac S)(*strict*)
    apply(clarsimp)
   apply(rename_tac S ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac ys y)(*strict*)
   apply (simp add: Esplit_signature_append)
   apply(erule_tac
      x="ys"
      in allE)
   apply(simp add: strict_prefix_def)
  apply(rename_tac a w v S)(*strict*)
  apply(clarsimp)
  apply(case_tac S)
   apply(rename_tac a w v S)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v S aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w v aa list)(*strict*)
  apply(erule_tac
      x="v"
      in meta_allE)
  apply(erule_tac
      x="list"
      in meta_allE)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a w v aa list)(*strict*)
   prefer 2
   apply (rule_tac
      w="aa"
      and v="list"
      in Esplit_signature_Cons)
  apply(rename_tac a w v aa list)(*strict*)
  apply(subgoal_tac "Esplit_signature [aa] @ Esplit_signature list = a#w@v")
   apply(rename_tac a w v aa list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a w v aa list)(*strict*)
  apply(thin_tac "Esplit_signature (aa # list) = Esplit_signature [aa] @ Esplit_signature list")
  apply(thin_tac "Esplit_signature (aa # list) = a # w @ v")
  apply(case_tac "ESplitItem_elem aa")
   apply(rename_tac a w v aa list)(*strict*)
   apply(subgoal_tac "list=[]")
    apply(rename_tac a w v aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac a aa)(*strict*)
    apply(rule_tac
      x="[aa]"
      in exI)
    apply(simp add: Esplit_signature_def option_to_list_def)
   apply(rename_tac a w v aa list)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(rule_tac
      xs="list"
      in rev_cases)
    apply(rename_tac a w v aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w v aa list ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v aa list ab)(*strict*)
  apply(subgoal_tac "Esplit_signature [aa] = [ab]")
   apply(rename_tac a w v aa list ab)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def option_to_list_def)
  apply(rename_tac a w v aa list ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w v aa list)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a w v aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w v aa list x)(*strict*)
   apply(erule_tac
      x="aa#x"
      in allE)
   apply(simp add: strict_prefix_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a w v aa list x)(*strict*)
    prefer 2
    apply (rule_tac
      w="aa"
      and v="x"
      in Esplit_signature_Cons)
   apply(rename_tac a w v aa list x)(*strict*)
   apply(force)
  apply(rename_tac a w v aa list)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a w v aa list)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(clarsimp)
   apply(rename_tac a w v aa list x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac a w v aa list x)(*strict*)
    apply(force)
   apply(rename_tac a w v aa list x)(*strict*)
   apply(rule_tac
      xs="list"
      in rev_cases)
    apply(rename_tac a w v aa list x)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w v aa list x ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a aa Sw Sv SL)(*strict*)
  apply(rule_tac
      x="aa#Sw"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="Esplit_signature (aa # Sw)"
      in ssubst)
   apply(rename_tac a aa Sw Sv SL)(*strict*)
   apply (rule_tac
      w="aa"
      and v="Sw"
      in Esplit_signature_Cons)
  apply(rename_tac a aa Sw Sv SL)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="Sv"
      in exI)
  apply(clarsimp)
  done

lemma Esplit_signature_length: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> strict_prefix x S
  \<Longrightarrow> length (Esplit_signature x) = length x"
  apply(induct x arbitrary: S)
   apply(rename_tac S)(*strict*)
   apply(clarsimp)
   apply(simp add: Esplit_signature_def)
  apply(rename_tac a x S)(*strict*)
  apply(clarsimp)
  apply(case_tac S)
   apply(rename_tac a x S)(*strict*)
   apply(clarsimp)
   apply(rename_tac a x)(*strict*)
   apply(simp add: strict_prefix_def)
  apply(rename_tac a x S aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a x aa list)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac x aa c)(*strict*)
  apply(erule_tac
      x="x@c"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x aa c)(*strict*)
   apply(simp add: EValidSplit_producing_def)
  apply(rename_tac x aa c)(*strict*)
  apply(rule_tac
      t="Esplit_signature (aa # x)"
      in ssubst)
   apply(rename_tac x aa c)(*strict*)
   apply (rule_tac
      w="aa"
      and v="x"
      in Esplit_signature_Cons)
  apply(rename_tac x aa c)(*strict*)
  apply(clarsimp)
  apply(simp add: EValidSplit_producing_def)
  apply(clarsimp)
  apply(rename_tac x aa c y ya)(*strict*)
  apply(simp add: Esplit_signature_def option_to_list_def)
  done

lemma no_pre_DT_revert_position_hlp2: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit_signature S = w @ v @ teA A # liftB \<alpha>
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> \<exists>Sw Sv SA S\<alpha>. S = Sw @ Sv @ SA # S\<alpha> \<and> Esplit_signature Sw = w \<and> length Sw = length (Esplit_signature Sw) \<and> Esplit_signature Sv = v \<and> length Sv = length (Esplit_signature Sv) \<and> Esplit_signature [SA] = [teA A] \<and> Esplit_signature S\<alpha> = liftB \<alpha>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      w="w"
      in Esplit_signature_split)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rename_tac x)(*strict*)
     apply(simp add: strict_prefix_def)
     apply(clarsimp)
     apply(rename_tac x c)(*strict*)
     apply(rule_tac
      xs="c"
      in rev_cases)
      apply(rename_tac x c)(*strict*)
      apply(clarsimp)
     apply(rename_tac x c ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ys y)(*strict*)
     apply(rule Esplit_signature_length)
        apply(rename_tac x ys y)(*strict*)
        apply(force)
       apply(rename_tac x ys y)(*strict*)
       apply(force)
      apply(rename_tac x ys y)(*strict*)
      apply(simp add: EValidSplit_def)
      apply(force)
     apply(rename_tac x ys y)(*strict*)
     apply(simp add: strict_prefix_def)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac
      S'="[]"
      in EValidSplit_Esplit_signature_length)
     apply(force)
    apply(force)
   apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(rename_tac Sw Sv SL)(*strict*)
  apply (simp add: Esplit_signature_append)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Sw Sv SL)(*strict*)
   prefer 2
   apply(rule_tac
      w="v"
      in Esplit_signature_split)
        apply(rename_tac Sw Sv SL)(*strict*)
        apply(force)
       apply(rename_tac Sw Sv SL)(*strict*)
       apply(force)
      apply(rename_tac Sw Sv SL)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SL)(*strict*)
     apply(clarsimp)
     apply(rename_tac Sw Sv SL x)(*strict*)
     apply(rule Esplit_signature_length)
        apply(rename_tac Sw Sv SL x)(*strict*)
        apply(force)
       apply(rename_tac Sw Sv SL x)(*strict*)
       apply(force)
      apply(rename_tac Sw Sv SL x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac Sw Sv SL x)(*strict*)
     apply(simp add: EValidSplit_def EValidSplit_producing_def)
     apply(clarsimp)
     apply(rename_tac Sw Sv SL x xa)(*strict*)
     apply(erule_tac
      x="xa"
      in ballE)
      apply(rename_tac Sw Sv SL x xa)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SL x xa)(*strict*)
     apply(subgoal_tac "xa \<in> set (butlast (Sw @ Sv @ SL))")
      apply(rename_tac Sw Sv SL x xa)(*strict*)
      apply(force)
     apply(rename_tac Sw Sv SL x xa)(*strict*)
     apply(rule in_set_butlast_appendI)
     apply(rule disjI2)
     apply(rule in_set_butlast_appendI)
     apply(rule disjI1)
     apply(force)
    apply(rename_tac Sw Sv SL)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac Sw Sv SL)(*strict*)
     prefer 2
     apply(rule_tac
      S'="[]"
      in EValidSplit_Esplit_signature_length)
     apply(force)
    apply(rename_tac Sw Sv SL)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SL)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(rename_tac Sw Sv SL x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac Sw Sv SL x)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SL x)(*strict*)
   apply(subgoal_tac "x \<in> set (butlast (Sw @ Sv @ SL))")
    apply(rename_tac Sw Sv SL x)(*strict*)
    apply(force)
   apply(rename_tac Sw Sv SL x)(*strict*)
   apply(rule in_set_butlast_appendI)
   apply(rule disjI2)
   apply(rule in_set_butlast_appendI)
   apply(rule disjI1)
   apply(force)
  apply(rename_tac Sw Sv SL)(*strict*)
  apply(clarsimp)
  apply(rename_tac Sw SL Swa Sva)(*strict*)
  apply(rule_tac
      x="Sw"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="Swa"
      in exI)
  apply(clarsimp)
  apply (simp add: Esplit_signature_append)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Sw SL Swa Sva)(*strict*)
   prefer 2
   apply(rule_tac
      w="[teA A]"
      in Esplit_signature_split)
        apply(rename_tac Sw SL Swa Sva)(*strict*)
        apply(force)
       apply(rename_tac Sw SL Swa Sva)(*strict*)
       apply(force)
      apply(rename_tac Sw SL Swa Sva)(*strict*)
      apply(force)
     apply(rename_tac Sw SL Swa Sva)(*strict*)
     apply(clarsimp)
     apply(rename_tac Sw SL Swa Sva x)(*strict*)
     apply(rule Esplit_signature_length)
        apply(rename_tac Sw SL Swa Sva x)(*strict*)
        apply(force)
       apply(rename_tac Sw SL Swa Sva x)(*strict*)
       apply(force)
      apply(rename_tac Sw SL Swa Sva x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac Sw SL Swa Sva x)(*strict*)
     apply(simp add: EValidSplit_def EValidSplit_producing_def)
     apply(clarsimp)
     apply(rename_tac Sw SL Swa Sva x xa)(*strict*)
     apply(erule_tac
      x="xa"
      in ballE)
      apply(rename_tac Sw SL Swa Sva x xa)(*strict*)
      apply(force)
     apply(rename_tac Sw SL Swa Sva x xa)(*strict*)
     apply(subgoal_tac "xa \<in> set (butlast (Sw @ Swa @ Sva @ SL))")
      apply(rename_tac Sw SL Swa Sva x xa)(*strict*)
      apply(force)
     apply(rename_tac Sw SL Swa Sva x xa)(*strict*)
     apply(rule in_set_butlast_appendI)
     apply(rule disjI2)
     apply(rule in_set_butlast_appendI)
     apply(rule disjI2)
     apply(rule in_set_butlast_appendI)
     apply(rule disjI1)
     apply(force)
    apply(rename_tac Sw SL Swa Sva)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac Sw SL Swa Sva)(*strict*)
     prefer 2
     apply(rule_tac
      S'="[]"
      in EValidSplit_Esplit_signature_length)
     apply(force)
    apply(rename_tac Sw SL Swa Sva)(*strict*)
    apply(force)
   apply(rename_tac Sw SL Swa Sva)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(rename_tac Sw SL Swa Sva x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac Sw SL Swa Sva x)(*strict*)
    apply(force)
   apply(rename_tac Sw SL Swa Sva x)(*strict*)
   apply(subgoal_tac "x \<in> set (butlast (Sw @ Swa @ Sva @ SL))")
    apply(rename_tac Sw SL Swa Sva x)(*strict*)
    apply(force)
   apply(rename_tac Sw SL Swa Sva x)(*strict*)
   apply(rule in_set_butlast_appendI)
   apply(rule disjI2)
   apply(rule in_set_butlast_appendI)
   apply(rule disjI2)
   apply(rule in_set_butlast_appendI)
   apply(rule disjI1)
   apply(force)
  apply(rename_tac Sw SL Swa Sva)(*strict*)
  apply(clarsimp)
  apply(rename_tac Sw SL Swa Swb Sv)(*strict*)
  apply(case_tac Swb)
   apply(rename_tac Sw SL Swa Swb Sv)(*strict*)
   apply(clarsimp)
  apply(rename_tac Sw SL Swa Swb Sv a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac Sw SL Swa Sv a)(*strict*)
  apply (simp add: Esplit_signature_append)
  done

hide_fact cfgRM_derivation_to_Esplit_derivation_hlp
hide_fact Esplit_inst_AX_initial_configuration_belongs
hide_fact Esplit_inst_AX_step_relation_preserves_belongs
hide_fact Esplit_inst_AX_step_relation_preserves_belongs1
hide_fact Esplit_inst_AX_step_relation_preserves_belongs2
hide_fact Esplit_inst_AX_step_relation_preserves_belongs3
hide_fact Esplit_inst_AX_step_relation_preserves_belongs4
hide_fact Esplit_signature_distrib_drop
hide_fact Esplit_signature_drop_eq_prime
hide_fact Esplit_signature_notwhere_None
hide_fact Esplit_signature_single_not_empty_setA
hide_fact Esplit_signature_split
hide_fact Esplit_signature_take_eq
hide_fact Esplit_signature_take_eq_prime
hide_fact EValidSplit_interline_enlarge
hide_fact EValidSplit_interline_preserve
hide_fact EValidSplit_interline_shrink
  (* important cfgRM_derivation_to_Esplit_derivation *)
  (* important e_derivation_at_tail_exists *)
  (* important ESplit_cfgRM_step_can_be_simulated *)
  (* important Esplit_derivation_enforces_EValidSplitExt_no_elim_before_nonterminal *)
  (* important Esplit_derivation_enforces_EValidSplitExt_no_pop_in_prods_before_nonterminal *)
  (* important ESplitItem_to_not_empty_on_generating_line *)
  (* important Esplit_signature_append *)
  (* important Esplit_signature_belongs_setA *)
  (* important Esplit_signature_belongs_setB *)
  (* important Esplit_signature_Cons *)
  (* important Esplit_signature_Cons_not_empty_setA *)
  (* important Esplit_signature_Cons_not_empty_setA2 *)
  (* important Esplit_signature_length *)
  (* important Esplit_signature_length_max *)
  (* important Esplit_signature_take_prefix_closureise *)
  (* important Esplit_signature_take_prefix_closureise2 *)
  (* important EValidSplit_construct_derivation *)
  (* important EValidSplit_continuation_not_empty *)
  (* important EValidSplit_DERIVED_l3_produce_produces_to *)
  (* important EValidSplit_DERIVED_terminal_produce_produces_to *)
  (* important EValidSplit_Esplit_signature_length *)
  (* important EValidSplit_take_prefix *)
  (* important no_pre_DT_revert_position_hlp2 *)
  (* important trans_der_list_construct_elimininating_derivation_prime *)
  (* important Xstep_gen_length *)

end
