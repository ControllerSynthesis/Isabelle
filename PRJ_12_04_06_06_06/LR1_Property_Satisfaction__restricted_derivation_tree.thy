section {*LR1\_Property\_Satisfaction\_\_restricted\_derivation\_tree*}
theory
  LR1_Property_Satisfaction__restricted_derivation_tree

imports
  PRJ_12_04_06_06_06__ENTRY

begin

record ('q,'s,'t) PSplitItem =
  PSplitItem_elim :: "('q,'s) DT_l2_l3_nonterminals list"
  PSplitItem_from :: "('q,'s) DT_l2_l3_nonterminals"
  PSplitItem_ignore :: "('q,'s) DT_l2_l3_nonterminals list"
  PSplitItem_elim_prods :: "(('q,'s) DT_l2_l3_nonterminals, 't) cfg_step_label list list"
  PSplitItem_prods :: "(('q, 't, 's) epda_step_label,(('q,'s) DT_l2_l3_nonterminals, 't) cfg_step_label)DT_two_elements list"
  PSplitItem_elem :: "(('q,'s) DT_l2_l3_nonterminals, 't) DT_two_elements"
  PSplitItem_to :: "('q,'s) DT_l2_l3_nonterminals list"

type_synonym ('q,'s,'t) PSplit = "('q,'s,'t) PSplitItem list"

definition PValidSplitItem_belongs :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "PValidSplitItem_belongs G' G S \<equiv>
   ( set (PSplitItem_elim S) \<subseteq> cfg_nonterminals G
  \<and> ((\<exists>q. set (fillL (PSplitItem_ignore S) q) \<subseteq> cfg_nonterminals G) \<or> (set ((PSplitItem_ignore S)) \<subseteq> cfg_nonterminals G))
  \<and> ((\<exists>q. (fill (PSplitItem_from S) q) \<in> cfg_nonterminals G) \<or> (((PSplitItem_from S)) \<in> cfg_nonterminals G))
  \<and> ((\<exists>q. set (fillL (PSplitItem_to S) q) \<subseteq> cfg_nonterminals G) \<or> (set ((PSplitItem_to S)) \<subseteq> cfg_nonterminals G))
  \<and> setA [PSplitItem_elem S] \<subseteq> cfg_nonterminals G
  \<and> setB [PSplitItem_elem S] \<subseteq> cfg_events G
  \<and> setB ((PSplitItem_prods S)) \<subseteq> cfg_productions G
  \<and> setA ((PSplitItem_prods S)) \<subseteq> epda_delta G'
  \<and> (\<forall>x\<in> set (PSplitItem_elim_prods S) . set x \<subseteq> cfg_productions G)
  \<and> proper_l3_l2_seq (PSplitItem_elim S @ [PSplitItem_from S] @ PSplitItem_ignore S)
  \<and> (filterA ([PSplitItem_elem S]) @ (PSplitItem_to S) @ (PSplitItem_ignore S) \<noteq> [] \<longrightarrow> proper_l3_l2_seq (filterA ([PSplitItem_elem S]) @ (PSplitItem_to S) @ (PSplitItem_ignore S))) )"

definition PValidSplitItem_elim :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "PValidSplitItem_elim G S \<equiv>
  length (PSplitItem_elim_prods S) = length (PSplitItem_elim S)
  \<and> elim_map G (PSplitItem_elim S) (PSplitItem_elim_prods S) (map (\<lambda>x.[]) (PSplitItem_elim_prods S))"

definition PValidSplitItem_gen :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "PValidSplitItem_gen G' G S \<equiv>
  \<exists>\<pi> d q c q1 q2 q3. 
    concretization G' (PSplitItem_prods S) \<pi>
    \<and> cfgLM.trans_der G d 
          \<lparr>cfg_conf = [teA (fillOpt (PSplitItem_from S) q)]\<rparr> 
          \<pi> 
          \<lparr>cfg_conf = fillWithContext (PSplitItem_elem S) (PSplitItem_to S) c q1 q2 q3\<rparr>
    \<and> ValidContext (PSplitItem_elem S) (PSplitItem_to S) c (PSplitItem_ignore S) q1 q2 q3
    \<and> ((\<exists>b. (teB b) = PSplitItem_elem S)
          \<longrightarrow> (\<forall>i < length \<pi>. 
                hd (cfg_conf (the (get_configuration (d i)))) \<noteq> PSplitItem_elem S))
    \<and> ((\<exists>A. (teA A) = PSplitItem_elem S) 
          \<longrightarrow> left_degen G d \<and> (PSplitItem_elim_prods S) = [])"

definition PValidSplit_interlineX :: "
  ('q, 's, 't) PSplitItem
  \<Rightarrow> ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "PValidSplit_interlineX S1 S2 \<equiv>
  PSplitItem_elim S2 @ [PSplitItem_from S2] @ PSplitItem_ignore S2 = PSplitItem_to S1 @ PSplitItem_ignore S1"

definition PValidSplit_interline :: "
  ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit_interline S \<equiv>
  \<forall>i. Suc i < length S \<longrightarrow> PValidSplit_interlineX (S ! i) (S ! Suc i)"

definition PValidSplitItem :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplitItem
  \<Rightarrow> bool"
  where
    "PValidSplitItem G' G S \<equiv>
  PValidSplitItem_belongs G' G S
  \<and> PValidSplitItem_elim G S
  \<and> PValidSplitItem_gen G' G S"

definition PValidSplit_ValidItem :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit_ValidItem G' G S \<equiv>
  \<forall>x \<in> set S. PValidSplitItem G' G x"

definition PValidSplit_initial :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit_initial G S \<equiv>
  PSplitItem_elim (hd S) = []
  \<and> PSplitItem_from (hd S) = (cfg_initial G)
  \<and> PSplitItem_ignore (hd S) = []"

definition PValidSplit_to_empty :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit_to_empty G S \<equiv>
  \<forall>x \<in> set S. 
    PSplitItem_to x = [] \<longrightarrow> 
      PSplitItem_prods x = [] \<and> [PSplitItem_elem x] = liftA [PSplitItem_from x]"

definition PValidSplit_final :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit_final G S \<equiv>
  PSplitItem_to (last S) @ PSplitItem_ignore (last S) \<noteq> []"

definition PValidSplit :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> bool"
  where
    "PValidSplit G' G S \<equiv>
  PValidSplit_interline S
  \<and> S \<noteq> []
  \<and> PValidSplit_initial G S
  \<and> PValidSplit_to_empty G S
  \<and> PValidSplit_final G S
  \<and> PValidSplit_ValidItem G' G S"

definition Psplit_signature :: "
  ('q, 'a, 'b) PSplit
  \<Rightarrow> (('q, 'a) DT_l2_l3_nonterminals, 'b) DT_two_elements list"
  where
    "Psplit_signature S \<equiv>
  map PSplitItem_elem S"

end

