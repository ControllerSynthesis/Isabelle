section {*LR1\_Property\_Satisfaction\_\_convert\_remaining\_productions*}
theory
  LR1_Property_Satisfaction__convert_remaining_productions

imports
  PRJ_12_04_06_06_10__ENTRY

begin

definition restrictX :: "
  ('q, 't, 's) epda
  \<Rightarrow> ('q, 's, 't) PSplit
  \<Rightarrow> ('q, 's, 't) PSplit"
  where
    "restrictX G' S \<equiv>
  map
    (\<lambda>I. I \<lparr>PSplitItem_prods :=
              map
                (\<lambda>X. case X of
                       teB p \<Rightarrow> teA (prod_to_edge G' p)
                       | teA p \<Rightarrow> teA p) (PSplitItem_prods I)\<rparr>)
    S"

lemma restrictX_length: "
  length (restrictX G' S) = length S"
  apply(simp add: restrictX_def)
  done

lemma equal_split_prefix_hlp1_updated: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=v@[teB b]@x1\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=v@[teB b]@x2\<rparr>)
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> EValidSplit G (S2@S2')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> length S2 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> v@[teB b] = Esplit_signature S2
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> x2 = Esplit_signature S2'
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> S2R=restrict G' G (S2@S2') (length (v@[teB b]))
  \<Longrightarrow> S1RX=restrictX G' S1R
  \<Longrightarrow> S2RX=restrictX G' S2R
  \<Longrightarrow> ESplitItem_elem ((S1@S1') ! (length v)) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S1R
  \<Longrightarrow> ESplitItem_elem ((S2@S2') ! (length v)) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S2R
  \<Longrightarrow> i\<le>length (v@[teB b])
  \<Longrightarrow> take i S1RX = take i S2RX"
  apply(induct i rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(case_tac x)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="take (Suc n) (restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1))))"
      and s="take n (restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1))))@[(restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1))))!n]"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule take_Suc_conv_app_nth)
   apply(rule_tac
      t="length (restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1))))"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule restrictX_length)
   apply(rename_tac n)(*strict*)
   apply (metis Suc_le_lessD append_length_inc length_Suc length_of_restrict take_n_vs_take_Suc_n zero_less_Suc)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="take (Suc n) (restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S1))))"
      and s="take n (restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S1))))@[(restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S1))))!n]"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule take_Suc_conv_app_nth)
   apply(rule_tac
      t="length (restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S1))))"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule restrictX_length)
   apply(rename_tac n)(*strict*)
   apply (metis Suc_le_lessD append_length_inc length_Suc length_of_restrict take_n_vs_take_Suc_n zero_less_Suc)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) )! n = restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S1))) ! n")
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(simp (no_asm) add: restrictX_def restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(case_tac "length (Esplit_signature S1)")
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac k)
  apply(rename_tac n k)(*strict*)
  apply(subgoal_tac "length(nat_seq 0 k) = SSx" for SSx)
   apply(rename_tac n k)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac n k)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 k ! n = SSX" for SSX)
   apply(rename_tac n k)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac n k)(*strict*)
    apply(force)
   apply(rename_tac n k)(*strict*)
   apply(force)
  apply(rename_tac n k)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newelem_def)
  apply(subgoal_tac "k = length v")
   apply(rename_tac n k)(*strict*)
   prefer 2
   apply(subgoal_tac "Suc k = length(v@[teB b])")
    apply(rename_tac n k)(*strict*)
    apply(rule Suc_inject)
    apply(rule_tac
      t="Suc k"
      and s="length(v@[teB b])"
      in ssubst)
     apply(rename_tac n k)(*strict*)
     apply(force)
    apply(rename_tac n k)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac n k)(*strict*)
   apply(subgoal_tac "length SSS = length (Esplit_signature S1) \<or> length SSS = Suc (length (Esplit_signature SSS)) \<and> S1' = []" for SSS)
    apply(rename_tac n k)(*strict*)
    prefer 2
    apply(rule EValidSplit_Esplit_signature_length)
    apply(force)
   apply(rename_tac n k)(*strict*)
   apply(erule disjE)
    apply(rename_tac n k)(*strict*)
    apply(rule_tac
      t="Suc k"
      and s="length S1"
      in ssubst)
     apply(rename_tac n k)(*strict*)
     apply(force)
    apply(rename_tac n k)(*strict*)
    apply(rule_tac
      t="v@[teB b]"
      and s="Esplit_signature S1"
      in ssubst)
     apply(rename_tac n k)(*strict*)
     apply(force)
    apply(rename_tac n k)(*strict*)
    apply(force)
   apply(rename_tac n k)(*strict*)
   apply(force)
  apply(rename_tac n k)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac " ESplitItem_elem (S1 ! n) = Some ((v@[teB b])!n) \<and> ESplitItem_elem (S2 ! n) = Some ((v@[teB b])!n) ")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac n)(*strict*)
    apply(rule Esplit_signature_take_prefix_closureise)
      apply(rename_tac n)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule Esplit_signature_take_prefix_closureise)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac " let S1nr=restrict G' G (S1 @ S1') (Suc (length v)) ! n; S2nr=restrict G' G (S2 @ S2') (Suc (length v)) ! n in PSplitItem_elim S1nr @ [PSplitItem_from S1nr] @ PSplitItem_ignore S1nr = PSplitItem_elim S2nr @ [PSplitItem_from S2nr] @ PSplitItem_ignore S2nr ")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: Let_def)
   apply(case_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(simp add: PValidSplit_def PValidSplit_initial_def)
    apply(clarsimp)
    apply(case_tac "restrict G' G (S1 @ S1') (Suc (length v))")
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(case_tac "restrict G' G (S2 @ S2') (Suc (length v))")
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac n nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "restrictX G' (restrict G' G (S1 @ S1') (Suc (length v))) ! nat = restrictX G' (restrict G' G (S2 @ S2') (Suc (length v))) ! nat")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule_tac
      n="Suc nat"
      and m="Suc nat"
      in nth_equal_by_take_equal)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(thin_tac "take (Suc nat) (restrictX G' (restrict G' G (S1 @ S1') (Suc (length v)))) = take (Suc nat) (restrictX G' (restrict G' G (S2 @ S2') (Suc (length v))))")
   apply(rename_tac nat)(*strict*)
   apply(rename_tac n)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "PValidSplit_interlineX (restrict G' G (S1 @ S1') (Suc (length v)) ! n) (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)\<and> PValidSplit_interlineX (restrict G' G (S2 @ S2') (Suc (length v)) ! n) (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp add: PValidSplit_def PValidSplit_interline_def)
    apply(clarsimp)
    apply(erule_tac
      x="n"
      in allE)+
    apply(erule_tac
      P="Suc n < length (restrict G' G (S1 @ S1') (Suc (length v)))"
      in impE)
     apply(rename_tac n)(*strict*)
     apply(simp add: restrict_def restrict_len_def restrict_map_def restrictX_def)
    apply(rename_tac n)(*strict*)
    apply(erule impE)
     apply(rename_tac n)(*strict*)
     apply(simp add: restrict_def restrict_len_def restrict_map_def restrictX_def)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(simp add: PValidSplit_interlineX_def)
   apply(simp add: restrict_def restrict_len_def restrict_map_def restrictX_def)
  apply(rename_tac n)(*strict*)
  apply(simp add: Let_def)
  apply(subgoal_tac "ESplitItem_elim_prods (S2 ! n) = PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(rule_tac
      t="map (\<lambda>i. \<lparr>PSplitItem_elim = ESplitItem_elim ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i)) # restrict_newignore (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i)), PSplitItem_ignore = restrict_newignore (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_elim_prods = ESplitItem_elim_prods ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i), PSplitItem_prods = restrict_newprods G' G (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_elem = restrict_newelem (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_to = restrict_newto (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i\<rparr>) (nat_seq 0 (min (length S2) (Suc (length v)) + min (length S2') (Suc (length v) - length S2) - Suc 0)) ! n"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "ESplitItem_elim_prods (S1 ! n) = PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(rule_tac
      t="map (\<lambda>i. \<lparr>PSplitItem_elim = ESplitItem_elim ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i)) # restrict_newignore (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i)), PSplitItem_ignore = restrict_newignore (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_elim_prods = ESplitItem_elim_prods ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! i), PSplitItem_prods = restrict_newprods G' G (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_elem = restrict_newelem (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i, PSplitItem_to = restrict_newto (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') i\<rparr>) (nat_seq 0 (min (length S2) (Suc (length v)) + min (length S2') (Suc (length v) - length S2) - Suc 0)) ! n"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! n) = ESplitItem_elim (S2 ! n) \<and> ESplitItem_elim_prods (S1 ! n) = ESplitItem_elim_prods (S2 ! n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(subgoal_tac "ESplitItem_elim (S1 ! n) = PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "ESplitItem_elim (S2 ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_elem (S1 ! n) = Some (PSplitItem_elem (restrict G' G (S1 @ S1') (Suc (length v)) ! n))")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def PValidSplit_def)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "ESplitItem_elem (S2 ! n) = Some (PSplitItem_elem (restrict G' G (S2 @ S2') (Suc (length v)) ! n))")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def PValidSplit_def)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(case_tac "ESplitItem_elem (S1 ! n)")
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n a)(*strict*)
   apply(case_tac a)
    apply(rename_tac n a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n aa)(*strict*)
    apply(rename_tac A)
    apply(rename_tac n A)(*strict*)
    apply(subgoal_tac "EValidSplitItem G (S1 ! n)")
     apply(rename_tac n A)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(rename_tac n A)(*strict*)
    apply(subgoal_tac "EValidSplitItem G (S2 ! n)")
     apply(rename_tac n A)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(rename_tac n A)(*strict*)
    apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac n A d da)(*strict*)
    apply(thin_tac "(\<exists>b. teB b = Esplit_signature S1 ! n) \<longrightarrow> (\<forall>i<length (ESplitItem_prods (S2 ! n)). hd (cfg_conf (the (get_configuration (da i)))) \<noteq> Esplit_signature S1 ! n)")
    apply(rename_tac n A d da)(*strict*)
    apply(thin_tac "(\<exists>b. teB b = Esplit_signature S1 ! n) \<longrightarrow> (\<forall>i<length (ESplitItem_prods (S1 ! n)). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> Esplit_signature S1 ! n)")
    apply(rename_tac n A d da)(*strict*)
    apply(erule_tac
      P="\<exists>A. teA A = Esplit_signature S1 ! n"
      and Q="left_degen G d \<and> PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = []"
      in impE)
     apply(rename_tac n A d da)(*strict*)
     apply(rule_tac
      x="A"
      in exI)
     apply(force)
    apply(rename_tac n A d da)(*strict*)
    apply(erule impE)
     apply(rename_tac n A d da)(*strict*)
     apply(rule_tac
      x="A"
      in exI)
     apply(force)
    apply(rename_tac n A d da)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplitItem_def EValidSplitItem_elim_def)
   apply(rename_tac n a ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac n ba)(*strict*)
   apply(rename_tac a)
   apply(rename_tac n a)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac n a)(*strict*)
    prefer 2
    apply(rename_tac n a)(*strict*)
    apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
     apply(rename_tac n a)(*strict*)
     prefer 2
     apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
      x="(restrict G' G (S2 @ S2') (Suc (length v))) ! n"
      and A="set (restrict G' G (S2 @ S2') (Suc (length v)))"
      in ballE)
      apply(rename_tac n a)(*strict*)
      prefer 2
      apply(subgoal_tac " (restrict G' G (S2 @ S2') (Suc (length v))) ! n \<in> set ((restrict G' G (S2 @ S2') (Suc (length v))))")
       apply(rename_tac n a)(*strict*)
       apply(force)
      apply(rename_tac n a)(*strict*)
      apply(rule nth_mem)
      apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
      apply(force)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
     apply(rename_tac n a)(*strict*)
     prefer 2
     apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
      A="set (restrict G' G (S2 @ S2') (Suc (length v)))"
      and x="restrict G' G (S1 @ S1') (Suc (length v)) ! n"
      in ballE)
      apply(rename_tac n a)(*strict*)
      prefer 2
      apply(subgoal_tac "restrict G' G (S1 @ S1') (Suc (length v)) ! n \<in> set (restrict G' G (S1 @ S1') (Suc (length v)))")
       apply(rename_tac n a)(*strict*)
       apply(force)
      apply(rename_tac n a)(*strict*)
      apply(rule nth_mem)
      apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
      apply(force)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(subgoal_tac "PValidSplitItem_elim G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
     apply(rename_tac n a)(*strict*)
     prefer 2
     apply(simp add: PValidSplitItem_def)
    apply(rename_tac n a)(*strict*)
    apply(subgoal_tac "PValidSplitItem_elim G (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
     apply(rename_tac n a)(*strict*)
     prefer 2
     apply(simp add: PValidSplitItem_def)
    apply(rename_tac n a)(*strict*)
    apply(simp add: PValidSplitItem_elim_def)
    apply(rename_tac n a)(*strict*)
    apply(rule_tac
      t="ESplitItem_elim_prods (S1 ! n)"
      and s="PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      in ssubst)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(rule_tac
      t="ESplitItem_elim_prods (S2 ! n)"
      and s="PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      in ssubst)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(rule_tac
      ns="PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      and v="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      in elim_map_equal_by_CFGlm_unambiguous)
            apply(rename_tac n a)(*strict*)
            apply(simp add: F2LR1inputx_def)
            apply(force)
           apply(rename_tac n a)(*strict*)
           apply(simp add: split_TSstructure_def)
          apply(rename_tac n a)(*strict*)
          apply(simp add: F2LR1inputx_def)
          apply(simp add: split_TSstructure_def)
          apply(rule cfgSTD_Nonblockingness_nonterminals_equal_cfgLM_accessible_nonterminals)
            apply(rename_tac n a)(*strict*)
            apply(force)
           apply(rename_tac n a)(*strict*)
           apply(force)
          apply(rename_tac n a)(*strict*)
          apply(force)
         apply(rename_tac n a)(*strict*)
         apply(simp add: F2LR1inputx_def)
         apply(simp add: split_TSstructure_def)
        apply(rename_tac n a)(*strict*)
        apply(force)
       apply(rename_tac n a)(*strict*)
       apply(rule_tac
      t="map (\<lambda>x. []) (PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      and s="map (\<lambda>x. []) (PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
      in ssubst)
        apply(rename_tac n a)(*strict*)
        apply(rule map_empty_eq)
        apply(rule_tac
      t="length (PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
      and s="length (PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
      in ssubst)
         apply(rename_tac n a)(*strict*)
         apply(force)
        apply(rename_tac n a)(*strict*)
        apply(rule_tac
      t="length (PSplitItem_elim_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      and s="length (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in ssubst)
         apply(rename_tac n a)(*strict*)
         apply(force)
        apply(rename_tac n a)(*strict*)
        apply(force)
       apply(rename_tac n a)(*strict*)
       apply(force)
      apply(rename_tac n a)(*strict*)
      apply(force)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(rule equal_by_strict_prefix_alt)
     apply(rename_tac n a)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(rule equal_split_prefix_hlp1_elim_eq_updated)
                      apply(rename_tac n a)(*strict*)
                      prefer 25
                      apply(force)+
   apply(rename_tac n a)(*strict*)
   apply(rule equal_split_prefix_hlp1_elim_eq_updated)
                      apply(rename_tac n a)(*strict*)
                      prefer 25
                      apply(force)+
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! n) = PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S2 ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      x="restrict G' G (S2 @ S2') (Suc (length v)) ! n"
      and A="set (restrict G' G (S2 @ S2') (Suc (length v)))"
      in ballE)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(subgoal_tac "restrict G' G (S2 @ S2') (Suc (length v)) ! n \<in> set (restrict G' G (S2 @ S2') (Suc (length v)))")
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule nth_mem)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      A="set (restrict G' G (S1 @ S1') (Suc (length v)))"
      and x="restrict G' G (S1 @ S1') (Suc (length v)) ! n"
      in ballE)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(subgoal_tac "restrict G' G (S1 @ S1') (Suc (length v)) ! n \<in> set (restrict G' G (S1 @ S1') (Suc (length v)))")
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule nth_mem)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "PSplitItem_from (restrict_map G' G (restrict_len (S1 @ S1') (Suc (length v))) ! n) = PSplitItem_from (restrict_map G' G (restrict_len (S2 @ S2') (Suc (length v))) ! n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp add: restrict_def)
   apply(rename_tac n)(*strict*)
   apply(simp add: restrict_map_def restrict_len_def PValidSplit_def)
  apply(rename_tac n)(*strict*)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "PSplitItem_ignore (restrict_map G' G (restrict_len (S1 @ S1') (Suc (length v))) ! n) = PSplitItem_ignore (restrict_map G' G (restrict_len (S2 @ S2') (Suc (length v))) ! n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp add: restrict_def)
   apply(rename_tac n)(*strict*)
   apply(simp add: restrict_map_def restrict_len_def PValidSplit_def)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "restrict_newprods G' G S1 n = PSplitItem_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "restrict_newprods G' G S2 n = PSplitItem_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "restrict_newto S1 n = PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "restrict_newto S2 n = PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "\<exists>ds \<pi>s fw. cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: cfgLMTDL_def)
   apply(subgoal_tac "\<exists>ds f\<pi> fw. cfgLM.trans_der_list SSG ds (map (\<lambda>w. \<lparr>cfg_conf = [w]\<rparr>) (Esplit_signature S1)) f\<pi> (map (\<lambda>w. \<lparr>cfg_conf = w\<rparr>) fw) \<and> setA (foldl (@) [] fw) = {}" for SSG)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule construct_elimininating_trans_der_list)
       apply(rename_tac n)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac n)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac n)(*strict*)
     apply(rule Esplit_signature_belongs_setA)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule Esplit_signature_belongs_setB)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n ds f\<pi> fw)(*strict*)
   apply(rule_tac
      x="ds"
      in exI)
   apply(rule_tac
      x="f\<pi>"
      in exI)
   apply(rule_tac
      x="map filterB fw"
      in exI)
   apply(rule_tac
      t="(map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) (map filterB fw))"
      and s="(map (\<lambda>w. \<lparr>cfg_conf = w\<rparr>) fw)"
      in ssubst)
    apply(rename_tac n ds f\<pi> fw)(*strict*)
    apply(rule listEqI)
     apply(rename_tac n ds f\<pi> fw)(*strict*)
     apply(force)
    apply(rename_tac n ds f\<pi> fw i)(*strict*)
    apply(clarsimp)
    apply (metis setA_empty_foldl liftBDeConv2)
   apply(rename_tac n ds f\<pi> fw)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(case_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)=[]")
   apply(rename_tac n ds \<pi>s fw)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac n ds \<pi>s fw)(*strict*)
    prefer 2
    apply(rule_tac
      i="n"
      and ?S1.0="S1"
      and n="length v"
      and v="v"
      and b="b"
      in e_derivation_can_be_embedded_minimally)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      prefer 2
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                     apply(rename_tac n ds \<pi>s fw)(*strict*)
                     apply(force)
                    apply(rename_tac n ds \<pi>s fw)(*strict*)
                    apply(force)
                   apply(rename_tac n ds \<pi>s fw)(*strict*)
                   apply(force)
                  apply(rename_tac n ds \<pi>s fw)(*strict*)
                  apply(force)
                 apply(rename_tac n ds \<pi>s fw)(*strict*)
                 apply(force)
                apply(rename_tac n ds \<pi>s fw)(*strict*)
                apply(force)
               apply(rename_tac n ds \<pi>s fw)(*strict*)
               apply(force)
              apply(rename_tac n ds \<pi>s fw)(*strict*)
              apply(force)
             apply(rename_tac n ds \<pi>s fw)(*strict*)
             apply(force)
            apply(rename_tac n ds \<pi>s fw)(*strict*)
            apply(force)
           apply(rename_tac n ds \<pi>s fw)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n ds \<pi>s fw)(*strict*)
    prefer 2
    apply(rule_tac
      i="n"
      and ?S1.0="S2"
      and n="length v"
      and v="v"
      and b="b"
      in e_derivation_can_be_embedded_minimally)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      prefer 2
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac n ds \<pi>s fw)(*strict*)
                      apply(force)
                     apply(rename_tac n ds \<pi>s fw)(*strict*)
                     apply(force)
                    apply(rename_tac n ds \<pi>s fw)(*strict*)
                    apply(force)
                   apply(rename_tac n ds \<pi>s fw)(*strict*)
                   apply(force)
                  apply(rename_tac n ds \<pi>s fw)(*strict*)
                  apply(force)
                 apply(rename_tac n ds \<pi>s fw)(*strict*)
                 apply(force)
                apply(rename_tac n ds \<pi>s fw)(*strict*)
                apply(force)
               apply(rename_tac n ds \<pi>s fw)(*strict*)
               apply(force)
              apply(rename_tac n ds \<pi>s fw)(*strict*)
              apply(force)
             apply(rename_tac n ds \<pi>s fw)(*strict*)
             apply(force)
            apply(rename_tac n ds \<pi>s fw)(*strict*)
            apply(force)
           apply(rename_tac n ds \<pi>s fw)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw)(*strict*)
   apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "Suc n\<le>length v")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(case_tac "n=length v")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     prefer 2
     apply(rule_tac
      n="length v"
      and S="S2"
      in restrict_newignore_last_empty)
       apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule ESplitItem_to_not_empty_on_generating_line)
         apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(subgoal_tac "restrict_newignore S2 (length v) = PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
    apply(rule_tac
      t="nat_seq 0 (length v) ! length v"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(simp (no_asm_simp))
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! n) = ESplitItem_to ((S2 @ S2') ! n)")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(rule_tac
      t="PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and s="restrict_newto (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') n"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="(S2 @ S2') ! n"
      and s="S2!n"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="length S2"
      and s="Suc (length v)"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="take (Suc (length v) - Suc (length v)) S2'"
      and s="[]"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="take (Suc (length v)) S2"
      and s="S2"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule take_all)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(simp (no_asm))
    apply(rule nonemtpy_newignore_implies_newto_unchanged)
    apply(rule_tac
      t="restrict_newignore S2 n"
      and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = ESplitItem_to ((S1 @ S1') ! n)")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(rule_tac
      t="PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      and s="restrict_newto (take (Suc (length v)) S1 @ take (Suc (length v) - length S1) S1') n"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="(S1 @ S1') ! n"
      and s="S1!n"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="length S1"
      and s="Suc (length v)"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="take (Suc (length v) - Suc (length v)) S1'"
      and s="[]"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="take (Suc (length v)) S1"
      and s="S1"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule take_all)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(simp (no_asm))
    apply(rule nonemtpy_newignore_implies_newto_unchanged)
    apply(rule_tac
      t="restrict_newignore S1 n"
      and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "restrict_newprods G' G S2 n = liftB (ESplitItem_prods (S2!n))")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(case_tac "ESplitItem_from (S2 ! n)")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(simp add: EValidSplit_def EValidSplit_producing_def)
     apply(clarsimp)
     apply(erule_tac
      x="S2!n"
      and A="set (butlast (S2 @ S2'))"
      and P="\<lambda>X. (\<exists>y. ESplitItem_from X = Some y) \<and> (\<exists>y. ESplitItem_elem X = Some y)"
      in ballE)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      prefer 2
      apply(rule in_set_butlast_append2)
       apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
    apply(subgoal_tac "EValidSplitItem_gen G (S2 ! n)")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
    apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
    apply(erule exE)+
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(erule conjE)+
    apply(rule_tac
      A="a"
      in nonemtpy_newignore_implies_newprods_unchanged)
       apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
      apply(rule_tac
      t="restrict_newignore S2 n"
      and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      in ssubst)
       apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
       apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(rule_tac
    t="the (ESplitItem_elem (S2 ! n)) # liftA (ESplitItem_to (S2 ! n))"
    and s="option_to_list (ESplitItem_elem (S2 ! n)) @ liftA (ESplitItem_to (S2 ! n))"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(simp (no_asm_simp))
    apply(simp add: option_to_list_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(rule_tac
    t="[teA a]"
    and s="liftA (option_to_list (ESplitItem_from (S2 ! n)))"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(rule_tac
    t="ESplitItem_from (S2 ! n)"
    and s="Some a"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
  apply(rule generation_derivation_has_always_nonterminal_at_front)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(blast)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(subgoal_tac "restrict_newprods G' G S1 n = liftB (ESplitItem_prods (S1!n))")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  prefer 2
  apply(case_tac "ESplitItem_from (S1 ! n)")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(erule_tac
    A="set (butlast (S1 @ S1'))"
    and x="S1!n"
    in ballE)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(rule in_set_butlast_append2)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S1 ! n)")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
    A="a"
    in nonemtpy_newignore_implies_newprods_unchanged)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(rule_tac
    t="restrict_newignore S1 n"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(rule_tac
    t="the (ESplitItem_elem (S1 ! n)) # liftA (ESplitItem_to (S1 ! n))"
    and s="option_to_list (ESplitItem_elem (S1 ! n)) @ liftA (ESplitItem_to (S1 ! n))"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(simp (no_asm_simp))
    apply(simp add: option_to_list_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(rule_tac
    t="[teA a]"
    and s="liftA (option_to_list (ESplitItem_from (S1 ! n)))"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(rule_tac
    t="ESplitItem_from (S1 ! n)"
    and s="Some a"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
  apply(rule generation_derivation_has_always_nonterminal_at_front)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
   apply(blast)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a d)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="PSplitItem_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="liftB (ESplitItem_prods (S1 ! n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="liftB (ESplitItem_prods (S1 ! n))"
    and s="restrict_newprods G' G S1 n"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp (no_asm_simp))
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="PSplitItem_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="liftB (ESplitItem_prods (S2 ! n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="liftB (ESplitItem_prods (S2 ! n))"
    and s="restrict_newprods G' G S2 n"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp (no_asm_simp))
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="ESplitItem_to ((S1 @ S1') ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="ESplitItem_to ((S2 @ S2') ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="(S1 @ S1') ! n"
    and s="S1!n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="(S2 @ S2') ! n"
    and s="S2!n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="liftB (ESplitItem_prods (S1 ! n)) = liftB (ESplitItem_prods (S2 ! n))"
    and s="(ESplitItem_prods (S1 ! n)) = (ESplitItem_prods (S2 ! n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(simp (no_asm))
   apply(rule impI)
   apply(rule liftB_inj)
   apply(blast)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (liftB (ESplitItem_prods (S1 ! n)))"
    and s="liftA(map (prod_to_edge G') (ESplitItem_prods (S1 ! n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule prod_to_edge_liftA_liftB)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (liftB (ESplitItem_prods (S2 ! n)))"
    and s="liftA(map (prod_to_edge G') (ESplitItem_prods (S2 ! n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(rule prod_to_edge_liftA_liftB)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d2a \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S2 @ S2') ! n))))))]\<rparr> e_\<pi>2a \<lparr>cfg_conf = liftB \<alpha>2a @ teB b # vaa\<rparr>")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S1 @ S1') ! n))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(case_tac "ESplitItem_from (S1 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="S1!n"
    and A="set (butlast (S1 @ S1'))"
    in ballE)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   prefer 2
   apply(rule in_set_butlast_append2)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(case_tac "ESplitItem_from (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="S2!n"
    and A="set (butlast (S2 @ S2'))"
    in ballE)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
   prefer 2
   apply(rule in_set_butlast_append2)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a aa)(*strict*)
  apply(rename_tac F1 F2)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(rule_tac
    t="liftA (map (prod_to_edge G') (ESplitItem_prods (S1 ! n))) = liftA (map (prod_to_edge G') (ESplitItem_prods (S2 ! n)))"
    and s=" (map (prod_to_edge G') (ESplitItem_prods (S1 ! n))) = (map (prod_to_edge G') (ESplitItem_prods (S2 ! n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(rule impI)
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(subgoal_tac "ESplitItem_prods (S1 ! n) = ESplitItem_prods (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(rule conjI)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(subgoal_tac "option_to_list (ESplitItem_elem (S2 ! n)) @ liftA (ESplitItem_to (S2 ! n)) = option_to_list (ESplitItem_elem (S1 ! n)) @ liftA (ESplitItem_to (S1 ! n))")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(rule liftA_inj)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(rule_tac
    w="option_to_list (ESplitItem_elem (S2 ! n))"
    in append_linj)
   apply(rule_tac
    t="option_to_list (ESplitItem_elem (S2 ! n)) @ liftA (ESplitItem_to (S2 ! n))"
    and s="option_to_list (ESplitItem_elem (S1 ! n)) @ liftA (ESplitItem_to (S1 ! n))"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(rule_tac
    t="ESplitItem_elem (S1 ! n)"
    and s="ESplitItem_elem (S2 ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S1 ! n)")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S2 ! n)")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
  apply(erule conjE)+
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
  apply(subgoal_tac "da (length ((ESplitItem_prods (S1 ! n)))) = d (length((ESplitItem_prods (S1 ! n))))")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
  apply(rule_tac
    ?d2.0="da"
    and ?d1.0="d"
    and ?\<pi>2.0="[]"
    in cfgLM_trans_der_coincide)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(rule_tac
    t="liftA (option_to_list (Some F1))"
    and s="liftA (option_to_list (ESplitItem_from (S2 ! n)))"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(rule_tac
    f="liftA"
    in arg_cong)
    apply(rule_tac
    f="option_to_list"
    in arg_cong)
    apply(rule_tac
    t="ESplitItem_from (S2 ! n)"
    and s="Some (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm_simp))
     apply(rule cropTol3l2_ID)
     apply(rule_tac
    t="restrict_newignore S2 n"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(rule_tac
    t="PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(rule_tac
    t="Some F1"
    and s="ESplitItem_from (S1 ! n)"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(rule_tac
    t="ESplitItem_from (S1 ! n)"
    and s="Some (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
    in ssubst)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm_simp))
     apply(rule cropTol3l2_ID)
     apply(rule_tac
    t="restrict_newignore S1 n"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
      apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 d da)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
  apply(case_tac "F1")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q ba)(*strict*)
  apply(rename_tac qF1 AF1)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
  apply(subgoal_tac "ESplitItem_ignore (S1 ! n) = []")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
   prefer 2
   apply(subgoal_tac "proper_l3_l2_seq (PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ option_to_list (Some (cons_l2 qF1 AF1)) @ ESplitItem_ignore (S1 ! n))")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    prefer 2
    apply(subgoal_tac "EValidSplitItem_belongs G (S1 ! n)")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
   apply(simp (no_asm_use) add: option_to_list_def)
   apply(rule l2_in_proper_l3_l2_seq_at_end)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
  apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n) = []")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp (no_asm_simp))
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemovedX S1 ! Suc n)))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2)(*strict*)
  apply(case_tac "F2")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q baa)(*strict*)
  apply(rename_tac qF2 AF2)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
  apply(subgoal_tac "ESplitItem_ignore (S2 ! n) = []")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
   prefer 2
   apply(subgoal_tac "proper_l3_l2_seq (PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ option_to_list (Some (cons_l2 qF2 AF2)) @ ESplitItem_ignore (S2 ! n))")
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    prefer 2
    apply(subgoal_tac "EValidSplitItem_belongs G (S2 ! n)")
     apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
   apply(simp (no_asm_use) add: option_to_list_def)
   apply(rule l2_in_proper_l3_l2_seq_at_end)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
  apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n) = []")
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp (no_asm_simp))
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemovedX S2 ! Suc n)))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(rename_tac q11 A1 q12 q21 A2 q22)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  prefer 2
  apply(rule_tac
    d="e_d1"
    and A="(cons_l3 q11 A1 q12)"
    and w="liftA(butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S1 @ S1') ! n))))))"
    in from_derives_prefix)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp add: split_TSstructure_def)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(rule_tac
    t="[teA (cons_l3   q11 A1 q12)] @ liftA (butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S1 @ S1') ! n))))))"
    and s="liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S1 @ S1') ! n))))))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm) add: liftA_commutes_over_concat)
   apply(rule_tac
    t="(S1 @ S1') ! n"
    and s="S1!n"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm_simp) add: option_to_list_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  prefer 2
  apply(rule_tac
    d="e_d1a"
    and A="(cons_l3 q21 A2 q22)"
    and w="liftA(butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S2 @ S2') ! n))))))"
    in from_derives_prefix)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp add: split_TSstructure_def)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(rule_tac
    t="[teA (cons_l3   q21 A2 q22)] @ liftA (butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S2 @ S2') ! n))))))"
    and s="liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S2 @ S2') ! n))))))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm) add: liftA_commutes_over_concat)
   apply(rule_tac
    t="(S2 @ S2') ! n"
    and s="S2!n"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_d1 e_\<pi>1 e_\<pi>2 p_da e_d1a e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(simp (no_asm_simp) add: option_to_list_def)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S1 @ S1') ! n))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr>")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d1a \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))) (ESplitItem_ignore ((S2 @ S2') ! n))))))\<rparr> e_\<pi>1a \<lparr>cfg_conf = liftB \<alpha>1a\<rparr>")
  apply(rename_tac n ds \<pi>s fw p_d e_d1 e_d2 va e_\<pi>1 e_\<pi>2 p_da e_d1a e_d2a vaa e_\<pi>1a e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(subgoal_tac "ESplitItem_from (S1 ! n) = ESplitItem_from (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  prefer 2
  apply(rule_tac
    t="ESplitItem_from (S1 ! n)"
    and s="Some (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(simp (no_asm_simp))
   apply(rule cropTol3l2_ID)
   apply(rule_tac
    t="restrict_newignore S1 n"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(simp (no_asm_simp))
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(rule_tac
    t="ESplitItem_from (S2 ! n)"
    and s="Some (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(simp (no_asm_simp))
   apply(rule cropTol3l2_ID)
   apply(rule_tac
    t="restrict_newignore S2 n"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(simp (no_asm_simp))
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  prefer 2
  apply(rule_tac
    G="G'"
    and G'="G"
    and ?d1.0="d1a"
    and ?d2.0="d1aa"
    and ?x1.0="\<alpha>2b@\<alpha>2"
    and ?x2.0="\<alpha>2c@\<alpha>2a"
    in eliminating_derivations_are_equal_with_differing_future6)
         apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
         apply(simp add: F2LR1inputx_def)
        apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
        apply(simp add: F2LR1inputx_def)
       apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
       apply(simp add: F2LR1inputx_def)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
      apply(simp add: F2LR1inputx_def)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
     apply(simp add: F2LR1inputx_def)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S1 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    v="\<pi>1a"
    in equal_by_length_and_prefix_of_greater)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S1 ! n)) \<or> SSX" for SSX)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    prefer 2
    apply(rule_tac
    b="\<pi>2 @ e_\<pi>2"
    and d="\<pi>s ! n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc n) (length v)))"
    in mutual_strict_prefix_prefix)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule sym)
    apply(rule_tac
    t="S1 ! n"
    and s="(S1@S1') ! n"
    in subst)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(erule disjE)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(subgoal_tac "c=[]")
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(rule_tac
    ?d1.0="d1a"
    and ?d2.0="d"
    in unique_generation_length)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S2 ! n)) \<or> SSX" for SSX)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(rule_tac
    b="\<pi>2a @ e_\<pi>2a"
    and d="\<pi>s ! n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc n) (length v)))"
    in mutual_strict_prefix_prefix)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="S2 ! n"
    and s="(S2@S2') ! n"
    in subst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(erule disjE)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(rule_tac
    ?d1.0="d1aa"
    and ?d2.0="da"
    in unique_generation_length)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "prefix (ESplitItem_prods (S1 ! n)) \<pi>1a")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S1 ! n)) \<or> SSX" for SSX)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(rule_tac
    b="\<pi>2 @ e_\<pi>2"
    and d="\<pi>s ! n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc n) (length v)))"
    in mutual_strict_prefix_prefix)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="S1 ! n"
    and s="(S1@S1') ! n"
    in subst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(erule disjE)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(rule_tac
    ?d1.0="d1a"
    and ?d2.0="d"
    in unique_generation_length)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "prefix (ESplitItem_prods (S2 ! n)) \<pi>1a")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S2 ! n)) \<or> SSX" for SSX)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(rule_tac
    b="\<pi>2a @ e_\<pi>2a"
    and d="\<pi>s ! n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc n) (length v)))"
    in mutual_strict_prefix_prefix)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="S2 ! n"
    and s="(S2@S2') ! n"
    in subst)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(erule disjE)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(rule_tac
    ?d1.0="d1aa"
    and ?d2.0="da"
    in unique_generation_length)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(case_tac "Esplit_signature S1 ! n")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S1 ! n)) < length (ESplitItem_prods (S2 ! n))")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(subgoal_tac "strict_prefix (ESplitItem_prods (S1 ! n)) (ESplitItem_prods (S2 ! n))")
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    prefer 2
    apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(simp add: strict_prefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(rule_tac
    v="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in left_degen_repetitions_in_parallel_derivation)
         apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S2 ! n)) < length (ESplitItem_prods (S1 ! n))")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(subgoal_tac "strict_prefix (ESplitItem_prods (S2 ! n)) (ESplitItem_prods (S1 ! n))")
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    prefer 2
    apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(simp add: strict_prefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(rule_tac
    v="[]"
    and ?d1.0="da"
    and ?d2.0="d"
    in left_degen_repetitions_in_parallel_derivation)
         apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(clarsimp)
  apply(case_tac "length (ESplitItem_prods (S1 ! n)) < length (ESplitItem_prods (S2 ! n))")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_prods (S1 ! n)) (ESplitItem_prods (S2 ! n))")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   prefer 2
   apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(rule_tac
    v="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in terminal_production_repetitions_in_parallel_derivation)
       apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S2 ! n)) < length (ESplitItem_prods (S1 ! n))")
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_prods (S2 ! n)) (ESplitItem_prods (S1 ! n))")
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   prefer 2
   apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(rule_tac
    v="[]"
    and ?d1.0="da"
    and ?d2.0="d"
    in terminal_production_repetitions_in_parallel_derivation)
       apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw p_d e_\<pi>2 p_da e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "fillOptL [] (last_back_state_if_l3_nonterminal []) = []")
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  prefer 2
  apply(simp add: fillOptL_def last_back_state_if_l3_nonterminal_def)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="restrict_newprods G' G (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) only: restrict_newprods_def)
  apply(rule_tac
    t="restrict_newignore (take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') n"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="[]"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_prods (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="restrict_newprods G' G (take (Suc (length v)) S1 @ take (Suc (length v) - length S1) S1') n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) only: restrict_newprods_def)
  apply(rule_tac
    t="restrict_newignore (take (Suc (length v)) S1 @ take (Suc (length v) - length S1) S1') n"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="[]"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    and s="restrict_newto S1 n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    and s="restrict_newto S2 n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) only: restrict_newto_def new_post_sig_def)
  apply(rule_tac
    t="ESplitItem_prods ((take (Suc (length v)) S1 @ take (Suc (length v) - length S1) S1') ! n)"
    and s="ESplitItem_prods (S1 ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="ESplitItem_prods ((take (Suc (length v)) S2 @ take (Suc (length v) - length S2) S2') ! n)"
    and s="ESplitItem_prods (S2 ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw d)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "EValidSplitItem_gen G (S1 ! n)")
  apply(rename_tac n ds \<pi>s fw d)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac n ds \<pi>s fw d)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw d da)(*strict*)
  apply(erule conjE)+
  apply(rename_tac d2x d1x)
  apply(rename_tac n ds \<pi>s fw d2x d1x)(*strict*)
  apply(case_tac "ESplitItem_from (S1 ! n)")
  apply(rename_tac n ds \<pi>s fw d2x d1x)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
  apply(rename_tac n ds \<pi>s fw d2x d1x)(*strict*)
  prefer 2
  apply(rule_tac cfgLM_trans_der_from_empty)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x a)(*strict*)
  apply(case_tac "ESplitItem_from (S2 ! n)")
  apply(rename_tac n ds \<pi>s fw d2x d1x a)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
  apply(rename_tac n ds \<pi>s fw d2x d1x a)(*strict*)
  prefer 2
  apply(rule_tac cfgLM_trans_der_from_empty)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x a aa)(*strict*)
  apply(rename_tac X1 X2)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "cropTol3l2_single X1 = cropTol3l2_single X2")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    t="X1"
    and s="the(ESplitItem_from (S1 ! n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="X2"
    and s="the(ESplitItem_from (S2 ! n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    ?w1.0="restrict_newignore S1 n"
    and ?w2.0="restrict_newignore S2 n"
    in cropTol3l2_single_equal_from_cropTol3l2_equal)
  apply(rule_tac
    t="hd(cropTol3l2 (the (ESplitItem_from (S1 ! n)) # restrict_newignore S1 n))"
    and s="PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="hd(cropTol3l2 (the (ESplitItem_from (S2 ! n)) # restrict_newignore S2 n))"
    and s="PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(case_tac "n=length v")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp (no_asm) add: restrict_toberemovedX_def)
  apply(rule_tac
    t="take (length (ESplitItem_to (S1 ! length v))) (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length ((restrict_toberemoved S1 @ [tl (ESplitItem_to (last S1) @ ESplitItem_ignore (last S1))]) ! Suc (length v))))"
    and s="[cropTol3l2_single (hd (ESplitItem_to (S1 ! length v)))]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="(restrict_toberemoved S1 @ [tl (ESplitItem_to (last S1) @ ESplitItem_ignore (last S1))]) ! Suc (length v)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule nth_append_beyond)
   apply(rule_tac
    t="length (restrict_toberemoved S1)"
    in ssubst)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="last S1"
    and s="S1!length v"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule last_nth3)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "ESplitItem_to (S1 ! length v) \<noteq> []")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule ESplitItem_to_not_empty_on_generating_line)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(case_tac "ESplitItem_to (S1 ! length v)")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 a list)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="take (length (ESplitItem_to (S2 ! length v))) (drop_and_crop (ESplitItem_to (S2 ! length v) @ ESplitItem_ignore (S2 ! length v)) (length ((restrict_toberemoved S2 @ [tl (ESplitItem_to (last S2) @ ESplitItem_ignore (last S2))]) ! Suc (length v))))"
    and s="[cropTol3l2_single (hd (ESplitItem_to (S2 ! length v)))]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="(restrict_toberemoved S2 @ [tl (ESplitItem_to (last S2) @ ESplitItem_ignore (last S2))]) ! Suc (length v)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule nth_append_beyond)
   apply(rule_tac
    t="length (restrict_toberemoved S2)"
    in ssubst)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="last S2"
    and s="S2!length v"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule last_nth3)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "ESplitItem_to (S2 ! length v) \<noteq> []")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule ESplitItem_to_not_empty_on_generating_line)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(case_tac "ESplitItem_to (S2 ! length v)")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 a list)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Esplit_signature S1 ! length v = teB b")
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac t="Esplit_signature S1" and s="v@[teB b]" in ssubst)
   apply(force)
  apply(rule nth_append_length)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "lastProduces d1x (ESplitItem_prods (S1 ! length v)) \<and> lastProduces d2x (ESplitItem_prods (S2 ! length v))")
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule conjI)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule lastProduces_intro)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule lastProduces_intro)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="d1x"
    and ?d2.0="d2x"
    in AX_equal_length_production_of_terminal_or_nonterminal)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="d1x"
    and ?d2.0="d2x"
    in prod_to_edge_equality_for_terminal_and_nonterminal_generation)
        apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast (ESplitItem_to (S1 ! length v)))")
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule_tac
    i="length((ESplitItem_prods (S1 ! length v)))"
    and d="d1x"
    in cfgLM.trans_der_position_detail)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e ci cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
   prefer 2
   apply(rule_tac
    e="e"
    and v="cfg_confa"
    and \<alpha>="[]"
    and w="[X1]"
    and d="d1x"
    and n="length((ESplitItem_prods (S1 ! length v)))"
    in only_l3_nonterminals_butlast_preserved)
         apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
       apply(clarsimp)
       apply(simp add: option_to_list_def)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
      apply(simp (no_asm))
      apply(simp add: only_l3_nonterminals_def)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "v1=[b]")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
   prefer 2
   apply(case_tac v1)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
    apply(case_tac v2)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list)(*strict*)
   apply(case_tac list)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista)(*strict*)
   apply(case_tac "ESplitItem_to (S1 ! length v)")
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
  apply(subgoal_tac "v2=ESplitItem_to (S1 ! length v)")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast (ESplitItem_to (S2 ! length v)))")
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule_tac
    i="length((ESplitItem_prods (S2 ! length v)))"
    and d="d2x"
    in cfgLM.trans_der_position_detail)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e ci cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
   prefer 2
   apply(rule_tac
    e="e"
    and v="cfg_confa"
    and \<alpha>="[]"
    and w="[X2]"
    and d="d2x"
    and n="length((ESplitItem_prods (S2 ! length v)))"
    in only_l3_nonterminals_butlast_preserved)
         apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
       apply(clarsimp)
       apply(simp add: option_to_list_def)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
      apply(simp (no_asm))
      apply(simp add: only_l3_nonterminals_def)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "v1=[b]")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
   prefer 2
   apply(case_tac v1)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
    apply(case_tac v2)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list)(*strict*)
   apply(case_tac list)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista)(*strict*)
   apply(case_tac "ESplitItem_to (S2 ! length v)")
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea a lista aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v1 v2 ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
  apply(subgoal_tac "v2=ESplitItem_to (S2 ! length v)")
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2 e v2 ea)(*strict*)
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "cropTol3l2_single (hd (ESplitItem_to (S1 ! length v))) = cropTol3l2_single (hd (ESplitItem_to (S2 ! length v)))")
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    d1x="d1x"
    and d2x="d2x"
    in compatibel_derivation_compatible_first_nonterminal_at_end)
         apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       prefer 2
       apply(simp add: option_to_list_def)
      apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      prefer 2
      apply(simp add: option_to_list_def)
     apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule conjI)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (restrict_newprodsX G' G (ESplitItem_prods (S1 ! length v)) (Some (Esplit_signature S1 ! length v)) [cropTol3l2_single (hd (ESplitItem_to (S1 ! length v)))])"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (restrict_newprodsX G' G (ESplitItem_prods (S2 ! length v)) (Some (Esplit_signature S1 ! length v)) [cropTol3l2_single (hd (ESplitItem_to (S2 ! length v)))])"
    in ssubst)
   apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "n<length v")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(simp (no_asm) add: restrict_toberemovedX_def)
  apply(rule_tac
    t="(restrict_toberemoved S1 @ [tl (ESplitItem_to (last S1) @ ESplitItem_ignore (last S1))]) ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule nth_append_1)
  apply(rule_tac
    t="length (restrict_toberemoved S1)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule length_restrict_toberemoved)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="(restrict_toberemoved S2 @ [tl (ESplitItem_to (last S2) @ ESplitItem_ignore (last S2))]) ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule nth_append_1)
  apply(rule_tac
    t="length (restrict_toberemoved S2)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule length_restrict_toberemoved)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (ESplitItem_ignore (S1 ! n)) \<le> length (restrict_toberemovedX S1 ! Suc n)")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemovedX S1 ! Suc n))) \<le> length (ESplitItem_to (S1 ! n))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "restrict_newignore S1 n = []")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule_tac
    t="restrict_newignore S1 n"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemovedX S1 ! Suc n))) \<le> length (ESplitItem_to (S1 ! n))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) - length (restrict_toberemovedX S1 ! Suc n) \<le> length (ESplitItem_to (S1 ! n))")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="length (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) - length (restrict_toberemovedX S1 ! Suc n)"
    in subst)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(blast)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (ESplitItem_ignore (S2 ! n)) \<le> length (restrict_toberemovedX S2 ! Suc n)")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemovedX S2 ! Suc n))) \<le> length (ESplitItem_to (S2 ! n))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(subgoal_tac "restrict_newignore S2 n = []")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   prefer 2
   apply(rule_tac
    t="restrict_newignore S2 n"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
    in ssubst)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemovedX S2 ! Suc n))) \<le> length (ESplitItem_to (S2 ! n))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "length (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) - length (restrict_toberemovedX S2 ! Suc n) \<le> length (ESplitItem_to (S2 ! n))")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="length (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) - length (restrict_toberemovedX S2 ! Suc n)"
    in subst)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(blast)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "restrict_toberemovedX S1 ! Suc n = restrict_toberemoved S1 ! Suc n")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "restrict_toberemovedX S2 ! Suc n = restrict_toberemoved S2 ! Suc n")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="take (length (ESplitItem_to (S2 ! n))) (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule take_all)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
    t="restrict_toberemoved S2 ! Suc n"
    and s="restrict_toberemovedX S2 ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="take (length (ESplitItem_to (S1 ! n))) (drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule take_all)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
    t="restrict_toberemoved S1 ! Suc n"
    and s="restrict_toberemovedX S1 ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="drop_and_crop (ESplitItem_to (S1 ! n) @ ESplitItem_ignore (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n))"
    and s=" drop_and_crop (butn (ESplitItem_to (S1 ! n)) ((length (restrict_toberemoved S1 ! Suc n))-length(ESplitItem_ignore (S1 ! n))) ) 0"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="min (min (length (ESplitItem_to (S1 ! n))) (length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n))) (length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n))"
    and s="length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    t="min (length (ESplitItem_to (S1 ! n))) (length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n))"
    and s="length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n)"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="min (length (ESplitItem_to (S1 ! n))) (length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n))"
    and s="(length (ESplitItem_to (S1 ! n)) + length (ESplitItem_ignore (S1 ! n)) - length (restrict_toberemoved S1 ! Suc n))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule Orderings.min_absorb2)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule Orderings.min_absorb1)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(rule_tac
    t="drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n))"
    and s=" drop_and_crop (butn (ESplitItem_to (S2 ! n)) ((length (restrict_toberemoved S2 ! Suc n))-length(ESplitItem_ignore (S2 ! n))) ) 0"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="min (min (length (ESplitItem_to (S2 ! n))) (length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemoved S2 ! Suc n))) (length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemoved S2 ! Suc n))"
    and s="length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemoved S2 ! Suc n)"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    t="min (length (ESplitItem_to (S2 ! n))) (length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemoved S2 ! Suc n))"
    and s="length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemoved S2 ! Suc n)"
    in ssubst)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    i="Suc n"
    and ?S1.0="S1"
    and n="length v"
    and v="v"
    and b="b"
    in e_derivation_can_be_embedded_minimally)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    prefer 2
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                   apply(force)
                  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                  apply(force)
                 apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                 apply(force)
                apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                apply(force)
               apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
               apply(force)
              apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
              apply(force)
             apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
             apply(force)
            apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
            apply(force)
           apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    i="Suc n"
    and ?S1.0="S2"
    and n="length v"
    and v="v"
    and b="b"
    in e_derivation_can_be_embedded_minimally)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    prefer 2
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                    apply(force)
                   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                   apply(force)
                  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                  apply(force)
                 apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                 apply(force)
                apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
                apply(force)
               apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
               apply(force)
              apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
              apply(force)
             apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
             apply(force)
            apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
            apply(force)
           apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods ((S2 @ S2') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc n) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S2 @ S2') ! Suc n))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S2 @ S2') ! Suc n))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc n)))\<rparr> (ESplitItem_prods ((S2 @ S2') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc n) (take (length v) fw))) @ teB b # va\<rparr>)")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc n)))\<rparr> (ESplitItem_prods ((S1 @ S1') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc n) (take (length v) fw))) @ teB b # va\<rparr>)")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods ((S1 @ S1') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc n) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc n)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S1 @ S1') ! Suc n))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S1 @ S1') ! Suc n))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(simp add: fillWithPreContext_def)
  apply(subgoal_tac "\<exists>Y1. ESplitItem_from (S1 ! Suc n)= Some Y1")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  prefer 2
  apply(subgoal_tac "(\<forall>x\<in> set (butlast (S1 @ S1')). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(erule_tac
    x="S1!Suc n"
    in ballE)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  prefer 2
  apply(subgoal_tac "S1 ! Suc n \<in> set (butlast (S1 @ S1'))")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(thin_tac "S1 ! Suc n \<notin> set (butlast (S1 @ S1'))")
  apply(rule nth_in_butlast_append)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    S="S1"
    and S'="[]"
    in EValidSplit_continuation_not_empty)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da)(*strict*)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  prefer 2
  apply(rule_tac
    n="n"
    and X="Y1"
    and S="S1"
    and S'="S1'"
    and d="p_d"
    and v="v"
    and b="b"
    and \<pi>="ESplitItem_prods ((S1 @ S1') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))"
    and tn="fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v)))) @ tl (ESplitItem_to ((S1 @ S1') ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc n))"
    in equal_split_prefix_hlp5_construct_relevant_cfgLMMIP)
           apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(thin_tac "cfgLMMIP G p_da (teA (fillOpt (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc n))))) # liftA (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S2 @ S2') ! Suc n)))))) (ESplitItem_prods ((S2 @ S2') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))) (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc n))))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(rule_tac
    t="teA Y1 # liftA (take (length (restrict_newignore S1 (Suc n))) (ESplitItem_ignore (S1 ! Suc n)))"
    and s="(teA (fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc n))))) # liftA (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S1 @ S1') ! Suc n))))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length v) ! Suc n = SSX" for SSX)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="(S1 @ S1') ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule conjI)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(rule fillOpt_single_with_last_back_state_if_l3_nonterminal)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! Suc n) @ ESplitItem_ignore (S1 ! Suc n)) (length (restrict_toberemovedX S1 ! Suc (Suc n))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="drop (length (ESplitItem_to (S1 ! Suc n))) (drop_and_crop (ESplitItem_to (S1 ! Suc n) @ ESplitItem_ignore (S1 ! Suc n)) (length (restrict_toberemovedX S1 ! Suc (Suc n))))"
    and s=" (drop_and_crop (ESplitItem_ignore (S1 ! Suc n)) (length (restrict_toberemovedX S1 ! Suc (Suc n))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d Y1)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule fillOptL_with_last_back_state_if_l3_nonterminal_X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(thin_tac "cfgLMMIP G p_d (teA (fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc n))))) # liftA (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S1 @ S1') ! Suc n)))))) (ESplitItem_prods ((S1 @ S1') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))) (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v)))) @ tl (ESplitItem_to ((S1 @ S1') ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc n))))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(subgoal_tac "\<exists>Y2. ESplitItem_from (S2 ! Suc n)= Some Y2")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  prefer 2
  apply(subgoal_tac "(\<forall>x\<in> set (butlast (S2 @ S2')). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(erule_tac
    x="S2!Suc n"
    in ballE)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  prefer 2
  apply(subgoal_tac "S2 ! Suc n \<in> set (butlast (S2 @ S2'))")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(thin_tac "S2 ! Suc n \<notin> set (butlast (S2 @ S2'))")
  apply(rule nth_in_butlast_append)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
  apply(rule_tac
    S="S2"
    and S'="[]"
    in EValidSplit_continuation_not_empty)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d \<pi>)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1)(*strict*)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (restrict_newprodsX G' G (ESplitItem_prods (S1 ! n)) (Some (Esplit_signature S1 ! n)) (drop_and_crop (butn (ESplitItem_to (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n) - length (ESplitItem_ignore (S1 ! n)))) 0))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule_tac
    t="map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (restrict_newprodsX G' G (ESplitItem_prods (S2 ! n)) (Some (Esplit_signature S1 ! n)) (drop_and_crop (butn (ESplitItem_to (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n) - length (ESplitItem_ignore (S2 ! n)))) 0))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  prefer 2
  apply(rule_tac
    n="n"
    and X="Y2"
    and S="S2"
    and S'="S2'"
    and d="p_da"
    and v="v"
    and b="b"
    and \<pi>="ESplitItem_prods ((S2 @ S2') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))"
    and tn="fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc n))"
    in equal_split_prefix_hlp5_construct_relevant_cfgLMMIP)
           apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
          apply(force)
         apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
         apply(force)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule_tac
    t="teA Y2 # liftA (take (length (restrict_newignore S2 (Suc n))) (ESplitItem_ignore (S2 ! Suc n)))"
    and s="(teA (fillOpt (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc n))))) # liftA (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S2 @ S2') ! Suc n))))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length v) ! Suc n = SSX" for SSX)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="(S2 @ S2') ! Suc n"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule conjI)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule fillOpt_single_with_last_back_state_if_l3_nonterminal)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S2 ! Suc n) @ ESplitItem_ignore (S2 ! Suc n)) (length (restrict_toberemovedX S2 ! Suc (Suc n))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule drop_and_crop_length)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="drop (length (ESplitItem_to (S2 ! Suc n))) (drop_and_crop (ESplitItem_to (S2 ! Suc n) @ ESplitItem_ignore (S2 ! Suc n)) (length (restrict_toberemovedX S2 ! Suc (Suc n))))"
    and s=" (drop_and_crop (ESplitItem_ignore (S2 ! Suc n)) (length (restrict_toberemovedX S2 ! Suc (Suc n))))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_da Y1 d Y2 \<pi>)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule fillOptL_with_last_back_state_if_l3_nonterminal_X)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(thin_tac "cfgLMMIP G p_da (teA (fillOpt (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc n))))) # liftA (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc n))) (ESplitItem_ignore ((S2 @ S2') ! Suc n)))))) (ESplitItem_prods ((S2 @ S2') ! Suc n) @ \<pi>s ! Suc n @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc n)) (length v)))) (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc n))))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi>)(*strict*)
  apply(erule exE)+
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d Y2 \<pi> da \<pi>')(*strict*)
  apply(rename_tac Y1 d1y Y2 \<pi>1y d2y \<pi>2y)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(rule_tac
    t="liftA (map (prod_to_edge G') (ESplitItem_prods (S1 ! n))) = liftA (map (prod_to_edge G') (ESplitItem_prods (S2 ! n)))"
    in ssubst)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(rule liftA_inj_equality)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(rule_tac
    ?d1.0="d1x"
    and ?d2.0="d2x"
    and de="ds!n"
    and \<alpha>e="fw!n"
    in equal_split_prefix_hlp2_withMIP_simplified)
            apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
            apply(force)
           apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
           apply(force)
          apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
          apply(simp add: option_to_list_def)
         apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
         apply(simp add: option_to_list_def)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
        apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
        apply(clarsimp)
        apply(erule_tac
    x="n"
    in allE)
        apply(clarsimp)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
     apply(case_tac "Esplit_signature S1 ! n")
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y a)(*strict*)
      apply(clarsimp)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
     apply(rule conjI)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
      apply(rule lastProduces_intro)
        apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
     apply(rule lastProduces_intro)
       apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
      apply(force)
     apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y \<pi>2y ba)(*strict*)
     apply(force)
    apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
    apply(force)
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
   apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(case_tac \<pi>1y)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  prefer 2
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y a list)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y)(*strict*)
  apply(simp add: cfgLMMIP_def cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec)(*strict*)
  apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec)(*strict*)
  apply(clarsimp)
  apply(case_tac "butn (ESplitItem_to (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n) - length (ESplitItem_ignore (S1 ! n)))")
   apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec)(*strict*)
   apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "butn (ESplitItem_to (S1 ! n)) (length (restrict_toberemoved S1 ! Suc n) - length (ESplitItem_ignore (S1 ! n)))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 d2y \<pi>2y e ea ec a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(case_tac \<pi>2y)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  prefer 2
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y a list)(*strict*)
  apply(force)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 p_d p_da Y1 d1y Y2 \<pi>1y d2y \<pi>2y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y)(*strict*)
  apply(simp add: cfgLMMIP_def cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb)(*strict*)
  apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb)(*strict*)
  apply(clarsimp)
  apply(case_tac "butn (ESplitItem_to (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n) - length (ESplitItem_ignore (S2 ! n)))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "butn (ESplitItem_to (S2 ! n)) (length (restrict_toberemoved S2 ! Suc n) - length (ESplitItem_ignore (S2 ! n)))")
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ds \<pi>s fw d2x d1x X1 X2 Y1 d1y Y2 \<pi>1y d2y e ea eb a list aa lista)(*strict*)
  apply(clarsimp)
  done

theorem equal_split_prefix_updated: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=v@[teB b]@x1\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=v@[teB b]@x2\<rparr>)
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> EValidSplit G (S2@S2')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> length S2 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> v@[teB b] = Esplit_signature S2
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> x2 = Esplit_signature S2'
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> S2R=restrict G' G (S2@S2') (length (v@[teB b]))
  \<Longrightarrow> restrictX G' S1R = restrictX G' S2R"
  apply(subgoal_tac "ESplitItem_elem ((S1 @ S1') ! length v) = Some (teB b)")
   prefer 2
   apply(rule equal_split_prefix_hlp2)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "PValidSplit G' G S1R")
   prefer 2
   apply(rule equal_split_prefix_hlp3)
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
  apply(subgoal_tac "ESplitItem_elem ((S2 @ S2') ! length v) = Some (teB b)")
   prefer 2
   apply(rule_tac
      ?d1.0="d2"
      in equal_split_prefix_hlp2)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "PValidSplit G' G S2R")
   prefer 2
   apply(rule_tac
      ?S1.0="S2"
      and ?d1.0="d2"
      in equal_split_prefix_hlp3)
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
  apply(subgoal_tac "take (length (v@[teB b])) (restrictX G' S1R) = take (length (v@[teB b])) (restrictX G' S2R)")
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      and S1'="S1'"
      and S2'="S2'"
      and ?S1.0="S1"
      and ?S2.0="S2"
      in equal_split_prefix_hlp1_updated)
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
      t="restrictX G' S1R"
      and s="take (length (v @ [teB b])) (restrictX G' S1R)"
      in ssubst)
   apply(simp add: restrict_def restrict_len_def restrict_map_def restrictX_def)
   apply(case_tac "length (Esplit_signature S1)")
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(nat_seq 0 nat) = SSx" for SSx)
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rule_tac
      t="restrictX G' S2R"
      and s="take (length (v @ [teB b])) (restrictX G' S2R)"
      in ssubst)
   apply(simp add: restrict_def restrict_len_def restrict_map_def restrictX_def)
   apply(case_tac "length (Esplit_signature S1)")
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(nat_seq 0 nat) = SSx" for SSx)
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(force)
  done

lemma equal_split_prefix_hlp1: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=v@[teB b]@x1\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=v@[teB b]@x2\<rparr>)
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> EValidSplit G (S2@S2')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> length S2 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> v@[teB b] = Esplit_signature S2
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> x2 = Esplit_signature S2'
  \<Longrightarrow> S1' \<noteq> []
  \<Longrightarrow> S2' \<noteq> []
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> S2R=restrict G' G (S2@S2') (length (v@[teB b]))
  \<Longrightarrow> ESplitItem_elem ((S1@S1') ! (length v)) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S1R
  \<Longrightarrow> ESplitItem_elem ((S2@S2') ! (length v)) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S2R
  \<Longrightarrow> i<length (v@[teB b])
  \<Longrightarrow> S1R!i = S2R!i"
  apply(subgoal_tac "restrictX G' S1R = restrictX G' S2R")
   prefer 2
   apply(rule_tac
      S1R="S1R"
      and S2R="S2R"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in equal_split_prefix_updated)
                  apply(force)
                 apply(force)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            prefer 7
            apply(force)
           apply(force)
          prefer 6
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "restrictX G' [S1R!i] = restrictX G' [S2R!i]")
   prefer 2
   apply(rule_tac
      t="restrictX G' [S1R!i]"
      and s="[(restrictX G' S1R) !i]"
      in subst)
    apply(simp (no_asm) add: restrictX_def)
    apply(rule_tac
      t="map (\<lambda>I. I\<lparr>PSplitItem_prods := map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (PSplitItem_prods I)\<rparr>) S1R ! i"
      in ssubst)
     apply(rule nth_map)
     apply(clarsimp)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature S1) - Suc 0)) = SSx" for SSx)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(clarsimp)
     apply(case_tac "Esplit_signature S1")
      apply(clarsimp)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(clarsimp)
   apply(rule_tac
      t="restrictX G' [S2R!i]"
      and s="[(restrictX G' S2R) !i]"
      in subst)
    apply(simp (no_asm) add: restrictX_def)
    apply(rule_tac
      t="map (\<lambda>I. I\<lparr>PSplitItem_prods := map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (PSplitItem_prods I)\<rparr>) S2R ! i"
      in ssubst)
     apply(rule nth_map)
     apply(clarsimp)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature S2) - Suc 0)) = SSx" for SSx)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(clarsimp)
     apply(case_tac "Esplit_signature S1")
      apply(clarsimp)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_prods (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_prods (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_from PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prodsa PSplitItem_elem PSplitItem_to)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_from PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prodsa PSplitItem_elem PSplitItem_to PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsaa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim PSplitItem_from PSplitItem_ignore PSplitItem_elim_prods PSplitItem_elem PSplitItem_to PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_to)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_to PSplitItem_elima PSplitItem_fromaa PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim PSplitItem_from PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_to PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa PSplitItem_elima PSplitItem_fromaa PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_to PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elim PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa PSplitItem_elima PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim PSplitItem_ignore PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_elim (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_elem (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_elem (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prods PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim_prods PSplitItem_prods PSplitItem_elem PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(subgoal_tac "PSplitItem_elim_prods (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) = PSplitItem_elim_prods (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
   prefer 2
   apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i")
   apply(rename_tac PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac PSplitItem_elim_prods PSplitItem_prods PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prodsa PSplitItem_elema PSplitItem_toa)(*strict*)
   apply(simp add: restrictX_def)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature S1) - Suc 0)) = SSx" for SSx)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length (Esplit_signature S1) - Suc 0) = length (Esplit_signature S1)")
   prefer 2
   apply(case_tac "Esplit_signature S1")
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length (Esplit_signature S1) - Suc 0) ! i = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp (no_asm) add: restrict_newprods_def)
  apply(subgoal_tac "\<exists>ds \<pi>s fw. cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw")
   prefer 2
   apply(simp add: cfgLMTDL_def)
   apply(subgoal_tac "\<exists>ds f\<pi> fw. cfgLM.trans_der_list SSG ds (map (\<lambda>w. \<lparr>cfg_conf = [w]\<rparr>) (Esplit_signature S1)) f\<pi> (map (\<lambda>w. \<lparr>cfg_conf = w\<rparr>) fw) \<and> setA (foldl (@) [] fw) = {}" for SSG)
    prefer 2
    apply(rule construct_elimininating_trans_der_list)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(simp add: split_TSstructure_def)
     apply(rule Esplit_signature_belongs_setA)
     apply(force)
    apply(rule Esplit_signature_belongs_setB)
    apply(force)
   apply(clarsimp)
   apply(rename_tac ds f\<pi> fw)(*strict*)
   apply(rule_tac
      x="ds"
      in exI)
   apply(rule_tac
      x="f\<pi>"
      in exI)
   apply(rule_tac
      x="map filterB fw"
      in exI)
   apply(rule_tac
      t="(map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) (map filterB fw))"
      and s="(map (\<lambda>w. \<lparr>cfg_conf = w\<rparr>) fw)"
      in ssubst)
    apply(rename_tac ds f\<pi> fw)(*strict*)
    apply(rule listEqI)
     apply(rename_tac ds f\<pi> fw)(*strict*)
     apply(force)
    apply(rename_tac ds f\<pi> fw ia)(*strict*)
    apply(clarsimp)
    apply (metis setA_empty_foldl liftBDeConv2)
   apply(rename_tac ds f\<pi> fw)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(case_tac "restrict_newignore S1 i = []")
   apply(rename_tac ds \<pi>s fw)(*strict*)
   prefer 2
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "restrict_newignore S2 i \<noteq> []")
    apply(rename_tac ds \<pi>s fw)(*strict*)
    prefer 2
    apply(rule_tac
      t="restrict_newignore S2 i"
      and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
      in ssubst)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(rule_tac
      t="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
      and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
      in subst)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(rule_tac
      t="PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
      and s="restrict_newignore S1 i"
      in ssubst)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="liftB (ESplitItem_prods (S1 ! i)) = liftB (ESplitItem_prods (S2 ! i))"
      and s="(ESplitItem_prods (S1 ! i)) = (ESplitItem_prods (S2 ! i))"
      in ssubst)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(simp (no_asm))
     apply(rule impI)
     apply(rule liftB_inj)
     apply(blast)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(subgoal_tac "i \<le> length v")
    apply(rename_tac ds \<pi>s fw)(*strict*)
    prefer 2
    apply (metis Suc_length less_not_refl less_trans_Suc trivNat)
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    prefer 2
    apply(rule_tac
      i="i"
      and ?S1.0="S1"
      and n="length v"
      and v="v"
      and b="b"
      in e_derivation_can_be_embedded_minimally)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      prefer 2
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                     apply(rename_tac ds \<pi>s fw)(*strict*)
                     apply(force)
                    apply(rename_tac ds \<pi>s fw)(*strict*)
                    apply(force)
                   apply(rename_tac ds \<pi>s fw)(*strict*)
                   apply(force)
                  apply(rename_tac ds \<pi>s fw)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw)(*strict*)
               apply(force)
              apply(rename_tac ds \<pi>s fw)(*strict*)
              apply(force)
             apply(rename_tac ds \<pi>s fw)(*strict*)
             apply(force)
            apply(rename_tac ds \<pi>s fw)(*strict*)
            apply(force)
           apply(rename_tac ds \<pi>s fw)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    prefer 2
    apply(rule_tac
      i="i"
      and ?S1.0="S2"
      and n="length v"
      and v="v"
      and b="b"
      in e_derivation_can_be_embedded_minimally)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      prefer 2
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                      apply(rename_tac ds \<pi>s fw)(*strict*)
                      apply(force)
                     apply(rename_tac ds \<pi>s fw)(*strict*)
                     apply(force)
                    apply(rename_tac ds \<pi>s fw)(*strict*)
                    apply(force)
                   apply(rename_tac ds \<pi>s fw)(*strict*)
                   apply(force)
                  apply(rename_tac ds \<pi>s fw)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw)(*strict*)
               apply(force)
              apply(rename_tac ds \<pi>s fw)(*strict*)
              apply(force)
             apply(rename_tac ds \<pi>s fw)(*strict*)
             apply(force)
            apply(rename_tac ds \<pi>s fw)(*strict*)
            apply(force)
           apply(rename_tac ds \<pi>s fw)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)))\<rparr> (ESplitItem_prods ((S1 @ S1') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop i (take (length v) fw))) @ teB b # va\<rparr>)")
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! i)))\<rparr> (ESplitItem_prods ((S2 @ S2') ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop i (take (length v) fw))) @ teB b # va\<rparr>)")
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(subgoal_tac "length (nat_seq 0 (length v)) = SSx" for SSx)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(subgoal_tac "take (Suc (length v)) S1 = S1")
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    prefer 2
    apply(rule take_all)
    apply (metis Esplit_signature_length_max Suc_length)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(subgoal_tac "take (Suc (length v)) S2 = S2")
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    prefer 2
    apply(rule take_all)
    apply (metis Esplit_signature_length_max Suc_length)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(subgoal_tac "nat_seq 0 (length v) ! i = SSX" for SSX)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(erule_tac
      P="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i) \<noteq> []"
      in impE)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(rule_tac
      t="length S1"
      and s="Suc(length v)"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply (metis Suc_length)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(rule_tac
      t="min (length S1') (Suc (length v) - Suc (length v))"
      and s="0"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(rule_tac
      t="min (Suc (length v)) (Suc (length v)) + 0 - Suc 0"
      and s="length v"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(erule impE)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(rule_tac
      t="length S2"
      and s="Suc(length v)"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply (metis Suc_length)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(rule_tac
      t="min (length S2') (Suc (length v) - Suc (length v))"
      and s="0"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(rule_tac
      t="min (Suc (length v)) (Suc (length v)) + 0 - Suc 0"
      and s="length v"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "Suc i\<le>length v")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(case_tac "i=length v")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     prefer 2
     apply(rule_tac
      n="length v"
      and S="S2"
      in restrict_newignore_last_empty)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply (metis length_Suc)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule ESplitItem_to_not_empty_on_generating_line)
         apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "PSplitItem_to (restrict G' G (S2 @ S2') (Suc (length v)) ! i) = ESplitItem_to ((S2 @ S2') ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="length (Esplit_signature S1)"
      and s="Suc(length v)"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply (metis Suc_length)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(S2 @ S2') ! i"
      and s="S2!i"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule nonemtpy_newignore_implies_newto_unchanged)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! i) = ESplitItem_to ((S1 @ S1') ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
    apply(clarsimp)
    apply(rule_tac
      t="length (Esplit_signature S1)"
      and s="Suc(length v)"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply (metis Suc_length)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="(S1 @ S1') ! i"
      and s="S1!i"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule_tac
      t="take (Suc (length v)) S1"
      and s="S1"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(rule take_all)
     apply (metis Suc_length nat_neq_iff trivNat)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(rule nonemtpy_newignore_implies_newto_unchanged)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "Suc i < length S1")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply (metis Suc_n_not_n drop_length_append le_antisym le_trans length_append_empty1 list.simps(2) nat.inject trivNat)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(subgoal_tac "Suc i < length S2")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    prefer 2
    apply (metis Suc_n_not_n drop_length_append le_antisym le_trans length_append_empty1 list.simps(2) nat.inject trivNat)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
   apply(case_tac "ESplitItem_from (S1 ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(simp add: EValidSplit_def EValidSplit_producing_def)
    apply(clarsimp)
    apply(erule_tac
      x="S1!i"
      and A="set (butlast (S1 @ S1'))"
      in ballE)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     prefer 2
     apply(rule in_set_butlast_append2)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
   apply(case_tac "ESplitItem_from (S2 ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
    apply(simp add: EValidSplit_def EValidSplit_producing_def)
    apply(clarsimp)
    apply(erule_tac
      x="S2!i"
      and A="set (butlast (S2 @ S2'))"
      in ballE)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
     prefer 2
     apply(rule in_set_butlast_append2)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a a aa)(*strict*)
   apply(rename_tac F1 F2)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2)(*strict*)
   apply(case_tac "F1")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q ba)(*strict*)
    apply(rename_tac qF1 AF1)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 qF1 AF1)(*strict*)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    apply(subgoal_tac "ESplitItem_ignore (S1 ! i) = []")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
     prefer 2
     apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S1 ! i) @ option_to_list (Some (cons_l2 qF1 AF1)) @ ESplitItem_ignore (S1 ! i))")
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
      prefer 2
      apply(subgoal_tac "EValidSplitItem_belongs G (S1 ! i)")
       apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
       prefer 2
       apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
      apply(simp add: EValidSplitItem_belongs_def)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
     apply(simp (no_asm_use) add: option_to_list_def)
     apply(rule l2_in_proper_l3_l2_seq_at_end)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    apply(subgoal_tac "restrict_newignore S1 i = []")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
    apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)) (length (restrict_toberemovedX S1 ! Suc i)))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
     apply(rule drop_and_crop_length)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F2 qF1 AF1)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2)(*strict*)
   apply(case_tac "F2")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q baa)(*strict*)
    apply(rename_tac qF2 AF2)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 qF2 AF2)(*strict*)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    apply(subgoal_tac "ESplitItem_ignore (S2 ! i) = []")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
     prefer 2
     apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S2 ! i) @ option_to_list (Some (cons_l2 qF2 AF2)) @ ESplitItem_ignore (S2 ! i))")
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
      prefer 2
      apply(subgoal_tac "EValidSplitItem_belongs G (S2 ! i)")
       apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
       prefer 2
       apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
      apply(simp add: EValidSplitItem_belongs_def)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
     apply(simp (no_asm_use) add: option_to_list_def)
     apply(rule l2_in_proper_l3_l2_seq_at_end)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    apply(subgoal_tac "restrict_newignore S2 i = []")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
    apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S2 ! i) @ ESplitItem_ignore (S2 ! i)) (length (restrict_toberemovedX S2 ! Suc i)))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
     apply(rule drop_and_crop_length)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a q1 ba q2 qF2 AF2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(subgoal_tac "length (Esplit_signature S1) = Suc (length v)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
    prefer 2
    apply (metis Suc_length)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(subgoal_tac "length (Esplit_signature S2) = Suc (length v)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
    prefer 2
    apply (metis Suc_length)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rename_tac q11 A1 q12 q21 A2 q22)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    prefer 2
    apply(rule_tac
      \<alpha>="\<alpha>1"
      and \<pi>="e_\<pi>1"
      and d="e_d1"
      and A="(cons_l3 q11 A1 q12)"
      and w="liftA(butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S1 @ S1') ! i))))))"
      in from_derives_prefix)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(rule_tac
      t="[teA (cons_l3   q11 A1 q12)] @ liftA (butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S1 @ S1') ! i))))))"
      and s="liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore ((S1 @ S1') ! i))))))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp (no_asm))
     apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rule_tac
      t="(S1 @ S1') ! i"
      and s="S1!i"
      in ssubst)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp (no_asm_simp) add: option_to_list_def)
     apply(rule_tac
      t="PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)"
      and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)"
      in ssubst)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    prefer 2
    apply(rule_tac
      d="e_d1a"
      and A="(cons_l3 q21 A2 q22)"
      and w="liftA(butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S2 @ S2') ! i))))))"
      in from_derives_prefix)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(rule_tac
      t="[teA (cons_l3   q21 A2 q22)] @ liftA (butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S2 @ S2') ! i))))))"
      and s="liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S2 @ S2') ! i))))))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp (no_asm))
     apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rule_tac
      t="(S2 @ S2') ! i"
      and s="S2!i"
      in ssubst)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
     apply(simp (no_asm_simp) add: option_to_list_def)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(thin_tac "cfgLM.trans_der G e_d1a \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! i))) (ESplitItem_ignore ((S2 @ S2') ! i))))))\<rparr> e_\<pi>1a \<lparr>cfg_conf = liftB \<alpha>1a\<rparr>")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(thin_tac "cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore ((S1 @ S1') ! i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr>")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d1 e_d1a e_d2 e_d2a va vaa e_\<pi>1 e_\<pi>1a e_\<pi>2 e_\<pi>2a \<alpha>1 \<alpha>2 \<alpha>1a \<alpha>2a F1 F2 q11 A1 q12 q21 A2 q22)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(subgoal_tac "ESplitItem_from (S1 ! i) = ESplitItem_from (S2 ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(rule_tac
      t="ESplitItem_from (S1 ! i)"
      and s="Some (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
     apply(rule cropTol3l2_ID)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(rule_tac
      t="ESplitItem_from (S2 ! i)"
      and s="Some (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! i))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(simp (no_asm_simp))
     apply(rule cropTol3l2_ID)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 q21 A2 q22 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and G'="G"
      and ?d1.0="d1a"
      and ?d2.0="d1aa"
      and ?x1.0="\<alpha>2b@\<alpha>2"
      and ?x2.0="\<alpha>2c@\<alpha>2a"
      in eliminating_derivations_are_equal_with_differing_future6)
           apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
          apply(simp add: F2LR1inputx_def)
         apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
         apply(simp add: F2LR1inputx_def)
        apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
        apply(simp add: F2LR1inputx_def)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
       apply(simp add: F2LR1inputx_def)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1 \<pi>1a \<pi>2 \<alpha>1b \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(subgoal_tac "EValidSplitItem_gen G (S1 ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(subgoal_tac "EValidSplitItem_gen G (S2 ! i)")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      v="\<pi>1a"
      in equal_by_length_and_prefix_of_greater)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     prefer 2
     apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S1 ! i)) \<or> SSX" for SSX)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      prefer 2
      apply(rule_tac
      b="\<pi>2 @ e_\<pi>2"
      and d="\<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))"
      in mutual_strict_prefix_prefix)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      apply(rule sym)
      apply(rule_tac
      t="S1 ! i"
      and s="(S1@S1') ! i"
      in subst)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
       apply(rule nth_append_1)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(erule disjE)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(simp add: strict_prefix_def)
     apply(clarsimp)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(subgoal_tac "c=[]")
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(rule_tac
      ?d1.0="d1a"
      and ?d2.0="d"
      in unique_generation_length)
        apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    prefer 2
    apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S2 ! i)) \<or> SSX" for SSX)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     prefer 2
     apply(rule_tac
      b="\<pi>2a @ e_\<pi>2a"
      and d="\<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))"
      in mutual_strict_prefix_prefix)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(rule sym)
     apply(rule_tac
      t="S2 ! i"
      and s="(S2@S2') ! i"
      in subst)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(erule disjE)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(subgoal_tac "c=[]")
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(rule_tac
      ?d1.0="d1aa"
      and ?d2.0="da"
      in unique_generation_length)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "prefix (ESplitItem_prods (S1 ! i)) \<pi>1a")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S1 ! i)) \<or> SSX" for SSX)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(rule_tac
    b="\<pi>2 @ e_\<pi>2"
    and d="\<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))"
    in mutual_strict_prefix_prefix)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="S1 ! i"
    and s="(S1@S1') ! i"
    in subst)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(rule_tac
    ?d1.0="d1a"
    and ?d2.0="d"
    in unique_generation_length)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "prefix (ESplitItem_prods (S2 ! i)) \<pi>1a")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(subgoal_tac "strict_prefix \<pi>1a (ESplitItem_prods (S2 ! i)) \<or> SSX" for SSX)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(rule_tac
    b="\<pi>2a @ e_\<pi>2a"
    and d="\<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))"
    in mutual_strict_prefix_prefix)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="S2 ! i"
    and s="(S2@S2') ! i"
    in subst)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(subgoal_tac "c=[]")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(rule_tac
    ?d1.0="d1aa"
    and ?d2.0="da"
    in unique_generation_length)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da c)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(subgoal_tac " ESplitItem_elem (S1 ! i) = Some ((v@[teB b])!i) \<and> ESplitItem_elem (S2 ! i) = Some ((v@[teB b])!i) ")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  prefer 2
  apply(rule conjI)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(rule Esplit_signature_take_prefix_closureise)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(rule Esplit_signature_take_prefix_closureise)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da)(*strict*)
  apply(clarsimp)
  apply(case_tac "Esplit_signature S1 ! i")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S1 ! i)) < length (ESplitItem_prods (S2 ! i))")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(subgoal_tac "strict_prefix (ESplitItem_prods (S1 ! i)) (ESplitItem_prods (S2 ! i))")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    prefer 2
    apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(simp add: strict_prefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(rule_tac
    v="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in left_degen_repetitions_in_parallel_derivation)
         apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S2 ! i)) < length (ESplitItem_prods (S1 ! i))")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(subgoal_tac "strict_prefix (ESplitItem_prods (S2 ! i)) (ESplitItem_prods (S1 ! i))")
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    prefer 2
    apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
   apply(simp add: strict_prefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(rule_tac
    v="[]"
    and ?d1.0="da"
    and ?d2.0="d"
    in left_degen_repetitions_in_parallel_derivation)
         apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a c ca cb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(clarsimp)
  apply(case_tac "length (ESplitItem_prods (S1 ! i)) < length (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_prods (S1 ! i)) (ESplitItem_prods (S2 ! i))")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   prefer 2
   apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(rule_tac
    v="[]"
    and ?d1.0="d"
    and ?d2.0="da"
    in terminal_production_repetitions_in_parallel_derivation)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S2 ! i)) < length (ESplitItem_prods (S1 ! i))")
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_prods (S2 ! i)) (ESplitItem_prods (S1 ! i))")
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   prefer 2
   apply(rule_tac
    v="\<pi>1a"
    in strict_prefix_from_prefix_of_longer_and_shorter)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(rule_tac
    v="[]"
    and ?d1.0="da"
    and ?d2.0="d"
    in terminal_production_repetitions_in_parallel_derivation)
       apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba c ca cb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw p_d p_da e_d2 e_d2a va vaa e_\<pi>2 e_\<pi>2a \<alpha>2 \<alpha>2a q11 A1 q12 d1a d1aa \<pi>1a \<pi>2 \<pi>2a \<alpha>1c \<alpha>2b \<alpha>2c d da ba)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "restrict_newignore S2 i = []")
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply(rule_tac
    t="restrict_newignore S2 i"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
    in subst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
    and s="restrict_newignore S1 i"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "map (prod_to_edge G') (ESplitItem_prods (S1 ! i)) = map (prod_to_edge G') (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(rule_tac
    t="liftA (map (prod_to_edge G') (ESplitItem_prods (S1 ! i)))"
    and s="PSplitItem_prods ((restrictX G' [restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i])!0)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrictX_def)
  apply(clarsimp)
  apply(rule sym)
  apply(simp add: restrict_newprods_def)
  apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="liftA (map (prod_to_edge G') (ESplitItem_prods (S2 ! i)))"
    and s="PSplitItem_prods ((restrictX G' [restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i])!0)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrictX_def)
  apply(clarsimp)
  apply(rule sym)
  apply(simp add: restrict_newprods_def)
  apply(rule equal_split_prefix_hlp1_triv_eq)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S1 ! i)) - Suc 0)) = SSx" for SSx)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0)) = SSx" for SSx)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "length (ESplitItem_prods (S1 ! i)) = length (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply (rule map_eq_imp_length_eq)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(simp only: restrict_newprodsX_def)
  apply(subgoal_tac " ESplitItem_prods (S1 ! i) = [] \<longleftrightarrow> ESplitItem_prods (S2 ! i) = [] ")
  apply(rename_tac ds \<pi>s fw)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(case_tac "ESplitItem_prods (S1 ! i) = []")
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="(if ESplitItem_prods (S1 ! i) = [] then [] else map (\<lambda>ia. if restrict_newprodsXX G ia (ESplitItem_prods (S1 ! i)) (ESplitItem_elem (S1 ! i)) (restrict_newto S1 i) then teB (ESplitItem_prods (S1 ! i) ! ia) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (ESplitItem_prods (S1 ! i) ! ia))) (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0)))"
    and s="map (\<lambda>ia. if restrict_newprodsXX G ia (ESplitItem_prods (S1 ! i)) (ESplitItem_elem (S1 ! i)) (restrict_newto S1 i) then teB (ESplitItem_prods (S1 ! i) ! ia) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (ESplitItem_prods (S1 ! i) ! ia))) (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule_tac
    t="(if ESplitItem_prods (S2 ! i) = [] then [] else map (\<lambda>ia. if restrict_newprodsXX G ia (ESplitItem_prods (S2 ! i)) (ESplitItem_elem (S2 ! i)) (restrict_newto S2 i) then teB (ESplitItem_prods (S2 ! i) ! ia) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (ESplitItem_prods (S2 ! i) ! ia))) (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0)))"
    and s="(map (\<lambda>ia. if restrict_newprodsXX G ia (ESplitItem_prods (S2 ! i)) (ESplitItem_elem (S2 ! i)) (restrict_newto S2 i) then teB (ESplitItem_prods (S2 ! i) ! ia) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (ESplitItem_prods (S2 ! i) ! ia))) (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0)))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(rule listEqI)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(rule impI)
  apply(simp (no_asm_use))
  apply(rule_tac
    t="(map SSf SSw)!ia" for SSf SSw
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(rule nth_map)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(rule_tac
    t="(map SSf SSw)!ia" for SSf SSw
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(rule nth_map)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0) ! ia = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length (ESplitItem_prods (S1 ! i)) - Suc 0) ! ia = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(case_tac "ESplitItem_elem (S1 ! i)")
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(clarsimp)
  apply(erule_tac
    x="S1!i"
    and A="set (butlast (S1 @ S1'))"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(subgoal_tac "S1 ! i \<in> set (butlast (S1 @ S1'))")
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(rule nth_in_butlast_append)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(case_tac "ESplitItem_elem (S2 ! i)")
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(clarsimp)
  apply(erule_tac
    x="S2!i"
    and A="set (butlast (S2 @ S2'))"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(subgoal_tac "S2 ! i \<in> set (butlast (S2 @ S2'))")
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(rule nth_in_butlast_append)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia a aa)(*strict*)
  apply(rename_tac X1 X2)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(subgoal_tac "X1=X2")
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  prefer 2
  apply(rule_tac
    t="X1"
    and s="PSplitItem_elem (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(rule_tac
    t="X2"
    and s="PSplitItem_elem (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X2)(*strict*)
  apply(rename_tac X)
  apply(rename_tac ds \<pi>s fw ia X1 X)(*strict*)
  apply(case_tac "ESplitItem_from (S1 ! i)")
  apply(rename_tac ds \<pi>s fw ia X1 X)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X)(*strict*)
  apply(erule_tac
    x="S1!i"
    and A="set (butlast (S1 @ S1'))"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia X)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X)(*strict*)
  apply(rule nth_in_butlast_append2)
   apply(rename_tac ds \<pi>s fw ia X)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X a)(*strict*)
  apply(case_tac "ESplitItem_from (S2 ! i)")
  apply(rename_tac ds \<pi>s fw ia X1 X a)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
  apply(erule_tac
    x="S2!i"
    and A="set (butlast (S2 @ S2'))"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
  apply(rule nth_in_butlast_append2)
   apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X a aa)(*strict*)
  apply(rename_tac F1 F2)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(subgoal_tac "cropTol3l2_single F1 = cropTol3l2_single F2")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  prefer 2
  apply(rule_tac
    t="cropTol3l2_single F1"
    and s="PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(rule_tac
    t="cropTol3l2_single F2"
    and s="PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S1 ! i)")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(subgoal_tac "EValidSplitItem_gen G (S2 ! i)")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2)(*strict*)
  apply(simp (no_asm_use) only: EValidSplitItem_gen_def)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 d da)(*strict*)
  apply(rename_tac dx1 dx2)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "restrict_newto S2 i = restrict_newto S1 i")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(rule_tac
    t="restrict_newto S1 i"
    and s="PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(rule_tac
    t="restrict_newto S2 i"
    and s="PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "notfinishingL (ESplitItem_prods (S1 ! i))")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a)(*strict*)
  apply(rule_tac
    xs="ESplitItem_to (S1 ! i)"
    in rev_cases)
   apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
   apply(rule_tac
    w="[]"
    and B="a"
    and d="dx1"
    in trans_der_notfinishingL)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    w="teA a#liftA ys"
    and B="y"
    and d="dx1"
    in trans_der_notfinishingL)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
  apply(rule_tac
    xs="ESplitItem_to (S1 ! i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="ESplitItem_prods (S1 ! i)"
    in rev_cases)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   prefer 2
   apply(rule_tac
    G="G"
    and d="dx1"
    and i="length ys"
    and kleene_starT="False"
    and END="True"
    in cfgLM.trans_der_step_detail)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(erule_tac
    x="dx1"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F1]\<rparr>"
    in allE)
  apply(erule_tac
    x="ys"
    in allE)
  apply(erule_tac
    x="ci"
    in allE)
  apply(erule impE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
    prefer 2
    apply(simp add: option_to_list_def)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(rule_tac
    m="Suc 0"
    and v="[Some y]"
    in get_labels_drop_tail)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(erule impE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(rule_tac
    x="[]"
    in exI)
   apply(clarsimp)
   apply(rule_tac
    x="[X]" for X
    in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r w1 w2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
  apply(thin_tac "\<forall>ia<length (ESplitItem_prods (S2 ! i)). hd (cfg_conf (the (get_configuration (dx2 ia)))) \<noteq> teB ba")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
  apply(erule_tac
    x="length ys"
    in allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "l=liftB w1")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
   prefer 2
   apply (metis split_decide1)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
  apply(case_tac w1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
   prefer 2
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(case_tac "prod_rhs y")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
    x="y"
    in ballE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(rule_tac
    w="teB ba#liftA ys"
    and B="y"
    and d="dx1"
    in trans_der_notfinishingL)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "notfinishingL (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a)(*strict*)
  apply(rule_tac
    xs="ESplitItem_to (S2 ! i)"
    in rev_cases)
   apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
   apply(rule_tac
    w="[]"
    and B="a"
    and d="dx2"
    in trans_der_notfinishingL)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    w="teA a#liftA ys"
    and B="y"
    and d="dx2"
    in trans_der_notfinishingL)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 a ys y)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2 ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
  apply(rule_tac
    xs="ESplitItem_to (S2 ! i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="ESplitItem_prods (S2 ! i)"
    in rev_cases)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   prefer 2
   apply(rule_tac
    G="G"
    and d="dx2"
    and i="length ys"
    and kleene_starT="False"
    and END="True"
    in cfgLM.trans_der_step_detail)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(erule_tac
    x="dx2"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F2]\<rparr>"
    in allE)
  apply(erule_tac
    x="ys"
    in allE)
  apply(erule_tac
    x="ci"
    in allE)
  apply(erule impE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
    prefer 2
    apply(simp add: option_to_list_def)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(rule_tac
    m="Suc 0"
    and v="[Some y]"
    in get_labels_drop_tail)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(erule impE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
   apply(rule_tac
    x="[]"
    in exI)
   apply(clarsimp)
   apply(rule_tac
    x="[X]" for X
    in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r w1 w2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e ci l r w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
  apply(thin_tac "\<forall>i<Suc (length ys). hd (cfg_conf (the (get_configuration (dx1 i)))) \<noteq> teB ba")
  apply(erule_tac
    x="length ys"
    in allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "l=liftB w1")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
   prefer 2
   apply (metis split_decide1)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e l r w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e r w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
  apply(case_tac w1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
   prefer 2
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e w1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(case_tac "prod_rhs y")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   apply(clarsimp)
   apply(case_tac list)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
    x="y"
    in ballE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y e list baa A B)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(rule_tac
    w="teB ba#liftA ys"
    and B="y"
    and d="dx2"
    in trans_der_notfinishingL)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba ys y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "\<forall>p\<in> set (butlast (ESplitItem_prods (S1 ! i))). \<forall>b A. prod_rhs p \<noteq> [teB b, teA A]")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A)(*strict*)
  apply(rule_tac
    xs="ESplitItem_prods (S1 ! i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k<length ys. ys!k=p")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  prefer 2
  apply (metis in_set_conv_nth)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx1"
    and i="k"
    and kleene_starT="False"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  apply(subgoal_tac "(ys @ [y]) ! k = ys!k")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  apply(clarsimp)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r cfg_confa)(*strict*)
  apply(case_tac ci')
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  prefer 2
  apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(erule_tac
    x="dx1"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F1]\<rparr>"
    in allE)
  apply(erule_tac
    x="take (Suc k) ys"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = l @ teB ba # teA A # r\<rparr>"
    in allE)
  apply(erule_tac
    P="cfgLMTD G dx1 \<lparr>cfg_conf = [teA F1]\<rparr> (take (Suc k) ys) \<lparr>cfg_conf = l @ teB ba # teA A # r\<rparr>"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(rule_tac
    t="min (length ys) (Suc k)"
    and s="Suc k"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    t="min (length ys) (Suc k)"
    and s="Suc k"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
  apply(rule_tac
    m="length (ys@[y])-Suc k"
    and v="map Some (drop(Suc k)(ys@[y]))"
    in get_labels_drop_tail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
   apply(clarsimp)
   apply (metis List.map_append append_take_drop_id_hlp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(erule_tac
    P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F1]\<rparr> = liftB w1 @ liftA w2"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    x="[X]" for X
    in exI)
  apply(clarsimp)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 a)(*strict*)
  apply(thin_tac "left_degen G dx2")
  apply(simp add: left_degen_def sat_refined_def)
  apply(erule_tac
    x="k"
    in allE)+
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(erule_tac
    x="Suc k"
    in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    eij="ea"
    and cij="\<lparr>cfg_conf = teB baa # liftA (ESplitItem_to (S1 ! i))\<rparr>"
    and ci="\<lparr>cfg_conf = liftB w1 @ liftA w2\<rparr>"
    and ei="Some (ys!k)"
    and d="dx1"
    and i="Suc k"
    and j="length (ys@[y])-Suc k"
    in cfgLM.derivation_monotonically_inc)
       apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (liftB w1 @ liftA w2) = w1")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_drop_liftA maxTermPrefix_term_string)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (teB baa # liftA (ESplitItem_to (S1 ! i))) = [baa]")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(case_tac l)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w)(*strict*)
  apply(case_tac w1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa)(*strict*)
   apply(case_tac w2)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list)(*strict*)
  apply(case_tac a)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb)(*strict*)
  apply(case_tac w1)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb)(*strict*)
  apply(case_tac w2)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "\<forall>p\<in> set (butlast (ESplitItem_prods (S2 ! i))). \<forall>b A. prod_rhs p \<noteq> [teB b, teA A]")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A)(*strict*)
  apply(rule_tac
    xs="ESplitItem_prods (S2 ! i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k<length ys. ys!k=p")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  prefer 2
  apply (metis in_set_conv_nth)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 p ba A ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx2"
    and i="k"
    and kleene_starT="False"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  apply(subgoal_tac "(ys @ [y]) ! k = ys!k")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r)(*strict*)
  apply(clarsimp)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r cfg_confa)(*strict*)
  apply(case_tac ci')
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e ci ci' l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  prefer 2
  apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(erule_tac
    x="dx2"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F2]\<rparr>"
    in allE)
  apply(erule_tac
    x="take (Suc k) ys"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = l @ teB ba # teA A # r\<rparr>"
    in allE)
  apply(erule_tac
    P="cfgLMTD G dx2 \<lparr>cfg_conf = [teA F2]\<rparr> (take (Suc k) ys) \<lparr>cfg_conf = l @ teB ba # teA A # r\<rparr>"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(rule_tac
    t="min (length ys) (Suc k)"
    and s="Suc k"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    t="min (length ys) (Suc k)"
    and s="Suc k"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
  apply(rule_tac
    m="length (ys@[y])-Suc k"
    and v="map Some (drop(Suc k)(ys@[y]))"
    in get_labels_drop_tail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
   apply(clarsimp)
   apply (metis List.map_append append_take_drop_id_hlp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r ea eb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(erule_tac
    P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F2]\<rparr> = liftB w1 @ liftA w2"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    x="[X]" for X
    in exI)
  apply(clarsimp)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 a)(*strict*)
  apply(thin_tac "left_degen G dx1")
  apply(simp add: left_degen_def sat_refined_def)
  apply(erule_tac
    x="k"
    in allE)+
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(erule_tac
    x="Suc k"
    in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    eij="eb"
    and cij="\<lparr>cfg_conf = teB baa # liftA (ESplitItem_to (S2 ! i))\<rparr>"
    and ci="\<lparr>cfg_conf = liftB w1 @ liftA w2\<rparr>"
    and ei="Some (ys!k)"
    and d="dx2"
    and i="Suc k"
    and j="length (ys@[y])-Suc k"
    in cfgLM.derivation_monotonically_inc)
       apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa ea eb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (liftB w1 @ liftA w2) = w1")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_drop_liftA maxTermPrefix_term_string)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (teB baa # liftA (ESplitItem_to (S2 ! i))) = [baa]")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(case_tac l)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w)(*strict*)
  apply(case_tac w1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa)(*strict*)
   apply(case_tac w2)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e l r w1 w2 baa w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list)(*strict*)
  apply(case_tac a)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w a list bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb)(*strict*)
  apply(case_tac w1)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb)(*strict*)
  apply(case_tac w2)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w2 baa list bb a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ba A ys y k e r w1 w2 baa w list bb a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "restrict_newprodsXX G (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0) ! ia) (ESplitItem_prods (S1 ! i)) (ESplitItem_elem (S1 ! i)) (restrict_newto S1 i) \<longleftrightarrow> restrict_newprodsXX G (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0) ! ia) (ESplitItem_prods (S2 ! i)) (ESplitItem_elem (S2 ! i)) (restrict_newto S2 i)")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(rule antisym)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(rule_tac
    ?dx1.0="dx1"
    and ?dx2.0="dx2"
    and ?F1.0="F1"
    and ?F2.0="F2"
    in restrict_newprodsXX_implication)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                    prefer 19
                    apply(force)
                   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                   apply(force)
                  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
               apply(simp add: option_to_list_def)
              apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
              apply(force)
             apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
             apply(simp add: option_to_list_def)
            apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
            apply(force)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
         apply(simp add: restrict_newto_def)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
        apply(rule_tac
    t="restrict_newto S1 i"
    and s="restrict_newto S2 i"
    in ssubst)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
        apply(simp (no_asm) add: restrict_newto_def)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
       apply(rule newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
      apply(rule_tac
    t="restrict_newto S1 i"
    and s="restrict_newto S2 i"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
      apply(rule newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(rule_tac
    ?dx1.0="dx2"
    and ?dx2.0="dx1"
    and ?F1.0="F2"
    and ?F2.0="F1"
    in restrict_newprodsXX_implication)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                    apply(force)
                   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                   prefer 19
                   apply(force)
                  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
               apply(force)
              apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
              apply(simp add: option_to_list_def)
             apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
             apply(force)
            apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
            apply(simp add: option_to_list_def)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
        apply(rule_tac
    t="restrict_newto S1 i"
    and s="restrict_newto S2 i"
    in ssubst)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
        apply(simp (no_asm) add: restrict_newto_def)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
       apply(simp add: restrict_newto_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
      apply(rule_tac
    t="restrict_newto S1 i"
    and s="restrict_newto S2 i"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
      apply(rule newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
     apply(rule newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0) ! ia) (ESplitItem_prods (S1 ! i)) (ESplitItem_elem (S1 ! i)) (restrict_newto S1 i)")
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw ia X1 X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(subgoal_tac "(map (prod_to_edge G') (ESplitItem_prods (S1 ! i)))!ia = (map (prod_to_edge G') (ESplitItem_prods (S2 ! i)))!ia")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(thin_tac "map (prod_to_edge G') (ESplitItem_prods (S1 ! i)) = map (prod_to_edge G') (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(simp add: prod_to_edge_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(simp add: restrict_newprodsXX_def)
  apply(simp add: option_to_list_def)
  apply(thin_tac "nat_seq 0 (length (ESplitItem_prods (S2 ! i)) - Suc 0) ! ia = ia")
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  prefer 2
  apply(rule_tac
    i="ia"
    and d="dx1"
    in cfgLM.trans_der_position_detail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
   apply(simp add: split_TSstructure_def)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
  prefer 2
  apply(rule_tac
    ?e1.0="e"
    and cI="ci"
    and n="ia"
    and d="dx1"
    in cfgLM.trans_der_skip_prime)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(subgoal_tac "prefix (realizable G (drop ia SSX)) (drop ia (ESplitItem_prods (S1 ! i)))" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  prefer 2
  apply(rule realizable_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
   apply(simp add: cfg_step_labels_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  prefer 2
  apply(rule_tac
    i="ia"
    and d="dx2"
    in cfgLM.trans_der_position_detail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
   apply(simp add: split_TSstructure_def)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
  prefer 2
  apply(rule_tac
    ?e1.0="ea"
    and cI="cia"
    and n="ia"
    and d="dx2"
    in cfgLM.trans_der_skip_prime)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(subgoal_tac "prefix (realizable G (drop ia SSX)) (drop ia (ESplitItem_prods (S2 ! i)))" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  prefer 2
  apply(rule realizable_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: cfg_step_labels_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  prefer 2
  apply(rule_tac
    \<pi>="drop ia (ESplitItem_prods (S1 ! i))"
    in unique_existence_of_realizable)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: cfg_step_labels_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  prefer 2
  apply(thin_tac "\<exists>!\<pi>'. \<exists>c. \<pi>' \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = drop ia (ESplitItem_prods (S1 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule_tac
    \<pi>="drop ia (ESplitItem_prods (S2 ! i))"
    in unique_existence_of_realizable)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: cfg_step_labels_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da)(*strict*)
  apply(clarify)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(subgoal_tac "realizable G (drop ia (ESplitItem_prods (S1 ! i))) = \<pi>'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  prefer 2
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S1 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S1 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S2 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S2 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(rule_tac
    d="d"
    and da="db"
    in realizable_eq_from_existence)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(simp add: cfg_step_labels_def)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(rule cfgLM.trans_der_all_step_labels)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(subgoal_tac "realizable G (drop ia (ESplitItem_prods (S2 ! i))) = \<pi>'a")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  prefer 2
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S1 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S1 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S2 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S2 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(rule_tac
    d="da"
    and da="dc"
    in realizable_eq_from_existence)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(simp add: cfg_step_labels_def)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(rule cfgLM.trans_der_all_step_labels)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(clarify)
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S1 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S1 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S1 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(thin_tac "\<forall>y y'. (\<exists>c. y \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = drop ia (ESplitItem_prods (S2 ! i)))) \<and> (\<exists>c. y' \<sqsubseteq> drop ia (ESplitItem_prods (S2 ! i)) \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = drop ia (ESplitItem_prods (S2 ! i)))) \<longrightarrow> y = y'")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(thin_tac "(e = Some (ESplitItem_prods (S1 ! i) ! (ia - Suc 0))) = (ea = Some (ESplitItem_prods (S2 ! i) ! (ia - Suc 0)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da \<pi>' \<pi>'a c ca db dc)(*strict*)
  apply(thin_tac "(0 < ia) = (ea = Some (ESplitItem_prods (S2 ! i) ! (ia - Suc 0)))")
  apply(thin_tac "(e = None) = (ea = None)")
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da c ca db dc)(*strict*)
  apply(case_tac ci)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da c ca db dc cfg_confa)(*strict*)
  apply(case_tac cia)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da c ca db dc cfg_confa cfg_confaa)(*strict*)
  apply(rename_tac x1 x2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e ci d ea cia da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = x1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterA x1"
    in exI)
  apply (rule liftA_filterA)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(erule_tac
    x="dx1"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F1]\<rparr>"
    in allE)
  apply(erule_tac
    x="(take ia (ESplitItem_prods (S1 ! i)))"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf=x1\<rparr>"
    in allE)
  apply(erule_tac
    P="cfgLMTD G dx1 \<lparr>cfg_conf = [teA F1]\<rparr> (take ia (ESplitItem_prods (S1 ! i))) \<lparr>cfg_conf = x1\<rparr>"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule_tac
    t="min (length (ESplitItem_prods (S2 ! i))) ia"
    and s="ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 eb ec ed ee ef eg)(*strict*)
  apply(rule_tac
    m="length (ESplitItem_prods (S1 ! i))-ia"
    and v="map Some (drop ia (ESplitItem_prods (S1 ! i)))"
    in get_labels_drop_tail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 eb ec ed ee ef eg)(*strict*)
   apply(clarsimp)
   apply (metis List.map_append append_take_drop_id)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(erule_tac
    P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F1]\<rparr> = liftB w1 @ liftA w2"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    x="[X]" for X
    in exI)
  apply(clarsimp)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w1 w2)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(case_tac w1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    eij="eb"
    and cij="\<lparr>cfg_conf = X # liftA (ESplitItem_to (S1 ! i))\<rparr>"
    and ei="e"
    and ci="\<lparr>cfg_conf = teB a # liftB list @ liftA w2\<rparr>"
    and d="dx1"
    and i="ia"
    and j="length (ESplitItem_prods (S1 ! i))-ia"
    in cfgLM.derivation_monotonically_inc)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (teB a # liftB list @ liftA w2) = a#list")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_pull_out append_Nil2 maxTermPrefix_liftA maxTermPrefix_shift)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w)(*strict*)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teA aa # liftA (ESplitItem_to (S1 ! i))) = []")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
   apply(subgoal_tac "a # list @ w = []")
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
   apply(rule_tac
    t="a # list @ w"
    and s="maxTermPrefix (teA aa # liftA (ESplitItem_to (S1 ! i)))"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w aa)(*strict*)
  apply (metis liftA.simps(2) liftA_commutes_over_concat maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w ba)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teB ba # liftA (ESplitItem_to (S1 ! i))) = [ba]")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 ba)(*strict*)
  apply(erule_tac
    x="ia"
    in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc x2 w2 a list w ba)(*strict*)
  apply (metis maxTermPrefix_pull_out liftA.simps(2) liftA_commutes_over_concat maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = x2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterA x2"
    in exI)
  apply (rule liftA_filterA)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(erule_tac
    x="dx2"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf = [teA F2]\<rparr>"
    in allE)
  apply(erule_tac
    x="(take ia (ESplitItem_prods (S2 ! i)))"
    in allE)
  apply(erule_tac
    x="\<lparr>cfg_conf=x2\<rparr>"
    in allE)
  apply(erule_tac
    P="cfgLMTD G dx2 \<lparr>cfg_conf = [teA F2]\<rparr> (take ia (ESplitItem_prods (S2 ! i))) \<lparr>cfg_conf = x2\<rparr>"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule_tac
    t="min (length (ESplitItem_prods (S2 ! i))) ia"
    and s="ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 l' eb ec ed ee ef eg)(*strict*)
  apply(rule_tac
    m="length (ESplitItem_prods (S2 ! i))-ia"
    and v="map Some (drop ia (ESplitItem_prods (S2 ! i)))"
    in get_labels_drop_tail)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 l' eb ec ed ee ef eg)(*strict*)
   apply(clarsimp)
   apply (metis List.map_append append_take_drop_id)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 l' eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(erule_tac
    P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F2]\<rparr> = liftB w1 @ liftA w2"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x2 l')(*strict*)
  apply(rule_tac
    x="[X]" for X
    in exI)
  apply(clarsimp)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w1 w2)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(case_tac w1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    eij="ec"
    and cij="\<lparr>cfg_conf = X # liftA (ESplitItem_to (S2 ! i))\<rparr>"
    and ei="ea"
    and ci="\<lparr>cfg_conf = teB a # liftB list @ liftA w2\<rparr>"
    and d="dx2"
    and i="ia"
    and j="length (ESplitItem_prods (S2 ! i))-ia"
    in cfgLM.derivation_monotonically_inc)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (teB a # liftB list @ liftA w2) = a#list")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_pull_out append_Nil2 maxTermPrefix_liftA maxTermPrefix_shift)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w)(*strict*)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teA aa # liftA (ESplitItem_to (S2 ! i))) = []")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
   apply(subgoal_tac "a # list @ w = []")
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
   apply(rule_tac
    t="a # list @ w"
    and s="maxTermPrefix (teA aa # liftA (ESplitItem_to (S2 ! i)))"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w aa)(*strict*)
  apply (metis liftA.simps(2) liftA_commutes_over_concat maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w ba)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teB ba # liftA (ESplitItem_to (S2 ! i))) = [ba]")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 ba)(*strict*)
  apply(erule_tac
    x="ia"
    in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 e d ea da c ca db dc l' w2 a list w ba)(*strict*)
  apply (metis maxTermPrefix_pull_out liftA.simps(2) liftA_commutes_over_concat maxTermPrefix_liftA)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc l' l'a)(*strict*)
  apply(rename_tac x1 x2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast x1)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    e="e"
    and v="liftA x1"
    and \<alpha>="[]"
    and w="[F1]"
    and d="dx1"
    and n="ia"
    in only_l3_nonterminals_butlast_preserved)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(clarsimp)
     apply(simp add: only_l3_nonterminals_def)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  apply(case_tac v1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list)(*strict*)
  apply(case_tac x1)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(subgoal_tac "x1=v2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(rule_tac liftA_inj)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast x2)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    e="ea"
    and v="liftA x2"
    and \<alpha>="[]"
    and w="[F2]"
    and d="dx2"
    and n="ia"
    in only_l3_nonterminals_butlast_preserved)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(clarsimp)
     apply(simp add: only_l3_nonterminals_def)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  apply(case_tac v1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list)(*strict*)
  apply(case_tac x2)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2 a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(subgoal_tac "x2=v2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 v2)(*strict*)
  apply(rule_tac liftA_inj)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "length (realizable G (drop ia (ESplitItem_prods (S1 ! i)))) = length (realizable G (drop ia (ESplitItem_prods (S2 ! i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="d"
    in realizable_length_eq)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
         apply (rule notfinishingL_drop)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply (rule notfinishingL_drop)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply (metis drop_map)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(erule_tac
    x="p"
    and A="set (butlast (ESplitItem_prods (S1 ! i)))"
    in ballE)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(subgoal_tac "p \<in> set (butlast (ESplitItem_prods (S1 ! i)))")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(rule_tac
    A="set (butlast (drop ia (ESplitItem_prods (S1 ! i))))"
    in set_mp)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
   apply (metis drop_butlast set_drop_subset)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(erule_tac
    x="p"
    and A="set (butlast (ESplitItem_prods (S2 ! i)))"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(subgoal_tac "p \<in> set (butlast (ESplitItem_prods (S2 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(rule_tac
    A="set (butlast (drop ia (ESplitItem_prods (S2 ! i))))"
    in set_mp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply (metis drop_butlast set_drop_subset)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 p ba A)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="db"
    and ?d2.0="dc"
    in prod_to_edge_eq_implies_same_terminal_production2)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(rule notfinishingL_prefix)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(rule notfinishingL_drop)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(rule notfinishingL_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(rule notfinishingL_drop)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(rule nth_drop2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(rule nth_drop2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(simp (no_asm))
  apply(rule same_source_edge_productions_have_similar_lhs)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(rule_tac
    A="set (ESplitItem_prods (S1 ! i))"
    in set_mp)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(simp add: cfg_step_labels_def)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(rule cfgLM.trans_der_all_step_labels)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
        apply(simp add: split_TSstructure_def)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(rule nth_mem)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(rule_tac
    A="set (ESplitItem_prods (S2 ! i))"
    in set_mp)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(simp add: cfg_step_labels_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(rule cfgLM.trans_der_all_step_labels)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(rule nth_mem)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(simp add: notfinishingL_def notfinishing_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(simp add: notfinishingL_def notfinishing_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    t="prod_to_edge G' ((ESplitItem_prods (S1 ! i)) ! ia)"
    and s="(map (prod_to_edge G') (ESplitItem_prods (S1 ! i)))!ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(metis nth_map)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    t="prod_to_edge G' ((ESplitItem_prods (S2 ! i)) ! ia)"
    and s="(map (prod_to_edge G') (ESplitItem_prods (S2 ! i)))!ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(metis nth_map)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(rule_tac
    ?x1.0="(ESplitItem_prods (S1 ! i))"
    and ?x2.0="(ESplitItem_prods (S2 ! i))"
    in equal_by_same_length_and_equal_embedding)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 \<alpha> v1 v2)(*strict*)
  apply(case_tac c)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 \<alpha> v1 v2 cfg_confa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da c ca db dc x1 x2 \<alpha> v1 v2 cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 e d ea da db dc x1 x2 \<alpha> v1 v2)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(thin_tac "(ia = 0) = (ea = None)")
  apply(rename_tac ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(subgoal_tac "derives G (drop ia (ESplitItem_prods (S1 ! i))) = liftB \<alpha> @ liftA v1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  prefer 2
  apply(simp add: derives_def)
  apply(rule_tac
    t="(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S1 ! i)))))]\<rparr> (realizable G (drop ia (ESplitItem_prods (S1 ! i)))) c)"
    and s="\<lparr>cfg_conf = liftB \<alpha> @ liftA v1\<rparr>"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(rule_tac
    a="\<lparr>cfg_conf = liftB \<alpha> @ liftA v1\<rparr>"
    in the_equality)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
   apply(rule_tac
    x="dz1"
    in exI)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
  apply(rule_tac
    ?d1.0="d"
    and ?d2.0="dz1"
    in cfgLM_trans_der_unique_result)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(subgoal_tac "derives G (drop ia (ESplitItem_prods (S2 ! i))) = liftB \<alpha> @ liftA v2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  prefer 2
  apply(simp add: derives_def)
  apply(rule_tac
    t="(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia (ESplitItem_prods (S2 ! i)))))]\<rparr> (realizable G (drop ia (ESplitItem_prods (S2 ! i)))) c)"
    and s="\<lparr>cfg_conf = liftB \<alpha> @ liftA v2\<rparr>"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(rule_tac
    a="\<lparr>cfg_conf = liftB \<alpha> @ liftA v2\<rparr>"
    in the_equality)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
   apply(rule_tac
    x="dz2"
    in exI)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
  apply(rule_tac
    ?d1.0="d"
    and ?d2.0="dz2"
    in cfgLM_trans_der_unique_result)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 x d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(clarsimp)
  apply(case_tac x1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx1"
    and i="ia"
    and kleene_starT="False"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x1 x2 \<alpha> v1 v2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2 a list)(*strict*)
  apply(rename_tac X1 x1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2 X1 x1)(*strict*)
  apply(case_tac x2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2 X1 x1)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx2"
    and i="ia"
    and kleene_starT="False"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 x2 \<alpha> v1 v2 X1 x1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 a list)(*strict*)
  apply(rename_tac X2 x2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "drop ia (ESplitItem_prods (S1 ! i)) = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule nth_drop2)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "drop ia (ESplitItem_prods (S2 ! i)) = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule nth_drop2)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac " (realizable G (ESplitItem_prods (S1 ! i) ! ia # drop (Suc ia) (ESplitItem_prods (S1 ! i)))) \<noteq> []")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule realizable_not_empty)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac " (realizable G (ESplitItem_prods (S2 ! i) ! ia # drop (Suc ia) (ESplitItem_prods (S2 ! i)))) \<noteq> []")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule realizable_not_empty)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "X1 = prod_lhs(ESplitItem_prods (S1 ! i) ! ia)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dy1"
    and i="0"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dz1"
    and i="0"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2 e ea ci' ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  apply(case_tac l)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2 e ea ci' ci'a l r la ra a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "X2 = prod_lhs(ESplitItem_prods (S2 ! i) ! ia)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dy2"
    and i="0"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dz2"
    and i="0"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
    apply(simp add: split_TSstructure_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 X2 x2 e ea ci' ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  apply(case_tac l)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 X2 x2 e ea ci' ci'a l r la ra a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 X2 x2 e ea ci' ci'a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 X1 x1 X2 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x2)(*strict*)
  apply(rule_tac
    xs="x1"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x2)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    d="dy1"
    and da="dy1"
    and \<pi>'="(ESplitItem_prods (S1 ! i) ! ia # drop (Suc ia) (ESplitItem_prods (S1 ! i)))"
    in realizable_eq_from_existence)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
      apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
       apply(simp add: cfg_step_labels_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
      apply(rule cfgLM.trans_der_all_step_labels)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = X # liftA (ESplitItem_to (S1 ! i))\<rparr> = \<lparr>cfg_conf = liftB \<alpha> @ liftA v1\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dy1"
    and ?d2.0="dz1"
    in cfgLM_trans_der_unique_result)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="X # liftA (ESplitItem_to (S1 ! i))"
    and v="X # liftA (restrict_newto S1 i)"
    in strict_prefix_contra)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(rule sym)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(thin_tac "X # liftA (ESplitItem_to (S1 ! i)) = liftB \<alpha> @ liftA v1")
  apply(clarsimp)
  apply(subgoal_tac "length (restrict_newto S1 i) \<le> length (ESplitItem_to (S1 ! i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply (metis liftA_preserves_length)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2)(*strict*)
  apply(simp (no_asm) add: restrict_newto_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x2 ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 ys y)(*strict*)
  apply(rename_tac x1 x1L)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 x1 x1L)(*strict*)
  apply(rule_tac
    xs="x2"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 x1 x1L)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 x1 x1L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 x1 x1L)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  prefer 2
  apply(rule_tac
    d="dy2"
    and da="dy2"
    and \<pi>'="(ESplitItem_prods (S2 ! i) ! ia # drop (Suc ia) (ESplitItem_prods (S2 ! i)))"
    in realizable_eq_from_existence)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
      apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
       apply(simp add: cfg_step_labels_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
      apply(rule cfgLM.trans_der_all_step_labels)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = X # liftA (ESplitItem_to (S2 ! i))\<rparr> = \<lparr>cfg_conf = liftB \<alpha> @ liftA v2\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dy2"
    and ?d2.0="dz2"
    in cfgLM_trans_der_unique_result)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    w="liftB \<alpha> @ liftA v2"
    and x="X # liftA (ESplitItem_to (S2 ! i))"
    and v="X # liftA (restrict_newto S2 i)"
    in strict_prefix_contra)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(rule sym)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(thin_tac "X # liftA (ESplitItem_to (S2 ! i)) = liftB \<alpha> @ liftA v2")
  apply(clarsimp)
  apply(rule_tac
    t="restrict_newto S1 i"
    and s="restrict_newto S2 i"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(subgoal_tac "length (restrict_newto S2 i) \<le> length (ESplitItem_to (S2 ! i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply (metis liftA_preserves_length)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L)(*strict*)
  apply(simp (no_asm) add: restrict_newto_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x2 x1 x1L ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L ys y)(*strict*)
  apply(rename_tac x2 x2L)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L)(*strict*)
  apply(case_tac "ESplitItem_prods (S1 ! i) ! ia")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac X1 r1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1)(*strict*)
  apply(case_tac "ESplitItem_prods (S2 ! i) ! ia")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 prod_lhs prod_rhsa)(*strict*)
  apply(rename_tac X2 r2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2)(*strict*)
  apply(case_tac X1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 X2 r2 q ba)(*strict*)
  apply(rule only_l3_nonterminals_l2_at_front)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2)(*strict*)
  apply(case_tac X2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q1 ba q2 q baa)(*strict*)
  apply(rule only_l3_nonterminals_l2_at_front)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dz1"
    and ?d2.0="dz2"
    in cropTol3l2_single_equal_of_compatible_derivations)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
    apply(rule_tac
    x="ia"
    and ?x1.0="(ESplitItem_prods (S1 ! i))"
    and ?x2.0="(ESplitItem_prods (S2 ! i))"
    in equal_by_same_length_and_equal_embedding)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
       apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
        apply(rule nth_drop2)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
      apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
       apply(rule nth_drop2)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rule notfinishingL_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rule_tac
    t="\<lparr>prod_lhs = X1, prod_rhs = r1\<rparr>"
    and s="ESplitItem_prods (S1 ! i) ! ia"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
    apply(rule nth_drop2)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rule notfinishingL_drop)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(rule notfinishingL_prefix)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(rule_tac
    t="\<lparr>prod_lhs = X2, prod_rhs = r2\<rparr>"
    and s="ESplitItem_prods (S2 ! i) ! ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(rule nth_drop2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(rule notfinishingL_drop)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(subgoal_tac "q1a = q1 \<and> ba = baa")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  prefer 2
  apply(simp add: cropTol3l2_single_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L X1 r1 X2 r2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q1 q2 ba q2a)(*strict*)
  apply(thin_tac "cropTol3l2_single (cons_l3 q1 ba q2) = cropTol3l2_single (cons_l3 q1 ba q2a)")
  apply(rename_tac q q1 c q2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(case_tac "v1=[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "v2=[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dz1"
    and ?d2.0="dz2"
    in compatible_derivation_reach_empty_configuration_synchronously_ext)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(rule_tac
    x="ia"
    and ?x1.0="(ESplitItem_prods (S1 ! i))"
    and ?x2.0="(ESplitItem_prods (S2 ! i))"
    in equal_by_same_length_and_equal_embedding)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(rule nth_drop2)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(rule nth_drop2)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule notfinishingL_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr>"
    and s="ESplitItem_prods (S1 ! i) ! ia"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(rule nth_drop2)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule notfinishingL_drop)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule notfinishingL_prefix)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr>"
    and s="ESplitItem_prods (S2 ! i) ! ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule nth_drop2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule notfinishingL_drop)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  prefer 2
  apply(rule_tac
    ?\<pi>1'.0="[]"
    and ?\<pi>2'.0="[]"
    and ?d1.0="dz1"
    and ?d2.0="dz2"
    in compatible_derivations_coincide_heavily)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
    x="ia"
    and ?x1.0="(ESplitItem_prods (S1 ! i))"
    and ?x2.0="(ESplitItem_prods (S2 ! i))"
    in equal_by_same_length_and_equal_embedding)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(rule nth_drop2)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(rule nth_drop2)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q c q2)(*strict*)
  apply(rename_tac q1 c q2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
  apply(subgoal_tac "realizable G (\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) = realizable G (\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dz1"
    and ?d2.0="dz2"
    in same_l3_source_and_same_target_liftB_and_same_prod_to_edge_implies_equal_prods)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule notfinishingL_prefix)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r1\<rparr>"
    and s="ESplitItem_prods (S1 ! i) ! ia"
    in ssubst)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(rule nth_drop2)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule notfinishingL_drop)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
   apply(rule notfinishingL_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
   apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r2\<rparr>"
    and s="ESplitItem_prods (S2 ! i) ! ia"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
   apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule nth_drop2)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
   apply(rule notfinishingL_drop)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
  apply(rule_tac
    x="ia"
    and ?x1.0="(ESplitItem_prods (S1 ! i))"
    and ?x2.0="(ESplitItem_prods (S2 ! i))"
    in equal_by_same_length_and_equal_embedding)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
      apply(rule nth_drop2)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
     apply(rule nth_drop2)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2 ca cb)(*strict*)
  apply(case_tac "realizable G (\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2 ca cb)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2 ca cb a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "realizable G (\<lparr>prod_lhs = cons_l3 q1 c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2 ca cb a list)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> x1 x1L x2 x2L r1 r2 q1 c q2 ca cb a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(case_tac "v2=[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "v1=[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dz2"
    and ?d2.0="dz1"
    in compatible_derivation_reach_empty_configuration_synchronously_ext)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(rule_tac
    x="ia"
    and ?x1.0="(ESplitItem_prods (S2 ! i))"
    and ?x2.0="(ESplitItem_prods (S1 ! i))"
    in equal_by_same_length_and_equal_embedding)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(rule_tac
    t="drop ia (ESplitItem_prods (S2 ! i))"
    in ssubst)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
        apply(rule nth_drop2)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(rule_tac
    t="drop ia (ESplitItem_prods (S1 ! i))"
    in ssubst)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
       apply(rule nth_drop2)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule notfinishingL_prefix)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr>"
    and s="ESplitItem_prods (S2 ! i) ! ia"
    in ssubst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
    apply(rule nth_drop2)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule notfinishingL_drop)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule notfinishingL_prefix)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule_tac
    t="\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr>"
    and s="ESplitItem_prods (S1 ! i) ! ia"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule_tac
    t="SSX#SSY" for SSX SSY
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(rule nth_drop2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(rule notfinishingL_drop)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "ESplitItem_elem (S1 ! length v) = Some (teB b)")
  apply(rename_tac ds \<pi>s fw i X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  prefer 2
  apply (metis nth_append)
  apply(rename_tac ds \<pi>s fw i X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(case_tac "ESplitItem_to (S1 ! length v)")
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_to_empty_def)
  apply(clarsimp)
  apply(erule_tac
    x="S1!length v"
    and A="set (butlast (S1 @ S1'))"
    in ballE)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
   prefer 2
   apply (metis nth_in_butlast_append)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
  apply(case_tac "ESplitItem_to (S2 ! length v)")
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
  apply(simp add: EValidSplit_def EValidSplit_to_empty_def)
  apply(clarsimp)
  apply(erule_tac
    x="S2!length v"
    and A="set (butlast (S2 @ S2'))"
    in ballE)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
   prefer 2
   apply (metis nth_in_butlast_append)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 a list aa lista)(*strict*)
  apply(rename_tac t1 t1s t2 t2s)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  apply(subgoal_tac "restrict_newto S1 (length v) = [cropTol3l2_single (hd(ESplitItem_to (S1 ! length v)))]")
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  prefer 2
  apply(simp add: restrict_newto_def new_post_sig_def restrict_toberemovedX_def)
  apply(rule_tac
    t="(restrict_toberemoved S1 @ [tl (ESplitItem_to (last S1) @ ESplitItem_ignore (last S1))]) ! Suc (length v)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
   apply(rule nth_append_2)
   apply (metis length_0_conv length_Suc length_restrict_toberemoved less_irrefl_nat less_zeroE trivNat)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  apply(rule_tac
    t="Suc (length v) - length (restrict_toberemoved S1)"
    and s="0"
    in ssubst)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
   apply(simp add: length_restrict_toberemoved)
   apply (metis length_0_conv length_Suc length_restrict_toberemoved less_irrefl_nat less_zeroE trivNat)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  apply(clarsimp)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="last S1"
    and s="S1!length v"
    in ssubst)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
   apply (metis length_Suc nth_last)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  apply(simp (no_asm) add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ca cb)(*strict*)
  apply(rule_tac
    xs="ca"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ca cb ys y)(*strict*)
  apply(rule_tac
    xs="cb"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ca cb ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ca cb ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa)(*strict*)
  apply(case_tac "v1")
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa)(*strict*)
  prefer 2
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa a list)(*strict*)
  apply(case_tac \<alpha>)
   apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw i F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1 t1s t2 t2s ys ysa)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(subgoal_tac "i<length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  prefer 2
  apply (metis Suc_inject Suc_lessI Suc_less_eq length_Suc)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) \<sqsubseteq> (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(thin_tac "(\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) \<sqsubseteq> (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(thin_tac "derives G (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) = liftB \<alpha> @ liftA v1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(thin_tac "derives G (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) = liftB \<alpha> @ liftA v2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 ca cb)(*strict*)
  apply(rename_tac t1' t2')
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2')(*strict*)
  apply(rule_tac
    xs="t1'"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2')(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2' ys y)(*strict*)
  apply(rule_tac
    xs="t2'"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2' ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2' ys y ysa ya)(*strict*)
  apply(rename_tac bx1 bx1L bx2 bx2L)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 t1' t2' bx1 bx1L bx2 bx2L)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(subgoal_tac "case X of teA A \<Rightarrow> \<alpha> = [] | teB b \<Rightarrow> \<alpha>=[b]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L a)(*strict*)
  apply(case_tac "\<alpha>")
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L a)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba)(*strict*)
  apply(case_tac "\<alpha>")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba)(*strict*)
  apply(case_tac v1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba list)(*strict*)
  apply(case_tac list)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba a lista)(*strict*)
  apply(case_tac "restrict_newto S1 i")
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L ba a lista aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(subgoal_tac "PValidSplit_interlineX (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! i) (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(subgoal_tac "PValidSplit_interline (restrict G' G (S1 @ S1') (length (Esplit_signature S1)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(simp add: PValidSplit_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(simp add: PValidSplit_interline_def)
  apply(erule_tac
    x="i"
    in allE)
  apply(erule_tac
    P="Suc i < length (restrict G' G (S1 @ S1') (length (Esplit_signature S1)))"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rule_tac
    t="Esplit_signature S1"
    and s="v @ [teB b]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(thin_tac "v @ [teB b] = Esplit_signature S1")
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(subgoal_tac "PValidSplit_interlineX (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! i) (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(subgoal_tac "PValidSplit_interline (restrict G' G (S2 @ S2') (length (Esplit_signature S2)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(simp add: PValidSplit_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(simp add: PValidSplit_interline_def)
  apply(erule_tac
    x="i"
    in allE)
  apply(erule_tac
    P="Suc i < length (restrict G' G (S2 @ S2') (length (Esplit_signature S1)))"
    in impE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rule_tac
    t="Esplit_signature S1"
    and s="v @ [teB b]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(thin_tac "v @ [teB b] = Esplit_signature S1")
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(simp add: PValidSplit_interlineX_def)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(rule_tac
    i="Suc i"
    and ?S1.0="S1"
    and n="length v"
    and v="v"
    and b="b"
    in e_derivation_can_be_embedded_minimally)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    prefer 2
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                   apply(force)
                  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
               apply(force)
              apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
              apply(force)
             apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
             apply(force)
            apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
            apply(force)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  prefer 2
  apply(rule_tac
    i="Suc i"
    and ?S1.0="S2"
    and n="length v"
    and v="v"
    and b="b"
    in e_derivation_can_be_embedded_minimally)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    prefer 2
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                    apply(force)
                   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                   apply(force)
                  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                  apply(force)
                 apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                 apply(force)
                apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
                apply(force)
               apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
               apply(force)
              apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
              apply(force)
             apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
             apply(force)
            apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
            apply(force)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
           apply(force)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L p_d p_da)(*strict*)
  apply(rename_tac pd1 pd2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2. ESplitItem_prods ((S2 @ S2') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S2 @ S2') ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S2 @ S2') ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ [teB b] @ va\<rparr>)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i) = [] \<longrightarrow> drop (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S2 @ S2') ! Suc i)) = ESplitItem_ignore ((S2 @ S2') ! Suc i) \<and> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc i)))\<rparr> (ESplitItem_prods ((S2 @ S2') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ [teB b] @ va\<rparr>)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2. ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S1 @ S1') ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S1 @ S1') ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ [teB b] @ va\<rparr>)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore ((S1 @ S1') ! Suc i)) = ESplitItem_ignore ((S1 @ S1') ! Suc i) \<and> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i)))\<rparr> (ESplitItem_prods ((S1 @ S1') ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ [teB b] @ va\<rparr>)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(clarsimp)
  apply(simp add: fillWithPreContext_def)
  apply(subgoal_tac "\<exists>Y1. ESplitItem_from (S1 ! Suc i)= Some Y1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  prefer 2
  apply(subgoal_tac "(\<forall>x\<in> set (butlast (S1 @ S1')). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(erule_tac
    x="S1!Suc i"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  prefer 2
  apply(subgoal_tac "S1 ! Suc i \<in> set (butlast (S1 @ S1'))")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(thin_tac "S1 ! Suc i \<notin> set (butlast (S1 @ S1'))")
  apply(rule nth_in_butlast_append)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
   apply (metis Suc_lessI append_Nil length_1_cons_nth length_Suc less_not_refl less_trans_Suc list.size(3) not_less_eq)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(subgoal_tac "length S1 = Suc(length v)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply (metis Suc_lessI append_Nil length_1_cons_nth length_Suc less_not_refl less_trans_Suc list.size(3) not_less_eq)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(subgoal_tac "(S1 @ S1') ! Suc i = S1!Suc i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length (Esplit_signature S1) - Suc 0) ! Suc i = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(subgoal_tac "(fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S1 @ S1') ! Suc i))))) = Y1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule fillOpt_hd_and_last_back_state)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(clarsimp)
  apply(thin_tac "fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some Y1))) = Y1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(subgoal_tac "\<exists>Y2. ESplitItem_from (S2 ! Suc i)= Some Y2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(subgoal_tac "(\<forall>x\<in> set (butlast (S2 @ S2')). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_producing_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(erule_tac
    x="S2!Suc i"
    in ballE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  prefer 2
  apply(subgoal_tac "S2 ! Suc i \<in> set (butlast (S2 @ S2'))")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(thin_tac "S2 ! Suc i \<notin> set (butlast (S2 @ S2'))")
  apply(rule nth_in_butlast_append)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
   apply (metis Suc_lessI append_Nil length_1_cons_nth length_Suc less_not_refl less_trans_Suc list.size(3) not_less_eq)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "length S2 = Suc(length v)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply (metis Suc_lessI append_Nil length_1_cons_nth length_Suc less_not_refl less_trans_Suc list.size(3) not_less_eq)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "(S2 @ S2') ! Suc i = S2!Suc i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length (Esplit_signature S2) - Suc 0) ! Suc i = SSX" for SSX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "(fillOpt (PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S2 @ S2') ! Suc i))))) = Y2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule fillOpt_hd_and_last_back_state)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "fillOpt (PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some Y2))) = Y2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v)))) @ tl (ESplitItem_to ((S1 @ S1') ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ESplitItem_to ((S1 @ S1') ! length v) @ ESplitItem_ignore ((S1 @ S1') ! length v)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)) = ESplitItem_to ((S2 @ S2') ! length v) @ ESplitItem_ignore ((S2 @ S2') ! length v)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule append_take_drop_id_C)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) = take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule append_take_drop_id_C)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "fillOptL (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)))) = take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "length v1=length v2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)[1]
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
    ?x1.0="[]"
    and ?x2.0="[]"
    and n="length(\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i)))"
    and ?v1.0="\<alpha>"
    and ?v2.0="\<alpha>"
    and ?w1.0="v1"
    and ?w2.0="v2"
    and q="q"
    and A="c"
    and ?q1.0="q1"
    and ?q2.0="q2"
    and G="G'"
    and G'="G"
    and ?d1.0="dz1"
    and ?d2.0="dz2"
    in cfgLM_positions_remain_compatible_l3l3)
                apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
                apply(simp add: F2LR1inputx_def split_TSstructure_def)
               apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
               apply(simp add: F2LR1inputx_def split_TSstructure_def)
              apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
              apply(simp add: F2LR1inputx_def split_TSstructure_def)
             apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
             apply(simp add: F2LR1inputx_def split_TSstructure_def)
            apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
            apply(simp add: F2LR1inputx_def split_TSstructure_def)
           apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
           apply(simp add: F2LR1inputx_def split_TSstructure_def)
          apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
          apply(force)
         apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
         apply(force)
        apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
        apply(force)
       apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 e ea eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! Suc i) @ hd (cropTol3l2 (Y1 # restrict_newignore S1 (Suc i))) # restrict_newignore S1 (Suc i) = restrict_newto S1 i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule_tac
    P="\<lambda>X. X"
    and s="PSplitItem_elim (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) @ PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) # PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) = PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i) @ PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(thin_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) @ PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) # PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i) = PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i) @ PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S2 ! Suc i) @ hd (cropTol3l2 (Y2 # restrict_newignore S2 (Suc i))) # restrict_newignore S2 (Suc i) = restrict_newto S2 i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule_tac
    P="\<lambda>X. X"
    and s="PSplitItem_elim (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) @ PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) = PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i) @ PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(thin_tac "PSplitItem_elim (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) @ PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) = PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i) @ PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "restrictX G' [(restrict G' G (S1 @ S1') (length (Esplit_signature S1)))!(Suc i)] = restrictX G' [(restrict G' G (S2 @ S2') (length (Esplit_signature S2)))!(Suc i)]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule_tac
    t="restrictX G' [(restrict G' G (S1 @ S1') (length (Esplit_signature S1)))!(Suc i)]"
    and s="[(restrictX G' (restrict G' G (S1 @ S1') (length (Esplit_signature S1)))) !(Suc i)]"
    in subst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrictX_def)
  apply(rule_tac
    t="map (\<lambda>I. I\<lparr>PSplitItem_prods := map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (PSplitItem_prods I)\<rparr>) (restrict G' G (S1 @ S1') (length (Esplit_signature S1))) ! (Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   apply(rule nth_map)
   apply(clarsimp)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature S1) - Suc 0)) = SSx" for SSx)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(rule_tac
    t="restrictX G' [(restrict G' G (S2 @ S2') (length (Esplit_signature S2)))!(Suc i)]"
    and s="[(restrictX G' (restrict G' G (S2 @ S2') (length (Esplit_signature S2)))) !(Suc i)]"
    in subst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrictX_def)
  apply(rule_tac
    t="map (\<lambda>I. I\<lparr>PSplitItem_prods := map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p))) (PSplitItem_prods I)\<rparr>) (restrict G' G (S2 @ S2') (length (Esplit_signature S2))) ! (Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   apply(rule nth_map)
   apply(clarsimp)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (length (Esplit_signature S2) - Suc 0)) = SSx" for SSx)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_from (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)) = PSplitItem_from (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa)(*strict*)
  apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
  apply(clarsimp)
  apply(simp add: restrictX_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)) = PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa)(*strict*)
  apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_froma PSplitItem_ignoreaa PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
  apply(simp add: restrictX_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)) = PSplitItem_elim (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(case_tac "restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa)(*strict*)
  apply(case_tac "restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_fromaa PSplitItem_ignoreaa PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 PSplitItem_elima PSplitItem_elim_prodsa PSplitItem_prods PSplitItem_elema PSplitItem_toa PSplitItem_elimaa PSplitItem_froma PSplitItem_ignorea PSplitItem_elim_prodsaa PSplitItem_prodsa PSplitItem_elemaa PSplitItem_toaa)(*strict*)
  apply(simp add: restrictX_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! Suc i) = ESplitItem_elim (S2 ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="PSplitItem_elim (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S2 ! Suc i)"
    and s="PSplitItem_elim (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "EValidSplitItem_elim G (S1 ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(subgoal_tac "EValidSplit_ValidItem G (S1 @ S1')")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp add: EValidSplitItem_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(simp add: EValidSplitItem_elim_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  prefer 2
  apply(rule elim_map_to_trans_der)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
    prefer 4
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
   apply(simp add: F2LR1inputx_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(thin_tac "elim_map G (ESplitItem_elim (S2 ! Suc i)) (ESplitItem_elim_prods (S1 ! Suc i)) (map (\<lambda>x. []) (ESplitItem_elim_prods (S1 ! Suc i)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2)(*strict*)
  apply(erule exE)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 d)(*strict*)
  apply(rename_tac delim)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="delim"
    and ?d2.0="pd1"
    in cfgLMMIP_and_cfgLM_trans_der_append)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "(S1 @ S1') ! length v = S1!length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "ESplitItem_prods (S1 ! length v)\<noteq>[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  prefer 2
  apply(subgoal_tac "EValidSplitItem_gen G ((S1@S1') ! (length v))")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d)(*strict*)
   prefer 2
   apply(rule cfgLM.trans_der_equal_conf_if_empty_prods)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S1 ! length v)")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(case_tac "Suc(Suc i)\<le>length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) \<noteq> []")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
   prefer 2
   apply(rule_tac
    n="Suc (Suc i)"
    and m="length v"
    in nat_seq_drop_last2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim w)(*strict*)
  apply(rule_tac
    v="w"
    and n="length v"
    in foldl_map_not_empty_by_last)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim w)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim w)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(subgoal_tac "length v= Suc i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(thin_tac "cfgLMMIP G pd1 (teA Y1 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v)))) @ tl (ESplitItem_to ((S1 @ S1') ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd1 pd2 Y1 Y2 delim d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim d)(*strict*)
  apply(rename_tac pd1)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="delim"
    and ?d2.0="pd2"
    in cfgLMMIP_and_cfgLM_trans_der_append)
     apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "(S2 @ S2') ! length v = S2!length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "ESplitItem_prods (S2 ! length v)\<noteq>[]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  prefer 2
  apply(subgoal_tac "EValidSplitItem_gen G ((S2@S2') ! (length v))")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d)(*strict*)
   prefer 2
   apply(rule cfgLM.trans_der_equal_conf_if_empty_prods)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S2 ! length v)")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(case_tac "Suc(Suc i)\<le>length v")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) \<noteq> []")
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
   prefer 2
   apply(rule_tac
    n="Suc (Suc i)"
    and m="length v"
    in nat_seq_drop_last2)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 w)(*strict*)
  apply(rule_tac
    v="w"
    and n="length v"
    in foldl_map_not_empty_by_last)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 w)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 w)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(subgoal_tac "length v= Suc i")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(thin_tac "cfgLMMIP G pd2 (teA Y2 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)))) (ESplitItem_prods (S2 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L pd2 Y1 Y2 delim pd1 d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L Y1 Y2 delim pd1 d)(*strict*)
  apply(rename_tac pd2)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L Y1 Y2 delim pd1 pd2)(*strict*)
  apply(rule_tac
    xs="restrict_newto S1 i"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L Y1 Y2 delim pd1 pd2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L Y1 Y2 delim pd1 pd2 ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac nts ntL)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx1L bx2 bx2L Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply (simp add:liftA_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(subgoal_tac "restrict_newignore S1 (Suc i) = PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(subgoal_tac "restrict_newignore S2 (Suc i) = PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(subgoal_tac "restrict_newignore S1 (Suc i) = restrict_newignore S2 (Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  prefer 2
  apply(rule_tac
    t="restrict_newignore S1 (Suc i)"
    and s="PSplitItem_ignore (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(rule_tac
    t="restrict_newignore S2 (Suc i)"
    and s="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(rule_tac
    xs=" (ESplitItem_elim (S2 ! Suc i)) @ Y1 # (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  prefer 2
  apply(rule_tac
    \<alpha>'="[]"
    and w="ys"
    and A="y"
    and d="pd1"
    and \<alpha>="foldl (@) [] (drop (Suc i) (take (length v) fw))"
    and b="b"
    and v=" (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v))))) @ (tl (ESplitItem_to ((S1 @ S1') ! length v))) @ (butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)))"
    in cfgLMMIP_decompose_into_trans_der_and_cfgLMMIP)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(rule_tac
    t="liftB [] @ liftA (ys @ [y])"
    and s="liftA (ESplitItem_elim (S2 ! Suc i)) @ teA Y1 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(rule_tac
    t="ys@[y]"
    and s="ESplitItem_elim (S2 ! Suc i) @ Y1 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @Y1 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ys @ [y]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply (simp add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply (simp add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys y \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 d1a d2a)(*strict*)
  apply(rename_tac ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "cfgLMMIP G d12a [teA y1] \<pi>12 (liftB (\<alpha>12 @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v)))) @ tl (ESplitItem_to ((S1 @ S1') ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a)(*strict*)
  apply(thin_tac "cfgLMMIP G pd1 (liftA (ESplitItem_elim (S2 ! Suc i)) @ teA Y1 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S1 @ S1') ! length v))))) @ liftA (tl (ESplitItem_to ((S1 @ S1') ! length v))) @ liftA (butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a)(*strict*)
  apply(rule_tac
    xs=" (ESplitItem_elim (S2 ! Suc i)) @ Y2 # (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)))"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  prefer 2
  apply(rule_tac
    \<alpha>'="[]"
    and w="ys"
    and A="y"
    and d="pd2"
    and \<alpha>="foldl (@) [] (drop (Suc i) (take (length v) fw))"
    and b="b"
    and v=" (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v))))) @ (tl (ESplitItem_to ((S2 @ S2') ! length v))) @ (butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc i)))"
    in cfgLMMIP_decompose_into_trans_der_and_cfgLMMIP)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(rule_tac
    t="liftB [] @ liftA (ys @ [y])"
    and s="liftA (ESplitItem_elim (S2 ! Suc i)) @ teA Y2 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(rule_tac
    t="ys@[y]"
    and s="ESplitItem_elim (S2 ! Suc i) @ Y2 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i))"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @ Y2 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)) = ys @ [y]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply (simp add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply (simp add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys y \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 d1a d2a)(*strict*)
  apply(rename_tac ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "cfgLMMIP G d22a [teA y2] \<pi>22 (liftB (\<alpha>22 @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v)))) @ tl (ESplitItem_to ((S2 @ S2') ! length v)) @ butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(thin_tac "cfgLMMIP G pd2 (liftA (ESplitItem_elim (S2 ! Suc i)) @ teA Y2 # liftA (take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)))) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S2 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to ((S2 @ S2') ! length v))))) @ liftA (tl (ESplitItem_to ((S2 @ S2') ! length v))) @ liftA (butn (restrict_toberemoved S2 ! length v) (length (restrict_toberemoved S2 ! Suc i))))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(subgoal_tac "prefix nts ys1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  prefer 2
  apply(rule_tac
    A="ntL"
    and B="y1"
    in butlast_preserves_prefix_1)
  apply(rule_tac
    t="nts @ [ntL]"
    and s="ESplitItem_elim (S1 ! Suc i) @ hd (cropTol3l2 (Y1 # restrict_newignore S1 (Suc i))) # restrict_newignore S1 (Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    t="ys1@[y1]"
    and s="ESplitItem_elim (S2 ! Suc i) @ Y1 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule prefix_butlast_drop)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i)"
    and s="restrict_newignore S1 (Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    xs="restrict_newignore S1 (Suc i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 delim y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="butlast (hd (cropTol3l2 (Y1 # restrict_newignore S1 (Suc i))) # restrict_newignore S1 (Suc i))"
    and s="Y1#ys"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="restrict_newignore S1 (Suc i)"
    and s="ys@[y]"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(thin_tac "restrict_newignore S1 (Suc i) = ys @ [y]")
  apply(rule_tac
    t="butlast SSX" for SSX
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
   apply(rule_tac
    w="hd (cropTol3l2 (Y1 # ys @ [y])) # ys"
    in butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="restrict_newignore S1 (Suc i)"
    and s="ys@[y]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  prefer 2
  apply(rule_tac
    S="S1"
    and x="Suc i"
    in restrict_newignore_prefix_of_ESplitItem_ignore_butlast)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  prefer 2
  apply(rule_tac
    S="S1"
    and i="Suc i"
    in restrict_newignore_shorter_than_ESplitItem_ignore)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    xs="ESplitItem_ignore (S1 ! Suc i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(subgoal_tac "prefix ys ysa")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  prefer 2
  apply(rule_tac
    t="ys"
    and s="butlast(ys@[y])"
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ysa"
    and s="butlast(ysa@[ya])"
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ys@[y]"
    and s="restrict_newignore S1 (Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ysa@[ya]"
    and s="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(subgoal_tac "\<exists>w. ys@w=ysa")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    and s="ys@w@[ya]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(case_tac w)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(rule_tac
    t="w"
    and s="[]"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a ys y ysa ya w)(*strict*)
  apply(simp (no_asm) add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(rule_tac
    t="w"
    and s="a#list"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a ys y ysa ya w a list)(*strict*)
  apply(simp (no_asm) add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(subgoal_tac "prefix nts ys2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  prefer 2
  apply(rule_tac
    A="ntL"
    and B="y2"
    in butlast_preserves_prefix_1)
  apply(rule_tac
    t="nts @ [ntL]"
    and s="ESplitItem_elim (S2 ! Suc i) @ hd (cropTol3l2 (Y2 # restrict_newignore S2 (Suc i))) # restrict_newignore S2 (Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    t="ys2@[y2]"
    and s="ESplitItem_elim (S2 ! Suc i) @ Y2 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i))"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule prefix_butlast_drop)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    t="PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S2)) ! Suc i)"
    and s="restrict_newignore S2 (Suc i)"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(rule_tac
    xs="restrict_newignore S2 (Suc i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 delim y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="butlast (hd (cropTol3l2 (Y2 # restrict_newignore S2 (Suc i))) # restrict_newignore S2 (Suc i))"
    and s="Y2#ys"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="restrict_newignore S2 (Suc i)"
    and s="ys@[y]"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(thin_tac "restrict_newignore S2 (Suc i) = ys @ [y]")
  apply(rule_tac
    t="butlast SSX" for SSX
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
   apply(rule_tac
    w="hd (cropTol3l2 (Y2 # ys @ [y])) # ys"
    in butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    t="restrict_newignore S2 (Suc i)"
    and s="ys@[y]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  prefer 2
  apply(rule_tac
    S="S2"
    and x="Suc i"
    in restrict_newignore_prefix_of_ESplitItem_ignore_butlast)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  prefer 2
  apply(rule_tac
    S="S2"
    and i="Suc i"
    in restrict_newignore_shorter_than_ESplitItem_ignore)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(rule_tac
    xs="ESplitItem_ignore (S2 ! Suc i)"
    in rev_cases)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(subgoal_tac "prefix ys ysa")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  prefer 2
  apply(rule_tac
    t="ys"
    and s="butlast(ys@[y])"
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ysa"
    and s="butlast(ysa@[ya])"
    in subst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ys@[y]"
    and s="restrict_newignore S2 (Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(rule_tac
    t="ysa@[ya]"
    and s="ESplitItem_ignore (S2 ! Suc i)"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(subgoal_tac "\<exists>w. ys@w=ysa")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(rule_tac
    t="ESplitItem_ignore (S2 ! Suc i)"
    and s="ys@w@[ya]"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(case_tac w)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(rule_tac
    t="w"
    and s="[]"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a ys y ysa ya w)(*strict*)
  apply(simp (no_asm) add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(rule_tac
    t="w"
    and s="a#list"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys y ysa ya w a list)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a ys y ysa ya w a list)(*strict*)
  apply(simp (no_asm) add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(subgoal_tac "\<exists>ys1'. nts@ys1'=ys1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(subgoal_tac "\<exists>ys2'. nts@ys2'=ys2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="d11a"
    and ?w1.0="liftA nts"
    and ?w2.0="liftA ys1'"
    in cfgLM_trans_der_cfgLM_derivation_can_be_decomposed)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(rule_tac
    t="liftA nts @ liftA ys1'"
    and s="liftA ys1"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(rule_tac
    t="ys1"
    and s="nts@ys1'"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply (simp (no_asm) add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2')(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1a d2a \<pi>1 \<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(erule conjE)+
  apply(rename_tac d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1d \<lparr>cfg_conf = liftA ys1'\<rparr> \<pi>1d \<lparr>cfg_conf = liftB \<alpha>1d\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d11a \<lparr>cfg_conf = liftA ys1\<rparr> \<pi>11 \<lparr>cfg_conf = liftB \<alpha>11\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="d21a"
    and ?w1.0="liftA nts"
    and ?w2.0="liftA ys2'"
    in cfgLM_trans_der_cfgLM_derivation_can_be_decomposed)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(rule_tac
    t="liftA nts @ liftA ys2'"
    and s="liftA ys2"
    in ssubst)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(rule_tac
    t="ys2"
    and s="nts@ys2'"
    in ssubst)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply (simp (no_asm) add:liftA_commutes_over_concat)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d1a d2a \<pi>1 \<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(erule conjE)+
  apply(rename_tac d2c d2d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c d2d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2d \<lparr>cfg_conf = liftA ys2'\<rparr> \<pi>2d \<lparr>cfg_conf = liftB \<alpha>2d\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c d2d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d21a \<lparr>cfg_conf = liftA ys2\<rparr> \<pi>21 \<lparr>cfg_conf = liftB \<alpha>21\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim pd1 pd2 nts ntL ys1 y1 \<pi>11 \<pi>12 \<alpha>11 \<alpha>12 d11a d12a ys2 y2 \<pi>21 \<pi>22 \<alpha>21 \<alpha>22 d21a d22a ys1' ys2' d1c d1d \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c d2d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(thin_tac "nts \<sqsubseteq> (nts @ ys1')")
  apply(thin_tac "nts \<sqsubseteq> (nts @ ys2')")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(subgoal_tac "suffix (liftA nts) bx1")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  prefer 2
  apply(simp add: suffix_def)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
  apply(case_tac v1)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a list)(*strict*)
  apply(rule_tac
    x="liftA list"
    in exI)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ba)(*strict*)
  apply(rule_tac
    x="liftA v1"
    in exI)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(subgoal_tac "suffix (liftA nts) bx2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  prefer 2
  apply(thin_tac "suffix (liftA nts) bx1")
  apply(simp add: suffix_def)
  apply(case_tac X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
  apply(case_tac v2)
   apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d a list)(*strict*)
  apply(rule_tac
    x="liftA list"
    in exI)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ba)(*strict*)
  apply(rule_tac
    x="liftA v2"
    in exI)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ca cb)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2c \<lparr>cfg_conf = ca @ bx1\<rparr> \<pi>2c \<lparr>cfg_conf = liftB \<alpha>2c\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ca cb)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ca cb)(*strict*)
  prefer 2
  apply(rule liftA_append)
  apply(rule sym)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx1 bx2 Y1 Y2 delim nts ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d d2c \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
  apply(thin_tac "liftA (l1 @ l2) = liftA l1 @ liftA l2")
  apply(subgoal_tac "bx2=liftA l2")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
  prefer 2
  apply (rule equal_split_prefix_hlp1_hlp1)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
  apply (metis liftA_preserves_length)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 bx2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d cb l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="d1c"
    and ?w1.0="liftA l1"
    and ?w2.0="liftA l2"
    in cfgLM_trans_der_cfgLM_derivation_can_be_decomposed)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d1a d2a \<pi>1 \<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(erule conjE)+
  apply(rename_tac d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d3d \<lparr>cfg_conf = liftA l2\<rparr> \<pi>3d \<lparr>cfg_conf = liftB \<alpha>3d\<rparr> ")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1c \<lparr>cfg_conf = liftA l1 @ liftA l2\<rparr> \<pi>1c \<lparr>cfg_conf = liftB \<alpha>1c\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  prefer 2
  apply(rule_tac
    w="[X]"
    and G="G"
    in trans_der_construct_elimininating_derivation_prime)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(simp add: F2LR1inputx_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply (metis reachable_and_eliminiable_implies_eliminable2 reachable_and_eliminiable_implies_reachable)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = X # liftA (ESplitItem_to (S1 ! i))\<rparr> \<in> cfg_configurations G")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  prefer 2
  apply(rule cfgLM.trans_der_belongs_configurations2)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d d \<pi> va)(*strict*)
  apply(rename_tac dX \<pi>X vX)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and ?d1.0="dX"
    and ?d2.0="d3c"
    in cfgLM_trans_der_biextend_prime)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX)(*strict*)
  apply(erule exE)+
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3d \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX d)(*strict*)
  apply(rename_tac d3d)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3da \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dX \<lparr>cfg_conf = [X]\<rparr> \<pi>X \<lparr>cfg_conf = liftB vX\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3da \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d3c \<lparr>cfg_conf = liftA l1\<rparr> \<pi>3c \<lparr>cfg_conf = liftB \<alpha>3c\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' d1c \<pi>1c \<pi>1d \<alpha>1c \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 d3c d3da \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d dX \<pi>X vX d3d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G delim \<lparr>cfg_conf = liftA (ESplitItem_elim (S2 ! Suc i))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = []\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "\<alpha>3c @ \<alpha>3d @ \<alpha>1d @ \<alpha>12 = foldl (@) [] (drop (Suc i) (take (length v) fw))")
  apply(thin_tac "\<alpha>2c @ \<alpha>2d @ \<alpha>22 = foldl (@) [] (drop (Suc i) (take (length v) fw))")
  apply(thin_tac "\<pi>2c @ \<pi>2d @ \<pi>22 = foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S2 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S2 @ S2') ! x)) @ ESplitItem_prods ((S2 @ S2') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @ Y2 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S2 ! Suc i)) = l1 @ l2 @ ys2' @ [y2]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "restrict_newignore S2 (Suc i) = PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "restrict_newignore S1 (Suc i) = PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @ Y1 # take (length (PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = l1 @ l2 @ ys1' @ [y1]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @ hd (cropTol3l2 (Y2 # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) = l1 @ l2 @ [ntL]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! Suc i) @ hd (cropTol3l2 (Y1 # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i))) # PSplitItem_ignore (restrict G' G (S2 @ S2') (length (Esplit_signature S1)) ! Suc i) = l1 @ l2 @ [ntL]")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "\<pi>3c @ \<pi>3d @ \<pi>1d @ \<pi>12 = foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "only_l3_nonterminals (cons_l3 q c q1 # x1)")
  apply(thin_tac "only_l3_nonterminals (cons_l3 q c q2 # x2)")
  apply(thin_tac "ESplitItem_from (S1 ! Suc i) = Some Y1")
  apply(thin_tac "ESplitItem_from (S2 ! Suc i) = Some Y2")
  apply(thin_tac "realizable G (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) = \<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "realizable G (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) = \<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "(\<exists>b. teB b = X) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S2 ! i)). hd (cfg_conf (the (get_configuration (dx1 ia)))) \<noteq> X)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "(\<exists>A. teA A = X) \<longrightarrow> left_degen G dx1 \<and> ESplitItem_elim_prods (S1 ! i) = []")
  apply(thin_tac "cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw")
  apply(thin_tac "(\<exists>b. teB b = X) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S2 ! i)). hd (cfg_conf (the (get_configuration (dx2 ia)))) \<noteq> X)")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "(\<exists>A. teA A = X) \<longrightarrow> left_degen G dx2 \<and> ESplitItem_elim_prods (S2 ! i) = []")
  apply(thin_tac "cfgLM.trans_der G dy2 \<lparr>cfg_conf = teA (cons_l3   q c q2) # liftA x2 @ [teA x2L]\<rparr> (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) \<lparr>cfg_conf = X # liftA (ESplitItem_to (S2 ! i))\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dy1 \<lparr>cfg_conf = teA (cons_l3   q c q1) # liftA x1 @ [teA x1L]\<rparr> (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) \<lparr>cfg_conf = X # liftA (ESplitItem_to (S1 ! i))\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dx1 \<lparr>cfg_conf = [teA F1]\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = X # liftA (ESplitItem_to (S1 ! i))\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dx2 \<lparr>cfg_conf = [teA F2]\<rparr> (ESplitItem_prods (S2 ! i)) \<lparr>cfg_conf = X # liftA (ESplitItem_to (S2 ! i))\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "dx1 ia = Some (pair ex1 \<lparr>cfg_conf = teA (cons_l3   q c q1) # liftA x1 @ [teA x1L]\<rparr>)")
  apply(thin_tac "dx2 ia = Some (pair ex2 \<lparr>cfg_conf = teA (cons_l3   q c q2) # liftA x2 @ [teA x2L]\<rparr>)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  prefer 2
  apply(rule_tac
    ?v1.0="[]"
    and ?v4.0="[]"
    and G="G"
    and ?d1.0="dz1"
    and ?d2.0="d3d"
    in cfgLM_trans_der_concat_extend_prime)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  prefer 2
  apply(rule_tac
    ?v1.0="[]"
    and ?v4.0="[]"
    and G="G"
    and ?d1.0="dz2"
    and ?d2.0="d3d"
    in cfgLM_trans_der_concat_extend_prime)
   apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
   apply(simp add: split_TSstructure_def)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(force)
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dz1 \<lparr>cfg_conf = [teA (cons_l3   q c q1)]\<rparr> (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i))) \<lparr>cfg_conf = X # liftA l1\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dz2 \<lparr>cfg_conf = [teA (cons_l3   q c q2)]\<rparr> (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) \<lparr>cfg_conf = X # liftA l1\<rparr>")
  apply(rename_tac ds \<pi>s fw ia X F1 F2 dx1 dx2 ex1 dy1 ex2 dy2 dz1 dz2 \<alpha> v1 v2 x1 x1L x2 x2L r1 r2 q q1 c q2 Y1 Y2 delim ntL y1 \<pi>12 \<alpha>12 y2 \<pi>22 \<alpha>22 ys1' ys2' \<pi>1d \<alpha>1d \<pi>2c \<pi>2d \<alpha>2c \<alpha>2d l1 l2 \<pi>3c \<pi>3d \<alpha>3c \<alpha>3d \<pi>X vX d3d)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d da)(*strict*)
  apply(rename_tac d1x d2x)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  prefer 2
  apply(rule_tac
    \<pi>1'="[]"
    and \<pi>2'="[]"
    and ?\<alpha>1.0="vX@\<alpha>3c"
    and ?\<alpha>2.0="vX@\<alpha>3c"
    and G="G"
    and G'="G'"
    and ?d1.0="d1x"
    and ?d2.0="d2x"
    in compatible_derivations_coincide_heavily)
     apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
     apply(force)
    apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
    apply(force)
   apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
   apply (simp add: liftB_commutes_over_concat)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply (simp add: liftB_commutes_over_concat)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(subgoal_tac "map (prod_to_edge G') (\<lparr>prod_lhs = cons_l3 q c q1, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i)))= map (prod_to_edge G') (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) ")
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(force)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply (metis drop_map)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q q1 c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  prefer 2
  apply(rule_tac
    \<alpha>="vX@\<alpha>3c"
    and G="G"
    and G'="G'"
    and ?d1.0="d1x"
    and ?d2.0="d2x"
    in same_l3_source_and_same_target_liftB_and_same_prod_to_edge_implies_equal_prods)
       apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
       apply(assumption)
      apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
      apply(assumption)
     apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
     apply (simp add: liftB_commutes_over_concat)
    apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
    apply (simp add: liftB_commutes_over_concat)
   apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
   prefer 3
   apply(subgoal_tac "map (prod_to_edge G') (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r1\<rparr> # drop (Suc ia) (ESplitItem_prods (S1 ! i)))= map (prod_to_edge G') (\<lparr>prod_lhs = cons_l3 q c q2, prod_rhs = r2\<rparr> # drop (Suc ia) (ESplitItem_prods (S2 ! i))) ")
    apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
    apply(force)
   apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
   apply (metis drop_map)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(rule trans_der_notfinishingL_froml3_ext)
    apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
    apply(force)
   apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
   apply(force)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(force)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(rule trans_der_notfinishingL_froml3_ext)
   apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
   apply(assumption)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(assumption)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(assumption)
  apply(rename_tac ia X F1 F2 \<alpha> v1 v2 r1 r2 q c q2 ntL l1 l2 \<pi>3c \<alpha>3c \<pi>X vX d3d d1x d2x)(*strict*)
  apply(clarsimp)
  done

theorem equal_split_prefix: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=v@[teB b]@x1\<rparr>)
  \<Longrightarrow> cfgRM.derivation_initial G d2
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=v@[teB b]@x2\<rparr>)
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> EValidSplit G (S2@S2')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> length S2 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> v@[teB b] = Esplit_signature S2
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> x2 = Esplit_signature S2'
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> S2R=restrict G' G (S2@S2') (length (v@[teB b]))
  \<Longrightarrow> S1R = S2R"
  apply(subgoal_tac "ESplitItem_elem ((S1 @ S1') ! length v) = Some (teB b)")
   prefer 2
   apply(rule equal_split_prefix_hlp2)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "PValidSplit G' G S1R")
   prefer 2
   apply(rule equal_split_prefix_hlp3)
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
  apply(subgoal_tac "ESplitItem_elem ((S2 @ S2') ! length v) = Some (teB b)")
   prefer 2
   apply(rule_tac
      ?d1.0="d2"
      in equal_split_prefix_hlp2)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "PValidSplit G' G S2R")
   prefer 2
   apply(rule_tac
      ?S1.0="S2"
      and ?d1.0="d2"
      in equal_split_prefix_hlp3)
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
  apply(rule listEqI)
   apply(clarsimp)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "length (Esplit_signature S1) = length S1")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis length_Suc)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length (v@[teB b]) = length S1")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis length_Suc)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      and S1'="S1'"
      and S2'="S2'"
      and ?S1.0="S1"
      and ?S2.0="S2"
      in equal_split_prefix_hlp1)
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
           apply(rename_tac i)(*strict*)
           apply(force)
          apply(rename_tac i)(*strict*)
          defer
          defer
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
    apply(rule_tac
      t="length (v @ [teB b])"
      and s="length S1R"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(rule_tac
      t="S1R"
      and s="restrict G' G (S1 @ S1') (length (v @ [teB b]))"
      in ssubst)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
     apply(clarsimp)
     apply(rule_tac
      t="length S1"
      and s="Suc (length v)"
      in ssubst)
      apply(rename_tac i)(*strict*)
      apply (metis length_Suc)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "length (nat_seq 0 (length v)) =SSX" for SSX)
      apply(rename_tac i)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(case_tac "S1'")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rename_tac i a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(thin_tac "EValidSplit G (S2 @ S2')")
   apply(simp add: EValidSplit_def EValidSplit_final_def)
   apply(clarsimp)
   apply(subgoal_tac "last S1 = S1!length v")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply (metis last_nth3 length_Suc)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_ValidItem_def)
   apply(erule_tac
      x="S1!length v"
      in ballE)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply (metis last_in_set)
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplitItem_def)
   apply(clarsimp)
   apply(case_tac "ESplitItem_from (S1 ! length v)")
    apply(rename_tac i)(*strict*)
    apply(simp add: EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac i d)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac i d)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac i d)(*strict*)
    apply(clarsimp)
   apply(rename_tac i a)(*strict*)
   apply(rule_tac
      b="b"
      and S="S1!length v"
      and G="G"
      and G'="G'"
      in EValidSplit_DERIVED_terminal_produce_produces_to)
        apply(rename_tac i a)(*strict*)
        apply(force)
       apply(rename_tac i a)(*strict*)
       apply(force)
      apply(rename_tac i a)(*strict*)
      apply(force)
     apply(rename_tac i a)(*strict*)
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(case_tac "S2'")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rename_tac i a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(thin_tac "EValidSplit G (S1 @ S1')")
  apply(simp add: EValidSplit_def EValidSplit_final_def)
  apply(clarsimp)
  apply(subgoal_tac "last S2 = S2!length v")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis last_nth3 length_Suc)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S2!length v"
      in ballE)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis last_in_set)
  apply(rename_tac i)(*strict*)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S2 ! length v)")
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac i d)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    apply(rename_tac i d)(*strict*)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(rename_tac i d)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(rule_tac
      b="b"
      and S="S2!length v"
      and G="G"
      and G'="G'"
      in EValidSplit_DERIVED_terminal_produce_produces_to)
       apply(rename_tac i a)(*strict*)
       apply(force)
      apply(rename_tac i a)(*strict*)
      apply(force)
     apply(rename_tac i a)(*strict*)
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(force)
  done

hide_fact equal_split_prefix_hlp1
hide_fact equal_split_prefix_hlp1_updated
hide_fact equal_split_prefix_updated
hide_fact restrictX_length
  (* important equal_split_prefix *)

end

