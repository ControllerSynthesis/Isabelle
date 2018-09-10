section {*LR1\_Property\_Satisfaction\_\_restrict\_entire\_derivation\_tree*}
theory
  LR1_Property_Satisfaction__restrict_entire_derivation_tree

imports
  PRJ_12_04_06_06_07__ENTRY

begin

lemma fillOpt_hd_and_last_back_state: "
  fillOpt (hd (cropTol3l2 (a # w))) (last_back_state_if_l3_nonterminal [a]) = a"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: last_back_state_if_l3_nonterminal_def cropTol3l2_def cropTol3l2_single_def)
   apply(case_tac a)
    apply(rename_tac q b)(*strict*)
    apply(clarsimp)
    apply(simp add: fillOpt_def)
   apply(rename_tac q1 b q2)(*strict*)
   apply(clarsimp)
   apply(simp add: fillOpt_def fill_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: last_back_state_if_l3_nonterminal_def cropTol3l2_def cropTol3l2_single_def)
  apply(case_tac a)
   apply(rename_tac q b)(*strict*)
   apply(clarsimp)
   apply(simp add: fillOpt_def fill_def)
  apply(rename_tac q1 b q2)(*strict*)
  apply(clarsimp)
  apply(simp add: fillOpt_def fill_def)
  done

lemma ignore_parts_in_relation: "
  i3=t3
  \<Longrightarrow> n3=[]
  \<Longrightarrow> \<exists>x3. t3=x3@t2
  \<Longrightarrow> \<exists>x2. t2=x2@t1
  \<Longrightarrow> \<exists>x1. t1=x1
  \<Longrightarrow> n1=a1
  \<Longrightarrow> n2=a2
  \<Longrightarrow> n3=a3
  \<Longrightarrow> i1=b1@t1
  \<Longrightarrow> i2=b2@t2
  \<Longrightarrow> i3=b3@t3
  \<Longrightarrow> length b1 = length a1
  \<Longrightarrow> length b2 = length a2
  \<Longrightarrow> length b3 = length a3
  \<Longrightarrow> butn i3 (length t1) @ drop (length n1) i1 = butn i3 (length t2) @ drop (length n2) i2"
  apply(clarsimp)
  apply(rename_tac x3 x2)(*strict*)
  apply(simp add: butn_def)
  done

lemma enforceSuffixS_Min_Min: "
    i\<le>k
    \<Longrightarrow> k < length w
      \<Longrightarrow> Min (enforceSuffixS w i) \<le> Min (enforceSuffixS w k)"
  apply(rule Min_antimono)
    apply(simp add: enforceSuffixS_def)
    apply(clarsimp)
    apply(rename_tac ia)(*strict*)
    apply(rule_tac
      x="(k-i)+ia"
      in exI)
    apply(clarsimp)
   apply(simp add: enforceSuffixS_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(force)
  apply(rule enforceSuffixS_finite)
  done

lemma fillOptL_length: "
  length(fillOptL w X) = length w"
  apply(simp add: fillOptL_def)
  apply(case_tac X)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(simp add: fillL_def appL_def)
  done

lemma fillOptL_with_take: "
  fillOptL (take (Suc n) (cropTol3l2 [ac])) (last_back_state_if_l3_nonterminal [ac]) = [ac]"
  apply(simp add: fillOptL_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fillL_def appL_def)
  apply(case_tac ac)
   apply(rename_tac q b)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac q1 b q2)(*strict*)
  apply(simp add: fillOptL_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fillL_def appL_def)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def)
  apply(simp add: fillOptL_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fillL_def appL_def fill_def)
  done

lemma elim_map_to_trans_der_cfgLMMIy: "
  valid_cfg G
  \<Longrightarrow> length ws=length \<pi>s
  \<Longrightarrow> length ws=length xs
  \<Longrightarrow> elim_map G ws \<pi>s (map (\<lambda>x. []) xs)
  \<Longrightarrow> \<exists>d. cfgLMMIy G d (liftA ws) (foldl (@) [] \<pi>s) [] []"
  apply(induct "ws" arbitrary: xs \<pi>s rule: rev_induct)
   apply(rename_tac xs \<pi>s)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(simp add: cfgLMMIy_def)
   apply(rule conjI)
    apply(rule cfgLM_trans_der_der1)
     apply(force)
    apply(simp add: cfg_configurations_def)
   apply(simp add: cfgLMMIyX_def)
  apply(rename_tac x xs xsa \<pi>s)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<pi>s=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac x xs xsa \<pi>s)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x xs xsa \<pi>s)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs xsa \<pi>s)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs xsa \<pi>s)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs xsa w' a')(*strict*)
  apply(subgoal_tac "xsa=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac x xs xsa w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x xs xsa w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs xsa w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs xsa w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' a' w'a)(*strict*)
  apply(rename_tac A w \<pi>s \<pi> ze)
  apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
  apply(erule_tac
      x="ze"
      in meta_allE)
  apply(erule_tac
      x="\<pi>s"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
   apply(subgoal_tac "elim_map SSG (take SSi SSv) (take SSi SSrenPIs) (map (\<lambda>x. []) SSx)" for SSG SSv SSi SSrenPIs SSx)
    apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
    prefer 2
    apply(rule_tac
      i="length w"
      and v="(w@[A])"
      and w="ze@[a]" for a
      in elim_map_restrict)
       apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
       apply(force)
      apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
    apply(force)
   apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s \<pi> ze)(*strict*)
  apply(simp add: elim_map_def)
  apply(erule_tac
      x="length w"
      in allE)
  apply(clarsimp)
  apply(rename_tac A w \<pi>s \<pi> ze d da n e)(*strict*)
  apply(subgoal_tac "(\<pi>s @ [\<pi>]) ! length ze = \<pi>")
   apply(rename_tac A w \<pi>s \<pi> ze d da n e)(*strict*)
   prefer 2
   apply (metis nth_append_2_prime_prime nth_first)
  apply(rename_tac A w \<pi>s \<pi> ze d da n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
  apply(subgoal_tac "(w @ [A]) ! length ze = A")
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   prefer 2
   apply (metis nth_append_2_prime_prime nth_first)
  apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(map (\<lambda>x. []) ze @ [[]]) ! length ze = []")
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   prefer 2
   apply (simp add: length_map nth_append_2_prime_prime nth_first)
  apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G da \<lparr>cfg_conf=[teA A]\<rparr> (map the (get_labels da n)) \<lparr>cfg_conf=[]\<rparr>")
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      t="length (get_labels da n)"
      and s="n"
      in ssubst)
    apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
    apply (simp add: get_labels_length)
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   apply(rule conjI)
    apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
     apply(force)
    apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
    apply(force)
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="(map (\<lambda>x. []) ze @ [[]]) ! length ze"
      and s="[]"
      in ssubst)
    apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
    apply(force)
   apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s ze d da n e)(*strict*)
  apply(thin_tac "da n = Some (pair e \<lparr>cfg_conf = liftB ((map (\<lambda>x. []) ze @ [[]]) ! length ze)\<rparr>)")
  apply(thin_tac "(w @ [A]) ! length ze = A")
  apply(thin_tac "(map (\<lambda>x. []) ze @ [[]]) ! length ze = []")
  apply(thin_tac "(\<pi>s @ [map the (get_labels da n)]) ! length ze = map the (get_labels da n)")
  apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(clarsimp)
  apply(rename_tac A w \<pi>s ze d da n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac A w \<pi>s ze d da n)(*strict*)
   prefer 2
   apply(unfold cfgLMMIy_def)
   apply(rule_tac
      ?v1.0="[]"
      and ?\<pi>1.0="(foldl (@) [] \<pi>s)"
      and G="G"
      and ?w2.0="[teA A]"
      and ?d1.0="d"
      and ?d2.0="da"
      in cfgLM_trans_der_biextend)
     apply(rename_tac A w \<pi>s ze d da n)(*strict*)
     apply(force)
    apply(rename_tac A w \<pi>s ze d da n)(*strict*)
    apply(force)
   apply(rename_tac A w \<pi>s ze d da n)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s ze d da n)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_map d (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teA A]\<rparr>)) (derivation_map da (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v\<rparr>)) (length (foldl (@) [] \<pi>s))"
      in exI)
  apply(rename_tac A w \<pi>s ze d da n)(*strict*)
  apply(rule conjI)
   apply(rename_tac A w \<pi>s ze d da n)(*strict*)
   apply(clarsimp)
   apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac A w \<pi>s ze d da n)(*strict*)
  apply(simp add: cfgLMMIyX_def)
  apply(clarsimp)
  apply(thin_tac "foldl (@) [] \<pi>s = [] \<longrightarrow> get_labels da n \<noteq> []")
  apply(thin_tac "foldl (@) [] \<pi>s \<noteq> [] \<longrightarrow> \<not> applicable G (foldl (@) [] \<pi>s) (butlast (liftA w))")
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac A w \<pi>s ze d da n db c)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "\<exists>e c. db (length (foldl (@) [] \<pi>s)) = Some (pair e c)")
   apply(rename_tac A w \<pi>s ze d da n db c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac A w \<pi>s ze d da n db c e ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (foldl (@) [] \<pi>s @ map the (get_labels da n))"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac A w \<pi>s ze d da n db c e ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac A w \<pi>s ze d da n db c e ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac A w \<pi>s ze d da n db c e ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac A w \<pi>s ze d da n db c)(*strict*)
  apply(clarsimp)
  apply(rename_tac A w \<pi>s ze d da n db c e ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac A w \<pi>s ze d da n db c e ca cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac A wa \<pi>s ze d da n db c e ca w)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftA wa\<rparr> (foldl (@) [] \<pi>s) \<lparr>cfg_conf=w\<rparr>")
   apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
   apply(rule_tac
      m="length(get_labels da n)"
      and v="(get_labels da n)"
      in get_labels_drop_tail)
    apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
     apply(force)
    apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
    apply(rule_tac
      t="n"
      and s="length(get_labels da n)"
      in ssubst)
     apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac A wa \<pi>s ze d da n db c e w ea eb ec ed)(*strict*)
   apply(force)
  apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
   prefer 2
   apply(rule_tac
      ?w2.0="[]"
      and ?d1.0="db"
      and ?d2.0="d"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
     apply(force)
    apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
   apply(force)
  apply(rename_tac A wa \<pi>s ze d da n db c e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa \<pi>s ze d da n db c e)(*strict*)
  apply(case_tac "get_labels da n=[]")
   apply(rename_tac A wa \<pi>s ze d da n db c e)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac A wa \<pi>s ze d da n db c e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. db (length (foldl (@) [] \<pi>s)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac A wa \<pi>s ze d da n db c e)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (foldl (@) [] \<pi>s @ map the (get_labels da n))"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee)(*strict*)
     apply(force)
    apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee)(*strict*)
    apply(force)
   apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee)(*strict*)
   apply(simp (no_asm))
   apply(case_tac "get_labels da n")
    apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee)(*strict*)
    apply(force)
   apply(rename_tac A wa \<pi>s ze d da n db c e ea eb ec ed ee a list)(*strict*)
   apply(force)
  apply(rename_tac A wa \<pi>s ze d da n db c e)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa \<pi>s ze d da n db c e e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  done

lemma concat_cfgLM_trans_der_cfgLMMIy: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[A1]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1@w3\<rparr>
  \<Longrightarrow> cfgLMMIy G d2 (w3@w2) \<pi>2 (liftB \<alpha>2) []
  \<Longrightarrow> \<pi>2\<noteq>[]
  \<Longrightarrow> w3@w2 \<noteq> []
  \<Longrightarrow> \<lparr>cfg_conf = w2\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> \<exists>d. cfgLMMIy G d ([A1]@w2) (\<pi>1@\<pi>2) (liftB \<alpha>1@liftB \<alpha>2) []"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="w2"
      and ?d1.0="d1"
      in cfgLM_trans_der_context)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?v1.0="\<alpha>1"
      and ?v4.0="[]"
      and G="G"
      and ?d1.0="derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = liftB [] @ cfg_conf x @ w2\<rparr>)"
      and ?d2.0="d2"
      in cfgLM_trans_der_concat_extend)
     apply(force)
    prefer 2
    apply(simp add: cfgLMMIy_def)
    apply(clarsimp)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      x="derivation_append (derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ w2\<rparr>)) (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>1 @ cfg_conf v\<rparr>)) (length \<pi>1)"
      in exI)
  apply(simp add: cfgLMMIy_def)
  apply(simp add: cfgLMMIyX_def)
  apply(clarsimp)
  apply(subgoal_tac "w2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   prefer 2
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(subgoal_tac "butlast (w3 @ w' @ [a']) = SSX" for SSX)
    apply(rename_tac w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(subgoal_tac "butlast ([A1] @ w' @ [a']) = SSX" for SSX)
    apply(rename_tac w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
   apply(rule_tac
      ?w2.0="liftB \<alpha>1@w3"
      and G="G"
      and ?w1.0="[A1]"
      and ?w3.0="w'"
      in applicable_contra2)
      apply(rename_tac w' a')(*strict*)
      apply(force)
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(case_tac "applicable G \<pi>2 ((liftB \<alpha>1 @ w3) @ w')")
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(subgoal_tac "applicable G \<pi>2 (w3 @ w')")
     apply(rename_tac w' a')(*strict*)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(rule applicable_drop_liftB)
     apply(rename_tac w' a')(*strict*)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "w3=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(force)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "\<pi>1@\<pi>2=[]")
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule applicable_with_empty_source)
  apply(force)
  done

definition restrict_toberemoved :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list list"
  where
    "restrict_toberemoved S \<equiv>
  enforceSuffix (map ESplitItem_ignore S)"

definition restrict_toberemovedX :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list list"
  where
    "restrict_toberemovedX S \<equiv>
  restrict_toberemoved S @ [tl (ESplitItem_to (last S) @ ESplitItem_ignore (last S))]"

definition new_post_sig :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list"
  where
    "new_post_sig S i \<equiv>
   drop_and_crop
    (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i))
    (length ((restrict_toberemovedX S) ! (Suc i)))"

definition restrict_newignore :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list"
  where
    "restrict_newignore S i \<equiv>
  drop (length (ESplitItem_to (S ! i))) (new_post_sig S i)"

definition restrict_newprodsXX :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> nat
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label list
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements option
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "restrict_newprodsXX G i prods_j elem_j newto_j \<equiv>
  strict_prefix (derives G (drop i prods_j)) (option_to_list (elem_j) @ liftA newto_j)"

definition restrict_newprodsX :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label list
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements option
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> (('q, 't, 's) epda_step_label, (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label) DT_two_elements list"
  where
    "restrict_newprodsX G' G prods_j elem_j newto_j \<equiv>
  if prods_j = []
  then []
  else 
    (map 
      (\<lambda>i. 
        if restrict_newprodsXX G i prods_j elem_j newto_j
        then teB (prods_j ! i)
        else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (prods_j ! i))) 
      (nat_seq 0 (length prods_j - Suc 0)))"

definition restrict_newto :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list"
  where
    "restrict_newto S i \<equiv>
  take (length (ESplitItem_to (S ! i))) (new_post_sig S i)"

definition restrict_newprods :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> (('q, 't, 's) epda_step_label, (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label) DT_two_elements list"
  where
    "restrict_newprods G' G S j \<equiv>
  if restrict_newignore S j = []
  then restrict_newprodsX G' G (ESplitItem_prods (S ! j)) (ESplitItem_elem (S ! j)) (restrict_newto S j)
  else liftB (ESplitItem_prods (S ! j))"

definition restrict_newelem :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements"
  where
    "restrict_newelem S i \<equiv>
  the (ESplitItem_elem (S ! i))"

definition restrict_map :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> ('q, 's, 't) PSplit"
  where
    "restrict_map G' G S \<equiv>
  map 
    (\<lambda>i. 
      \<lparr>PSplitItem_elim = ESplitItem_elim (S ! i),
      PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from (S ! i)) # restrict_newignore S i)),
      PSplitItem_ignore = restrict_newignore S i,
      PSplitItem_elim_prods = ESplitItem_elim_prods (S ! i),
      PSplitItem_prods = restrict_newprods G' G S i,
      PSplitItem_elem = restrict_newelem S i,
      PSplitItem_to = restrict_newto S i\<rparr>) 
    (nat_seq 0 (length S - Suc 0))"

definition restrict_len :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's, 't) ESplit"
  where
    "restrict_len S n \<equiv>
  take n S"

definition restrict :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg
  \<Rightarrow> ('q, 's, 't) ESplit
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's, 't) PSplit"
  where
    "restrict G' G S n \<equiv>
  restrict_map G' G (restrict_len S n)"

lemma equal_split_prefix_hlp2: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf = v @ [teB b] @ x1\<rparr>)
  \<Longrightarrow> EValidSplit G (S1 @ S1')
  \<Longrightarrow> length S1 = length (v @ [teB b])
  \<Longrightarrow> v @ [teB b] = Esplit_signature S1
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> S1R = restrict G' G (S1 @ S1') (length (v @ [teB b]))
  \<Longrightarrow> ESplitItem_elem ((S1 @ S1') ! length v) = Some (teB b)"
  apply(simp add: Esplit_signature_def)
  apply(clarsimp)
  apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="(w' @ a' # S1') ! length v"
      and s="a'"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply (metis Suc_length length_append map_map nat.inject nth_append_length)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac a')
  apply(rename_tac w' a' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_to)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_to)(*strict*)
  apply(case_tac "ESplitItem_elema")
   apply(rename_tac w' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_to)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_to)(*strict*)
   apply(simp add: option_to_list_def)
   apply (metis EValidSplit_Esplit_signature_length Esplit_signature_def List.map.compositionality distrib_add_apppend_with_map list.simps(2) n_not_Suc_n)
  apply(rename_tac w' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_to a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' ESplitItem_elim ESplitItem_from ESplitItem_ignore ESplitItem_elim_prods ESplitItem_prods ESplitItem_to a)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma length_of_restrict: "
      0<n
    \<Longrightarrow> n\<le>length S
    \<Longrightarrow> length(restrict G' G S n) = n"
  apply(simp add: restrict_def)
  apply(simp add: restrict_map_def restrict_len_def)
  apply(rule_tac
      t="min (length S) n"
      and s="n"
      in ssubst)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (n-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  done

lemma length_restrict_toberemoved: "
  S\<noteq>[]
    \<Longrightarrow> length (restrict_toberemoved S) = length S"
  apply(simp add: restrict_toberemoved_def enforceSuffix_def)
  apply(subgoal_tac "length (nat_seq 0 (length S-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  done

lemma restrict_toberemoved_smaller_than_ignore: "
  i\<le>k
    \<Longrightarrow> k < length S
    \<Longrightarrow> length (restrict_toberemoved S ! i) \<le> length (ESplitItem_ignore (S ! k))"
  apply(subgoal_tac "nat_seq 0 (length S- Suc 0) ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(simp add: restrict_toberemoved_def)
  apply(simp add: enforceSuffix_def)
  apply(subgoal_tac "length (nat_seq 0 (length S- Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: restrict_toberemoved_def enforceSuffix_def takeB_def)
  apply(subgoal_tac "Min (enforceSuffixS (map ESplitItem_ignore S) i) \<le> length (ESplitItem_ignore (S ! i))")
   prefer 2
   apply(rule enforceSuffixS_smaller)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule enforceSuffixS_smaller)
   apply(force)
  apply(force)
  done

lemma restrict_toberemoved_last_is_ignore: "
  S\<noteq>[]
  \<Longrightarrow> last (restrict_toberemoved S) = ESplitItem_ignore (last S)"
  apply(simp add: restrict_toberemoved_def)
  apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: enforceSuffix_def)
  apply(subgoal_tac "\<exists>w. nat_seq 0 (length w') = w @ [length w']")
   apply(rename_tac w' a')(*strict*)
   prefer 2
   apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' a')(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac a')(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply (metis natUptTo_n_n)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac a' w'a a'a)(*strict*)
   apply(rule_tac
      x="nat_seq 0 ((length w'a))"
      in exI)
   apply (metis le0 nat_seq_drop_last_simp)
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a' w)(*strict*)
  apply(subgoal_tac "(map ESplitItem_ignore w' @ [ESplitItem_ignore a']) ! length w' =ESplitItem_ignore a'")
   apply(rename_tac w' a' w)(*strict*)
   prefer 2
   apply (metis length_map nth_append_2_prime_prime nth_first)
  apply(rename_tac w' a' w)(*strict*)
  apply(clarsimp)
  apply(simp add: takeB_def)
  apply(case_tac "length (ESplitItem_ignore a') - Min (enforceSuffixS (map ESplitItem_ignore w' @ [ESplitItem_ignore a']) (length w'))")
   apply(rename_tac w' a' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' w nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (ESplitItem_ignore a') = Suc nat+Min (enforceSuffixS (map ESplitItem_ignore w' @ [ESplitItem_ignore a']) (length w'))")
   apply(rename_tac w' a' w nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w' a' w nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_ignore a'")
   apply(rename_tac w' a' w nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' w nat a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "enforceSuffixS (map ESplitItem_ignore w' @ [a # list]) (length w') = enforceSuffixS ([a # list]) 0")
   apply(rename_tac w' a' w nat a list)(*strict*)
   prefer 2
   apply(rule enforceSuffixS_shift)
   apply(force)
  apply(rename_tac w' a' w nat a list)(*strict*)
  apply(clarsimp)
  apply(thin_tac "enforceSuffixS (map ESplitItem_ignore w' @ [a # list]) (length w') = enforceSuffixS [a # list] 0")
  apply(rename_tac w' a' w nat a list)(*strict*)
  apply(subgoal_tac "Min (enforceSuffixS [a # list] 0) = length (a#list)")
   apply(rename_tac w' a' w nat a list)(*strict*)
   prefer 2
   apply(rule Min_enforceSuffixS_single)
  apply(rename_tac w' a' w nat a list)(*strict*)
  apply(subgoal_tac "length list=nat + length(a#list)")
   apply(rename_tac w' a' w nat a list)(*strict*)
   prefer 2
   apply(rule_tac
      t="length (a#list)"
      and s="Min (enforceSuffixS [a # list] 0)"
      in subst)
    apply(rename_tac w' a' w nat a list)(*strict*)
    apply(force)
   apply(rename_tac w' a' w nat a list)(*strict*)
   apply(force)
  apply(rename_tac w' a' w nat a list)(*strict*)
  apply(thin_tac "length list = nat + Min (enforceSuffixS [a # list] 0)")
  apply(thin_tac "Min (enforceSuffixS [a # list] 0) = length (a # list)")
  apply(thin_tac "drop nat list \<noteq> a # list")
  apply(thin_tac "nat_seq 0 (length w') = w @ [length w']")
  apply(thin_tac "(map ESplitItem_ignore w' @ [a # list]) ! length w' = a # list")
  apply(thin_tac "ESplitItem_ignore a' = a # list")
  apply(clarsimp)
  done

lemma restrict_toberemoved_preserves_length: "
    w \<noteq> []
  \<Longrightarrow> length (restrict_toberemoved w) = length w"
  apply(simp add: restrict_toberemoved_def enforceSuffix_def)
  apply(subgoal_tac "length (nat_seq 0 (length w-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  done

lemma restrict_toberemovedX_equals_restrict_toberemoved: "
  n<length S
  \<Longrightarrow> restrict_toberemovedX S ! n = restrict_toberemoved S ! n"
  apply(simp add: restrict_toberemovedX_def)
  apply(subgoal_tac "length(restrict_toberemoved S) = SSX" for SSX)
   prefer 2
   apply(rule length_restrict_toberemoved)
   apply(force)
  apply(rule_tac
      xs="S"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(rule nth_append_1)
  apply(force)
  done

lemma restrict_toberemoved_direct_computation: "
  S\<noteq>[]
  \<Longrightarrow> Suc i<length S
  \<Longrightarrow> w1@ESplitItem_ignore (S ! i)=w2@ESplitItem_ignore (S ! Suc i)
  \<Longrightarrow> restrict_toberemoved S ! i = takeB (length(restrict_toberemoved S ! (Suc i))) (ESplitItem_ignore (S ! i))"
  apply(simp add: restrict_toberemoved_def)
  apply(simp add: enforceSuffix_def)
  apply(subgoal_tac "nat_seq 0 (length S - Suc 0) ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length S-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "nat_seq 0 (length S - Suc 0) ! (Suc i) = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "enforceSuffixS (map ESplitItem_ignore S) i= enforceSuffixS (map ESplitItem_ignore S) (Suc i) \<union>{length(ESplitItem_ignore (S ! i))}")
   apply(clarsimp)
   apply(rule_tac
      t="length (takeB (Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i))) (ESplitItem_ignore (S ! Suc i)))"
      and s="Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i))"
      in ssubst)
    apply(simp add: takeB_def)
    apply(subgoal_tac "Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i)) \<le> length (ESplitItem_ignore (S ! Suc i))")
     apply(force)
    apply(rule Lattices_Big.linorder_class.Min_le)
     apply(rule enforceSuffixS_finite)
    apply(simp add: enforceSuffixS_def)
    apply(rule_tac
      x="0"
      in exI)
    apply(clarsimp)
   apply(case_tac "Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i)) \<le> length(ESplitItem_ignore (S ! i))")
    apply(subgoal_tac "Min ({length (ESplitItem_ignore (S ! i))} \<union> enforceSuffixS (map ESplitItem_ignore S) (Suc i)) = Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i))")
     apply(clarsimp)
    apply(rule Min_insert)
      apply(rule enforceSuffixS_finite)
     apply(simp add: enforceSuffixS_def)
     apply(rule_tac
      x="0"
      in exI)
     apply(clarsimp)
    apply(force)
   apply(case_tac "length(ESplitItem_ignore (S ! i)) < Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i))")
    prefer 2
    apply(force)
   apply(thin_tac "\<not> Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i)) \<le> length (ESplitItem_ignore (S ! i))")
   apply(subgoal_tac "Min ({length (ESplitItem_ignore (S ! i))} \<union> enforceSuffixS (map ESplitItem_ignore S) (Suc i)) = length (ESplitItem_ignore (S ! i))")
    prefer 2
    apply(rule order_antisym)
     apply(rule Lattices_Big.linorder_class.Min_le)
      apply(clarsimp)
      apply(rule enforceSuffixS_finite)
     apply(force)
    apply(rule Min_ge_absorb)
      apply(rule enforceSuffixS_finite)
     apply(simp add: enforceSuffixS_def)
     apply(rule_tac
      x="0"
      in exI)
     apply(clarsimp)
    apply(force)
   apply(clarsimp)
   apply(simp add: takeB_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: enforceSuffixS_def)
   apply(clarsimp)
   apply(rename_tac ia)(*strict*)
   apply(case_tac ia)
    apply(rename_tac ia)(*strict*)
    apply(clarsimp)
   apply(rename_tac ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: enforceSuffixS_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(simp add: enforceSuffixS_def)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(rule_tac
      x="Suc ia"
      in exI)
  apply(clarsimp)
  done

lemma restrict_PValidSplit_interline: "
  F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> Suc n \<le> length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> ESplitItem_to (S!n) \<noteq> []
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))"
  apply(simp add: PValidSplit_interline_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "Suc i < length S \<longrightarrow> EValidSplit_interlineX (S ! i) (S ! Suc i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_interline_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min (length S) (Suc n) = Suc n")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq 0 n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq 0 n ! (Suc i) = SSn+SSi" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! Suc i) @ option_to_list (ESplitItem_from (S ! Suc i)) @ ESplitItem_ignore (S ! Suc i))")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_ValidItem_def)
   apply(erule_tac
      x="S ! Suc i"
      in ballE)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "((ESplitItem_to (S ! i) = [] \<longrightarrow> filterA (option_to_list (ESplitItem_elem (S ! i))) = [] \<longrightarrow> ESplitItem_ignore (S ! i) \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (option_to_list (ESplitItem_elem (S ! i))) @ ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)))")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_ValidItem_def)
   apply(erule_tac
      x="S ! i"
      in ballE)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_def restrict_len_def restrict_map_def)
  apply(simp add: PValidSplit_interlineX_def EValidSplit_interlineX_def)
  apply(case_tac "ESplitItem_from (S!Suc i)")
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i w' a')(*strict*)
   apply(subgoal_tac "(w' @ [a']) ! Suc i = w'!Suc i")
    apply(rename_tac i w' a')(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(w' @ [a']) ! i = w'! i")
    apply(rename_tac i w' a')(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i w' a')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="w'!Suc i"
      in ballE)
    apply(rename_tac i w' a')(*strict*)
    apply(force)
   apply(rename_tac i w' a')(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(erule impE)
   apply(rename_tac i a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac i a q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q b)(*strict*)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "ESplitItem_ignore (S ! Suc i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i q b)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i q b)(*strict*)
   apply(erule disjE)
    apply(rename_tac i q b)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac i q b w' a')(*strict*)
    apply(rule_tac
      w'="w'"
      and a="a'"
      and w="ESplitItem_elim (S ! Suc i)"
      and q="q"
      and A="b"
      in proper_l3_l2_seq_nol2)
    apply(force)
   apply(rename_tac i q b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="hd (cropTol3l2 (cons_l2 q b # restrict_newignore (take (Suc n) S) (Suc i)))"
      and s="cons_l2 q b"
      in ssubst)
    apply(rename_tac i q b)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def)
   apply(rename_tac i q b)(*strict*)
   apply(rule_tac
      t="restrict_newignore (take (Suc n) S) (Suc i)"
      and s="[]"
      in ssubst)
    apply(rename_tac i q b)(*strict*)
    apply(simp add: restrict_toberemovedX_def restrict_newignore_def new_post_sig_def)
    apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! Suc i)) (length ((restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc (Suc i))))"
      in ssubst)
     apply(rename_tac i q b)(*strict*)
     apply(rule drop_and_crop_length)
    apply(rename_tac i q b)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q b)(*strict*)
   apply(simp add: restrict_newignore_def restrict_newto_def restrict_toberemovedX_def new_post_sig_def)
   apply(rule_tac
      t="length ((restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc i)"
      and s="0"
      in ssubst)
    apply(rename_tac i q b)(*strict*)
    prefer 2
    apply(rule_tac
      t="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ [cons_l2 q b]"
      in ssubst)
     apply(rename_tac i q b)(*strict*)
     apply(force)
    apply(rename_tac i q b)(*strict*)
    apply(simp (no_asm) add: drop_and_crop_def cropTol3l2_def butn_def cropTol3l2_single_def)
   apply(rename_tac i q b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc i"
      in ssubst)
    apply(rename_tac i q b)(*strict*)
    apply(rule nth_append_1)
    apply(rule_tac
      t="length(restrict_toberemoved (take (Suc n) S))"
      in ssubst)
     apply(rename_tac i q b)(*strict*)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(rename_tac i q b)(*strict*)
    apply(force)
   apply(rename_tac i q b)(*strict*)
   apply(subgoal_tac "length (restrict_toberemoved (take (Suc n) S) ! Suc i)=0")
    apply(rename_tac i q b)(*strict*)
    apply(force)
   apply(rename_tac i q b)(*strict*)
   apply(subgoal_tac "length (restrict_toberemoved (take (Suc n) S) ! Suc i) \<le> length (ESplitItem_ignore (S ! Suc i))")
    apply(rename_tac i q b)(*strict*)
    prefer 2
    apply(rule_tac
      t="S!Suc i"
      and s="take (Suc n) S!Suc i"
      in ssubst)
     apply(rename_tac i q b)(*strict*)
     apply(force)
    apply(rename_tac i q b)(*strict*)
    apply(rule restrict_toberemoved_smaller_than_ignore)
     apply(rename_tac i q b)(*strict*)
     apply(force)
    apply(rename_tac i q b)(*strict*)
    apply(force)
   apply(rename_tac i q b)(*strict*)
   apply(force)
  apply(rename_tac i a q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q1 b q2)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "ESplitItem_ignore (S ! Suc i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac i q1 b q2)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac i q1 b q2)(*strict*)
  apply(erule disjE)
   apply(rename_tac i q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      w="ESplitItem_elim (S ! Suc i)"
      and q="q1"
      and A="b"
      and q'="q2"
      in proper_l3_l2_seq_nol3)
   apply(force)
  apply(rename_tac i q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(thin_tac "proper_l3_l2_seq (filterA (case ESplitItem_elem (S ! i) of None \<Rightarrow> [] | Some A \<Rightarrow> [A]) @ ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i))")
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(case_tac "Suc i=n")
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newto_def restrict_newignore_def new_post_sig_def restrict_toberemovedX_def)
   apply(rule_tac
      t="((restrict_toberemoved (take (Suc (Suc i)) S) @ [tl (ESplitItem_to (last (take (Suc (Suc i)) S)) @ ESplitItem_ignore (last (take (Suc (Suc i)) S)))]) ! Suc (Suc i))"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule nth_append_beyond)
    apply(rule_tac
      t="length(restrict_toberemoved (take (Suc (Suc i)) S))"
      in ssubst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(rule_tac
      t="last (take (Suc (Suc i)) S)"
      and s="S!(Suc i)"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule last_take_nth)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(rule_tac
      t="(restrict_toberemoved (take (Suc (Suc i)) S) @ [tl (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i))]) ! Suc i"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule nth_append_1)
    apply(rule_tac
      t="length(restrict_toberemoved (take (Suc (Suc i)) S))"
      in ssubst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(rule_tac
      t="drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (tl (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i)))))"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(rule_tac
      t="drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemoved (take (Suc (Suc i)) S) ! Suc i)))"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac " restrict_toberemoved (take (Suc (Suc i)) S) ! (Suc i) = ESplitItem_ignore (S ! (Suc i))")
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last (take (Suc (Suc i)) S))" for SSS)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     prefer 2
     apply(rule restrict_toberemoved_last_is_ignore)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(subgoal_tac "length(restrict_toberemoved (take (Suc (Suc i)) S)) = length(take (Suc (Suc i)) S)")
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     prefer 2
     apply(rule restrict_toberemoved_preserves_length)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule_tac
      t="restrict_toberemoved (take (Suc (Suc i)) S) ! (Suc i)"
      and s="last (restrict_toberemoved (take (Suc (Suc i)) S))"
      in ssubst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(rule last_nth_prime)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule_tac
      t="(S ! (Suc i))"
      and s="(last (take (Suc (Suc i)) S))"
      in subst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(rule last_take_nth)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_final_def)
   apply(clarsimp)
   apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(subgoal_tac "(w'a @ [a'a]) ! Suc i = w'a!Suc i")
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(w'a @ [a'a]) ! i = w'a! i")
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_elim (w'a ! Suc i) @ cons_l3 q1 b q2 # w' @ [a'] = ESplitItem_to (w'a ! i) @ ESplitItem_ignore (w'a! i)")
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    prefer 2
    apply(rule_tac
      t="ESplitItem_to (w'a ! i) @ ESplitItem_ignore (w'a ! i)"
      and s="ESplitItem_to ((w'a @ [a'a]) ! i) @ ESplitItem_ignore ((w'a @ [a'a]) ! i)"
      in ssubst)
     apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
     apply(rule_tac
      t="(w'a @ [a'a]) ! i"
      and s="w'a!i"
      in ssubst)
      apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
     apply(force)
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(subgoal_tac "drop (length (ESplitItem_to (w'a ! Suc i))) (drop_and_crop (ESplitItem_to (w'a ! Suc i) @ w' @ [a']) (Suc (length w'))) = []")
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    prefer 2
    apply(simp add: drop_and_crop_def butn_def)
    apply(rule cropTol3l2_makes_shorter)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(clarsimp)
   apply(thin_tac "length (drop_and_crop (ESplitItem_to (w'a ! Suc i) @ w' @ [a']) (Suc (length w'))) \<le> length (ESplitItem_to (w'a ! Suc i))")
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(case_tac "ESplitItem_to (w'a ! (Suc i))")
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "hd (cropTol3l2 (cons_l3 q1 b q2 # drop_and_crop (w' @ [a']) (Suc (length list + length w')))) = cons_l2 q1 b")
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    prefer 2
    apply(simp (no_asm) add: drop_and_crop_def butn_def cropTol3l2_def cropTol3l2_single_def)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_elim (w'a ! Suc i) @ cons_l2 q1 b # drop_and_crop (w' @ [a']) (Suc (length list + length w')) = drop_and_crop (ESplitItem_to (w'a ! i) @ ESplitItem_ignore (w'a ! i)) (Suc (length w'))")
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(thin_tac "ESplitItem_elim (w'a ! Suc i) @ cons_l2 q1 b # drop_and_crop (w' @ [a']) (Suc (length list + length w')) \<noteq> drop_and_crop (ESplitItem_to (w'a ! i) @ ESplitItem_ignore (w'a ! i)) (Suc (length w'))")
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(rule_tac
      t="ESplitItem_to (w'a ! i) @ ESplitItem_ignore (w'a ! i)"
      and s="ESplitItem_elim (w'a ! Suc i) @ cons_l3 q1 b q2 # w' @ [a']"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(simp (no_asm) add: drop_and_crop_def butn_def cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(subgoal_tac "Suc i<n")
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "restrict_newignore (take (Suc n) S) (Suc i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newignore_def restrict_newto_def new_post_sig_def)
   apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = SSx" for SSx)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(thin_tac "length (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = Suc (length (ESplitItem_to (S ! Suc i)) + length w') - length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i))")
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(subgoal_tac "Suc (length (ESplitItem_to (S ! Suc i)) + length w') \<le> length (ESplitItem_to (S ! Suc i))+length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i))")
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(thin_tac "Suc (length (ESplitItem_to (S ! Suc i)) + length w') - length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)) \<le> length (ESplitItem_to (S ! Suc i))")
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "Suc (Suc i) < length S \<longrightarrow> EValidSplit_interlineX (S ! (Suc i)) (S ! Suc (Suc i))")
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(simp add: EValidSplit_interline_def)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(erule impE)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(simp add: EValidSplit_interlineX_def)
   apply(rule_tac
      t="restrict_toberemovedX (take (Suc n) S) ! Suc i"
      and s="restrict_toberemoved (take (Suc n) S) ! Suc i"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(subgoal_tac "Suc (length w') \<le> length (restrict_toberemoved (take (Suc n) S) ! Suc (Suc i))")
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(rule_tac
      s="restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)"
      and t="restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)"
      in subst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(thin_tac "Suc (length w') \<le> length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i))")
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(subgoal_tac "restrict_toberemoved (take (Suc n) S) ! (Suc i) = takeB (length(restrict_toberemoved (take (Suc n) S) ! (Suc (Suc i)))) (ESplitItem_ignore (S ! (Suc i)))")
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    prefer 2
    apply(rule_tac
      t="S!(Suc i)"
      and s="take(Suc n)S!(Suc i)"
      in ssubst)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc i)) @ option_to_list (ESplitItem_from (S ! Suc (Suc i)))"
      in restrict_toberemoved_direct_computation)
      apply(rename_tac i q1 b q2 w' a')(*strict*)
      apply(force)
     apply(rename_tac i q1 b q2 w' a')(*strict*)
     apply(force)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(simp add: takeB_def)
   apply(rule_tac
      t="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w' @ [a']"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a')(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a')(*strict*)
   apply(simp (no_asm) add: drop_and_crop_def butn_def)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac i q1 b q2 w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(rule_tac
      t="hd (cropTol3l2 (cons_l3 q1 b q2 # w'a @ [a'a]))"
      and s="cons_l3 q1 b q2"
      in ssubst)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(simp add: restrict_newignore_def restrict_newto_def new_post_sig_def)
  apply(rule_tac
      t="restrict_toberemovedX (take (Suc n) S) ! Suc i"
      and s="restrict_toberemoved (take (Suc n) S) ! Suc i"
      in ssubst)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(subgoal_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)))) = w'a @ [a'a]")
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   prefer 2
   apply(rule_tac
      s="restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)"
      and t="restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)"
      in subst)
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(thin_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = w'a @ [a'a]")
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(subgoal_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)))) = SSX" for SSX)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   prefer 2
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ w' @ [a']) (length (restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)))) = w'a @ [a'a]")
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(subgoal_tac "length (drop_and_crop (w' @ [a']) (length (restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)))) = SSx" for SSx)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w' @ [a']"
      in ssubst)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(subgoal_tac "Suc (Suc i) < length S \<longrightarrow> EValidSplit_interlineX (S ! (Suc i)) (S ! Suc (Suc i))")
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_interline_def)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(erule impE)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "restrict_toberemoved (take (Suc n) S) ! (Suc i) = takeB (length(restrict_toberemoved (take (Suc n) S) ! (Suc (Suc i)))) (ESplitItem_ignore (S ! (Suc i)))")
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   prefer 2
   apply(rule_tac
      t="S!(Suc i)"
      and s="take(Suc n)S!(Suc i)"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc i)) @ option_to_list (ESplitItem_from (S ! Suc (Suc i)))"
      in restrict_toberemoved_direct_computation)
     apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
     apply(force)
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
  apply(simp add: takeB_def)
  apply(case_tac "restrict_toberemoved (take (Suc n) S) ! Suc (Suc i)")
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(clarsimp)
   apply(simp add: drop_and_crop_def)
   apply(simp add: cropTol3l2_def butn_def)
   apply(rule conjI)
    apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' w'a a'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q1 b q2 a' w'a)(*strict*)
   apply(rule_tac
      t="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w'a @ [a']"
      in ssubst)
    apply(rename_tac i q1 b q2 a' w'a)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 a' w'a)(*strict*)
   apply(rule_tac
      t="last (ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w'a @ [a'])"
      and s="a'"
      in ssubst)
    apply(rename_tac i q1 b q2 a' w'a)(*strict*)
    apply (metis append_is_Nil_conv last_ConsR last_appendR last_snoc list.simps(2) not_Cons_self)
   apply(rename_tac i q1 b q2 a' w'a)(*strict*)
   apply(rule_tac
      t="butlast (ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w'a @ [a'])"
      in ssubst)
    apply(rename_tac i q1 b q2 a' w'a)(*strict*)
    apply(rule_tac
      w="ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w'a"
      in butlast_direct)
    apply(force)
   apply(rename_tac i q1 b q2 a' w'a)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ cons_l3 q1 b q2 # w' @ [a']"
      in ssubst)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(simp (no_asm) add: drop_and_crop_def)
  apply(simp (no_asm) add: cropTol3l2_def butn_def)
  apply(rule conjI)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Suc (length w') - length list"
      and s="Suc(Suc (length w'a))"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="length w' - length list"
      and s="Suc (length w'a)"
      in ssubst)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(force)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(simp add: drop_and_crop_def)
   apply(simp add: cropTol3l2_def butn_def)
   apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   apply(subgoal_tac "take (length w' - length list) w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   apply(erule disjE)
    apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' a list w'a a'a)(*strict*)
   apply(rule sym)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length list<Suc(length w')")
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(clarsimp)
  apply(simp add: drop_and_crop_def)
  apply(simp add: cropTol3l2_def butn_def)
  apply(case_tac "length w' \<le> length list \<or> w' = []")
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' w'a a'a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
  apply(subgoal_tac "length list < length w'")
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="last (take (length w' - length list) w')"
      and s="last (take (Suc (length w') - length list) (cons_l3 q1 b q2 # w' @ [a']))"
      in ssubst)
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   apply(case_tac "length w' - length list")
    apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length w'=Suc nat+length list")
    apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "length w' - length list")
   apply(rename_tac i q1 b q2 w' a' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length w'=Suc nat+length list")
   apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "take (Suc nat) w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
  apply(erule disjE)
   apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' a list nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i q1 b q2 w' a' a list nat w'a a'a)(*strict*)
  apply(rule sym)
  apply(rule butlast_direct)
  apply(force)
  done

lemma restrict_PValidSplit_notEmpty: "
  Suc n \<le> length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> restrict G' G S (Suc n) \<noteq> []"
  apply(simp add: restrict_def)
  apply(simp add: restrict_map_def restrict_def restrict_len_def)
  apply(rule_tac
      t="min (length S) (Suc n)"
      and s="Suc n"
      in ssubst)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (Suc n-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(force)
  done

lemma restrict_PValidSplit_initial: "
  F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> PValidSplit_initial G (restrict G' G S (Suc n))"
  apply(simp add: PValidSplit_initial_def restrict_def)
  apply(simp add: restrict_map_def restrict_def restrict_len_def)
  apply(rule_tac
      t="min (length S) (Suc n)"
      and s="Suc n"
      in ssubst)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (Suc n-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. nat_seq 0 n = [0] @ w ")
   prefer 2
   apply(case_tac n)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply (metis natUptTo_n_n)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="nat_seq (Suc 0) (Suc nat)"
      in exI)
   apply (metis less_eq_nat.simps(1) nat_seq_pullout)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: EValidSplit_initial_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(case_tac S)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac w a list)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def)
    apply(clarsimp)
    apply(simp add: F2LR1inputx_def cfg_sub_def F_SDPDA_TO_CFG_STD_def)
   apply(rename_tac w a list)(*strict*)
   apply(simp add: restrict_newignore_def)
   apply(simp add: new_post_sig_def)
   apply(rule_tac
      t="min (length list) (length w)"
      and s="length w"
      in ssubst)
    apply(rename_tac w a list)(*strict*)
    apply(force)
   apply(rename_tac w a list)(*strict*)
   apply(rule drop_and_crop_makes_shorter)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(case_tac S)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac S1 S)
  apply(rename_tac w S1 S)(*strict*)
  apply(case_tac S)
   apply(rename_tac w S1 S)(*strict*)
   apply(clarsimp)
  apply(rename_tac w S1 S a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w S1 a list)(*strict*)
  apply(rename_tac S2 S)
  apply(rename_tac w S1 S2 S)(*strict*)
  apply(simp add: EValidSplit_producing_def)
  done

lemma restrict_PValidSplit_to_empty: "
  F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> PValidSplit_to_empty G (restrict G' G S (Suc n))"
  apply(simp add: PValidSplit_to_empty_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: EValidSplit_to_empty_def)
  apply(subgoal_tac "S!i \<in> set(butlast S)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i w' a')(*strict*)
   apply(subgoal_tac "(w' @ [a']) ! i = w'!i")
    apply(rename_tac i w' a')(*strict*)
    apply(force)
   apply(rename_tac i w' a')(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="S!i"
      in ballE)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "min (length S) (Suc n) = Suc n")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "nat_seq 0 n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq 0 n) = SSn + 1 - SSm" for SSn SSm)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp (no_asm) add: restrict_newprods_def restrict_newignore_def restrict_newto_def)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>x\<in> set (butlast S). (\<exists>y. ESplitItem_from x = Some y) \<and> (\<exists>y. ESplitItem_elem x = Some y)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_producing_def)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="S!i"
      in ballE)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(case_tac "ESplitItem_to (S ! i)")
   apply(rename_tac i y ya)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac i y)(*strict*)
   apply(case_tac y)
    apply(rename_tac i y q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac i q ba)(*strict*)
    apply(simp add: restrict_newprodsX_def restrict_newelem_def cropTol3l2_def cropTol3l2_single_def)
   apply(rename_tac i y q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(simp add: restrict_newprodsX_def restrict_newelem_def cropTol3l2_def cropTol3l2_single_def)
   apply(simp add: new_post_sig_def)
   apply(case_tac "i=n")
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(force)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(subgoal_tac "i<n")
    apply(rename_tac i q1 ba q2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))=SSx" for SSx)
    apply(rename_tac i q1 ba q2)(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(thin_tac "drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = []")
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(simp add: restrict_def restrict_map_def restrict_len_def)
   apply(simp add: restrict_newto_def)
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(simp add: EValidSplit_interlineX_def)
   apply(subgoal_tac "restrict_toberemoved (take (Suc n) S) ! i = takeB (length(restrict_toberemoved (take (Suc n) S) ! (Suc i))) (ESplitItem_ignore (S ! i))")
    apply(rename_tac i q1 ba q2)(*strict*)
    prefer 2
    apply(rule_tac
      t="S!i"
      and s="take(Suc n)S!i"
      in ssubst)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc i) @ option_to_list (ESplitItem_from (S ! Suc i))"
      and ?w1.0="[]"
      in restrict_toberemoved_direct_computation)
      apply(rename_tac i q1 ba q2)(*strict*)
      apply(force)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(rule_tac
      s="S!i"
      and t="take(Suc n)S!i"
      in ssubst)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(rule_tac
      s="S!Suc i"
      and t="take(Suc n)S!Suc i"
      in ssubst)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(rule sym)
    apply(force)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(simp add: takeB_def)
   apply(subgoal_tac "length (restrict_toberemoved (take (Suc n) S) ! (Suc i)) \<le> length (ESplitItem_ignore (take (Suc n) S ! (Suc i)))")
    apply(rename_tac i q1 ba q2)(*strict*)
    prefer 2
    apply(rule restrict_toberemoved_smaller_than_ignore)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(force)
   apply(rename_tac i q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_from (S ! Suc i)")
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_producing_def)
    apply(erule_tac
      x="S!Suc i"
      in ballE)
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(subgoal_tac "S ! Suc i \<in> set (butlast S)")
     apply(rename_tac i q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2)(*strict*)
    apply(rule butlast_nth_mem)
    apply(force)
   apply(rename_tac i q1 ba q2 a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "length (ESplitItem_ignore (S ! i)) \<le> length (restrict_toberemoved (take (Suc n) S) ! Suc i)")
    apply(rename_tac i q1 ba q2 a)(*strict*)
    prefer 2
    apply(rule_tac
      s="restrict_toberemovedX (take (Suc n) S) ! Suc (i)"
      and t="restrict_toberemoved (take (Suc n) S) ! Suc (i)"
      in subst)
     apply(rename_tac i q1 ba q2 a)(*strict*)
     apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac i q1 ba q2 a)(*strict*)
    apply(force)
   apply(rename_tac i q1 ba q2 a)(*strict*)
   apply(thin_tac "length (ESplitItem_ignore (S ! i)) \<le> length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
   apply(rename_tac i q1 ba q2 a)(*strict*)
   apply(subgoal_tac "length(ESplitItem_ignore (S ! (Suc i)))<length(ESplitItem_ignore (S ! i))")
    apply(rename_tac i q1 ba q2 a)(*strict*)
    apply(subgoal_tac "length(ESplitItem_ignore (S ! (Suc i)))\<ge>length(ESplitItem_ignore (S ! i))")
     apply(rename_tac i q1 ba q2 a)(*strict*)
     apply(force)
    apply(rename_tac i q1 ba q2 a)(*strict*)
    apply(force)
   apply(rename_tac i q1 ba q2 a)(*strict*)
   apply(rule_tac
      t="ESplitItem_ignore (S ! i)"
      and s="ESplitItem_elim (S ! Suc i) @ a # ESplitItem_ignore (S ! Suc i)"
      in ssubst)
    apply(rename_tac i q1 ba q2 a)(*strict*)
    apply(force)
   apply(rename_tac i q1 ba q2 a)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac i y ya a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_prods (S ! i) = []")
   apply(rename_tac i y ya a list)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def EValidSplit_ValidItem_def)
   apply(erule_tac
      x="S!i"
      in ballE)
    apply(rename_tac i y ya a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(simp add: EValidSplitItem_def)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac i y ya a list d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(rename_tac i y ya a list)(*strict*)
  apply(simp add: restrict_newprodsX_def)
  apply(subgoal_tac "False")
   apply(rename_tac i y ya a list)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(simp add: restrict_newto_def new_post_sig_def)
  apply(case_tac "i=n")
   apply(rename_tac i y ya a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac y a list)(*strict*)
   apply(simp add: restrict_toberemovedX_def)
   apply(subgoal_tac "(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc n = SSX" for SSX)
    apply(rename_tac y a list)(*strict*)
    prefer 2
    apply(rule nth_append_beyond)
    apply(rule_tac
      t="length (restrict_toberemoved (take (Suc n) S))"
      in ssubst)
     apply(rename_tac y a list)(*strict*)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(rename_tac y a list)(*strict*)
    apply(force)
   apply(rename_tac y a list)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc n = tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))")
   apply(rename_tac y a list)(*strict*)
   apply(subgoal_tac "length(drop_and_crop (a # list @ ESplitItem_ignore (S ! n)) (length (ESplitItem_to (last (take (Suc n) S))) + length (ESplitItem_ignore (last (take (Suc n) S))) - Suc 0)) = SSX" for SSX)
    apply(rename_tac y a list)(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac y a list)(*strict*)
   apply(clarsimp)
   apply(thin_tac "drop_and_crop (a # list @ ESplitItem_ignore (S ! n)) (length (ESplitItem_to (last (take (Suc n) S))) + length (ESplitItem_ignore (last (take (Suc n) S))) - Suc 0) = []")
   apply(rename_tac y a list)(*strict*)
   apply(subgoal_tac "last (take (Suc n) S) = S!n")
    apply(rename_tac y a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac y a list)(*strict*)
   apply(rule last_take_nth)
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(subgoal_tac "i<n")
   apply(rename_tac i y ya a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "drop_and_crop (a # list @ ESplitItem_ignore (S ! i)) (length (restrict_toberemoved (take (Suc n) S) ! Suc i)) = []")
   apply(rename_tac i y ya a list)(*strict*)
   prefer 2
   apply(rule_tac
      s="restrict_toberemovedX (take (Suc n) S) ! Suc i"
      and t="restrict_toberemoved (take (Suc n) S) ! Suc i"
      in subst)
    apply(rename_tac i y ya a list)(*strict*)
    apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(thin_tac "drop_and_crop (a # list @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = []")
  apply(rename_tac i y ya a list)(*strict*)
  apply(subgoal_tac "length(drop_and_crop (a # list @ ESplitItem_ignore (S ! i)) (length (restrict_toberemoved (take (Suc n) S) ! Suc i))) = SSX" for SSX)
   apply(rename_tac i y ya a list)(*strict*)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(rename_tac i y ya a list)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop_and_crop (a # list @ ESplitItem_ignore (S ! i)) (length (restrict_toberemoved (take (Suc n) S) ! Suc i)) = []")
  apply(rename_tac i y ya a list)(*strict*)
  apply(subgoal_tac "length (restrict_toberemoved (take (Suc n) S) ! (Suc i)) \<le> length (ESplitItem_ignore (take (Suc n) S ! (Suc i)))")
   apply(rename_tac i y ya a list)(*strict*)
   prefer 2
   apply(rule restrict_toberemoved_smaller_than_ignore)
    apply(rename_tac i y ya a list)(*strict*)
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (restrict_toberemoved (take (Suc n) S) ! i) \<le> length (ESplitItem_ignore (take (Suc n) S ! i))")
   apply(rename_tac i y ya a list)(*strict*)
   prefer 2
   apply(rule restrict_toberemoved_smaller_than_ignore)
    apply(rename_tac i y ya a list)(*strict*)
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S ! Suc i)")
   apply(rename_tac i y ya a list)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!Suc i"
      in ballE)
    apply(rename_tac i y ya a list)(*strict*)
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(subgoal_tac "S ! Suc i \<in> set (butlast S)")
    apply(rename_tac i y ya a list)(*strict*)
    apply(force)
   apply(rename_tac i y ya a list)(*strict*)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(simp add: EValidSplit_interline_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "length(a # list @ ESplitItem_ignore (S ! i))<length(a # list @ ESplitItem_ignore (S ! i))")
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(rule_tac
      y="Suc (length list + length (ESplitItem_ignore (S ! i)))"
      in le_less_trans)
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(rule_tac
      y="length (restrict_toberemoved (take (Suc n) S) ! Suc i)"
      in le_less_trans)
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(rule_tac
      y="length(ESplitItem_ignore (S ! Suc i))"
      in le_less_trans)
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(rule_tac
      y="length(ESplitItem_elim (S ! Suc i) @ aa # ESplitItem_ignore (S ! Suc i))"
      in less_le_trans)
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(rule_tac
      t="ESplitItem_elim (S ! Suc i) @ aa # ESplitItem_ignore (S ! Suc i)"
      and s="a # list @ ESplitItem_ignore (S ! i)"
      in ssubst)
   apply(rename_tac i y ya a list aa)(*strict*)
   apply(force)
  apply(rename_tac i y ya a list aa)(*strict*)
  apply(force)
  done

lemma restrict_PValidSplit_final: "
  split_TSstructure G
  \<Longrightarrow> F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> PValidSplit_final G (restrict G' G S (Suc n))"
  apply(simp add: PValidSplit_final_def)
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(subgoal_tac "min (length S)(Suc n) = Suc n")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq 0 n) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. nat_seq 0 n = w @ [n]")
   prefer 2
   apply(case_tac n)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply (metis natUptTo_n_n)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="nat_seq 0 nat"
      in exI)
   apply (metis le0 nat_seq_drop_last_simp)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! length w) @ ESplitItem_ignore (S ! length w)) (length (restrict_toberemovedX (take (Suc (length w)) S) ! Suc (length w))))=SSX" for SSX)
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (drop_and_crop (ESplitItem_to (S ! length w) @ ESplitItem_ignore (S ! length w)) (length (restrict_toberemovedX (take (Suc (length w)) S) ! Suc (length w)))) = length (ESplitItem_to (S ! length w)) + length (ESplitItem_ignore (S ! length w)) - length (restrict_toberemovedX (take (Suc (length w)) S) ! Suc (length w))")
  apply(rename_tac w)(*strict*)
  apply(case_tac "ESplitItem_to (S ! length w) = []")
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_to_empty_def)
   apply(erule_tac
      x="S!length w"
      in ballE)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(case_tac "ESplitItem_from (S ! length w)")
     apply(rename_tac w)(*strict*)
     apply(clarsimp)
    apply(rename_tac w a)(*strict*)
    apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      xs="S"
      in rev_cases)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(ys @ [y]) ! length w = SSX" for SSX)
    apply(rename_tac w ys y)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac w ys y)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "length(drop_and_crop (ESplitItem_to (S ! length w) @ ESplitItem_ignore (S ! length w)) (length (restrict_toberemovedX (take (Suc (length w)) S) ! Suc (length w)))) =SSX" for SSX)
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop_and_crop (ESplitItem_to (S ! length w) @ ESplitItem_ignore (S ! length w)) (length (restrict_toberemovedX (take (Suc (length w)) S) ! Suc (length w))) = []")
  apply(rename_tac w)(*strict*)
  apply(simp add: restrict_toberemovedX_def)
  apply(subgoal_tac "(restrict_toberemoved (take (Suc (length w)) S) @ [tl (ESplitItem_to (last (take (Suc (length w)) S)) @ ESplitItem_ignore (last (take (Suc (length w)) S)))]) ! Suc (length w)=SSX" for SSX)
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule nth_append_beyond)
   apply(rule_tac
      t="length (restrict_toberemoved (take (Suc (length w)) S))"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(restrict_toberemoved (take (Suc (length w)) S) @ [tl (ESplitItem_to (last (take (Suc (length w)) S)) @ ESplitItem_ignore (last (take (Suc (length w)) S)))]) ! Suc (length w) = tl (ESplitItem_to (last (take (Suc (length w)) S)) @ ESplitItem_ignore (last (take (Suc (length w)) S)))")
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "last (take (Suc (length w)) S)=SSX" for SSX)
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule last_take_nth)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(case_tac "length (ESplitItem_to (S ! length w))")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rename_tac w nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  done

lemma restrict_PValidSplit_belongs_prods_setB: "
F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> ESplitItem_to (S ! n) \<noteq> []
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> i < Suc n
  \<Longrightarrow> min (length S) (Suc n) = Suc n
  \<Longrightarrow> nat_seq 0 n ! i = i
  \<Longrightarrow> length (nat_seq 0 n) = Suc n
  \<Longrightarrow> EValidSplitItem_belongs G (S ! i)
  \<Longrightarrow> EValidSplitItem_elim G (S ! i)
  \<Longrightarrow> EValidSplitItem_gen G (S ! i)
  \<Longrightarrow> setB (PSplitItem_prods (restrict G' G S (Suc n) ! i)) \<subseteq> cfg_productions G"
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def restrict_newprods_def restrict_newprodsX_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>i. SSn\<le>i \<and> i\<le>SSm \<and> SSx \<in> setB [SSf i]" for SSn SSm SSx SSf)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule setB_map_nat_seq)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "x \<in> setB X" for X)
   apply(clarsimp)
   apply(rename_tac x ia)(*strict*)
   apply(case_tac "restrict_newprodsXX G ia (ESplitItem_prods (S ! i)) (ESplitItem_elem (S ! i)) ((restrict_newto (take (Suc n) S) i))")
    apply(rename_tac x ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac ia)(*strict*)
    apply(rule_tac
      A="set(ESplitItem_prods (S ! i))"
      in set_mp)
     apply(rename_tac ia)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
    apply(rename_tac ia)(*strict*)
    apply(rule nth_mem)
    apply(case_tac "length (ESplitItem_prods (S ! i))")
     apply(rename_tac ia)(*strict*)
     apply(force)
    apply(rename_tac ia nat)(*strict*)
    apply(force)
   apply(rename_tac x ia)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: setB_liftB)
  apply(rule_tac
      A="set(ESplitItem_prods (S ! i))"
      in set_mp)
   apply(rename_tac x)(*strict*)
   apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma restrict_PValidSplit_belongs_prods_setA: "
F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> ESplitItem_to (S ! n) \<noteq> []
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> i < Suc n
  \<Longrightarrow> min (length S) (Suc n) = Suc n
  \<Longrightarrow> nat_seq 0 n ! i = i
  \<Longrightarrow> length (nat_seq 0 n) = Suc n
  \<Longrightarrow> EValidSplitItem_belongs G (S ! i)
  \<Longrightarrow> EValidSplitItem_elim G (S ! i)
  \<Longrightarrow> EValidSplitItem_gen G (S ! i)
  \<Longrightarrow> setA (PSplitItem_prods (restrict G' G S (Suc n) ! i)) \<subseteq> epda_delta G'"
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def restrict_newprods_def restrict_newprodsX_def)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: setA_liftB)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>i. SSn\<le>i \<and> i\<le>SSm \<and> SSx \<in> setA [SSf i]" for SSn SSm SSx SSf)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule setA_map_nat_seq)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> setA X" for X)
  apply(clarsimp)
  apply(rename_tac x ia)(*strict*)
  apply(case_tac "restrict_newprodsXX G ia (ESplitItem_prods (S ! i)) (ESplitItem_elem (S ! i)) ((restrict_newto (take (Suc n) S) i))")
   apply(rename_tac x ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac x ia)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(rule THE_unique_edge_is_in_delta_prime_enhanced)
    apply(rename_tac ia)(*strict*)
    apply(force)
   apply(rename_tac ia)(*strict*)
   apply(rule_tac
      A="set(ESplitItem_prods (S ! i))"
      in set_mp)
    apply(rename_tac ia)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
   apply(rename_tac ia)(*strict*)
   apply(rule nth_mem)
   apply(case_tac "length (ESplitItem_prods (S ! i))")
    apply(rename_tac ia)(*strict*)
    apply(force)
   apply(rename_tac ia nat)(*strict*)
   apply(force)
  apply(rename_tac ia)(*strict*)
  apply(case_tac "length (ESplitItem_prods (S ! i))")
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S ! i)")
   apply(rename_tac ia nat)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac ia nat d)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!i"
      in ballE)
    apply(rename_tac ia nat d)(*strict*)
    apply(force)
   apply(rename_tac ia nat d)(*strict*)
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(rename_tac ia nat d)(*strict*)
    apply(force)
   apply(rename_tac ia nat d)(*strict*)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rename_tac ia nat a)(*strict*)
  apply(simp add: EValidSplit_producing_def)
  apply(erule_tac
      x="S!i"
      in ballE)
   apply(rename_tac ia nat a)(*strict*)
   prefer 2
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(rename_tac ia nat a)(*strict*)
    apply(force)
   apply(rename_tac ia nat a)(*strict*)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rename_tac ia nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia nat a y)(*strict*)
  apply(rule_tac
      xs="ESplitItem_to (S ! i)"
      in rev_cases)
   apply(rename_tac ia nat a y)(*strict*)
   prefer 2
   apply(rename_tac ia nat a y ys ya)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac ia nat a y ys ya d)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule notfinishingL_use)
      apply(rename_tac ia nat a y ys ya d)(*strict*)
      apply(rule_tac
      w="y # liftA ys"
      in trans_der_notfinishingL)
        apply(rename_tac ia nat a y ys ya d)(*strict*)
        apply(force)
       apply(rename_tac ia nat a y ys ya d)(*strict*)
       apply(force)
      apply(rename_tac ia nat a y ys ya d)(*strict*)
      apply (simp only: liftA_commutes_over_concat)
      apply(clarsimp)
      apply(force)
     apply(rename_tac ia nat a y ys ya d)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ia nat a y ys ya d)(*strict*)
    apply(force)
   apply(rename_tac ia nat a y ys ya d)(*strict*)
   apply(force)
  apply(rename_tac ia nat a y)(*strict*)
  apply(case_tac y)
   apply(rename_tac ia nat a y aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia nat a aa)(*strict*)
   apply(simp add: EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac ia nat a aa d)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule notfinishingL_use)
      apply(rename_tac ia nat a aa d)(*strict*)
      apply(rule_tac
      w="[]"
      in trans_der_notfinishingL)
        apply(rename_tac ia nat a aa d)(*strict*)
        apply(force)
       apply(rename_tac ia nat a aa d)(*strict*)
       apply(force)
      apply(rename_tac ia nat a aa d)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac ia nat a aa d)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ia nat a aa d)(*strict*)
    apply(force)
   apply(rename_tac ia nat a aa d)(*strict*)
   apply(force)
  apply(rename_tac ia nat a y ba)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ia nat a y ba)(*strict*)
   apply(force)
  apply(rename_tac ia nat a y ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia nat a ba)(*strict*)
  apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
       apply(rename_tac ia nat a ba)(*strict*)
       apply(force)+
  done

lemma restrict_toberemoved_at_last: "
  Suc i=length S
  \<Longrightarrow> restrict_toberemoved S! i = ESplitItem_ignore (S!i)"
  apply(simp add: restrict_toberemoved_def)
  apply(simp add: enforceSuffix_def)
  apply(rule_tac
      t="length S - Suc 0"
      and s="i"
      in ssubst)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 i) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 i ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: takeB_def)
  apply(subgoal_tac "length (ESplitItem_ignore (S ! i))\<le> Min (enforceSuffixS (map ESplitItem_ignore S) i)")
   apply(force)
  apply(rule_tac
      t="(x \<le> Min A)" for x A
      in ssubst)
   apply(rule Lattices_Big.linorder_class.Min_ge_iff)
    apply(rule enforceSuffixS_finite)
   apply(simp add: enforceSuffixS_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(simp add: enforceSuffixS_def)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(case_tac ia)
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia nat)(*strict*)
  apply(clarsimp)
  done

lemma restrict_PValidSplit_belongs: "
F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> ESplitItem_to (S ! n)\<noteq>[]
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> i < Suc n
  \<Longrightarrow> PValidSplitItem_belongs G' G (restrict G' G S (Suc n) ! i)"
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S!i"
      in ballE)
   prefer 2
   apply(force)
  apply(subgoal_tac "min (length S) (Suc n) = Suc n")
   prefer 2
   apply(force)
  apply(subgoal_tac "nat_seq 0 n ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 n) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_def)
  apply(simp add: PValidSplitItem_belongs_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: EValidSplitItem_belongs_def)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      in ssubst)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(case_tac "i=n")
    apply(rule disjI2)
    apply(simp add: restrict_toberemovedX_def)
    apply(rule_tac
      t="(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc n"
      in ssubst)
     apply(rule nth_append_beyond)
     apply(rule_tac
      t="length(restrict_toberemoved (take (Suc n) S))"
      in ssubst)
      apply(rule length_restrict_toberemoved)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "last (take (Suc n) S) = S!n")
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
     apply(case_tac "ESplitItem_to (S ! n)")
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x a list)(*strict*)
     apply(clarsimp)
     apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
    apply(rename_tac x)(*strict*)
    apply(rule last_take_nth)
    apply(force)
   apply(subgoal_tac "i<n")
    prefer 2
    apply(force)
   apply(rule_tac
      t="restrict_toberemovedX (take (Suc n) S) ! Suc i"
      and s="restrict_toberemoved (take (Suc n) S) ! Suc i"
      in ssubst)
    apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
    apply(force)
   apply(case_tac "restrict_toberemoved (take (Suc n) S) ! Suc i")
    apply(rule disjI2)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: drop_and_crop_def butn_def)
    apply(subgoal_tac "cropTol3l2 (ESplitItem_ignore (S ! i)) = ESplitItem_ignore (S ! i)")
     apply(rename_tac x)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(clarsimp)
    apply(rule cropTol3l2_of_tail_of_proper_l3_l2_seq_ident)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule disjI1)
   apply(case_tac "ESplitItem_ignore (S ! i)")
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(simp add: drop_and_crop_def butn_def cropTol3l2_def fillL_def appL_def)
   apply(rename_tac a list aa lista)(*strict*)
   apply(subgoal_tac "\<exists>q. fillL (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemoved (take (Suc n) S) ! Suc i))) q = butn SSw SSn" for SSw SSn)
    apply(rename_tac a list aa lista)(*strict*)
    prefer 2
    apply(rule fillL_exists)
     apply(rename_tac a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac a list aa lista)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac a list aa lista)(*strict*)
     prefer 2
     apply(rule_tac
      n="length(ESplitItem_elim (S ! i) @ option_to_list (ESplitItem_from (S ! i)))"
      in proper_l3_l2_seq_drop)
      apply(rename_tac a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac a list aa lista)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list aa lista q)(*strict*)
   apply(rule_tac
      x="q"
      in exI)
   apply(clarsimp)
   apply(rename_tac a list aa lista q x)(*strict*)
   apply(subgoal_tac "x \<in> set(aa#lista)")
    apply(rename_tac a list aa lista q x)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
    apply(clarsimp)
    apply(force)
   apply(rename_tac a list aa lista q x)(*strict*)
   apply(rule_tac
      A="set (butn (aa # lista) (Suc (length list)))"
      in set_mp)
    apply(rename_tac a list aa lista q x)(*strict*)
    apply(rule set_butn_subset)
   apply(rename_tac a list aa lista q x)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      and s="X" for X
      in ssubst)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(case_tac "ESplitItem_from (S ! i)")
    apply(clarsimp)
    apply(simp add: EValidSplit_producing_def)
    apply(erule_tac
      x="S!i"
      in ballE)
     apply(force)
    apply(subgoal_tac "S!i\<in> set(butlast S)")
     apply(force)
    apply(rule butlast_nth_mem)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "ESplitItem_ignore (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac a)(*strict*)
   apply(erule disjE)
    apply(rename_tac a)(*strict*)
    apply(rule disjI2)
    apply(clarsimp)
    apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
    apply(case_tac a)
     apply(rename_tac a q ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q ba)(*strict*)
     apply(simp add: cropTol3l2_single_def)
     apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
    apply(rename_tac a q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 ba q2)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac q1 ba q2)(*strict*)
    apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! i) @ [cons_l3 q1 ba q2])")
     apply(rename_tac q1 ba q2)(*strict*)
     prefer 2
     apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
    apply(rename_tac q1 ba q2)(*strict*)
    apply(rule proper_l3_l2_seq_nol3)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(case_tac "drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))")
    apply(rename_tac a)(*strict*)
    apply(rule disjI1)
    apply(clarsimp)
    apply(rename_tac a w' a')(*strict*)
    apply(case_tac a)
     apply(rename_tac a w' a' q ba)(*strict*)
     apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! i) @ cons_l2 q ba # w' @ [a'])")
      apply(rename_tac a w' a' q ba)(*strict*)
      prefer 2
      apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
     apply(rename_tac a w' a' q ba)(*strict*)
     apply(rule proper_l3_l2_seq_nol2)
     apply(force)
    apply(rename_tac a w' a' q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' q1 ba q2)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def)
    apply(rule_tac
      x="q2"
      in exI)
    apply(simp add: fill_def)
    apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
   apply(rename_tac a aa list)(*strict*)
   apply(rule disjI2)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac a aa list w' a')(*strict*)
   apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newignore_def restrict_newto_def new_post_sig_def)
   apply(subgoal_tac "ESplitItem_ignore (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(subgoal_tac "ESplitItem_to (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(subgoal_tac "butn (ESplitItem_ignore (S ! i)) ((length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(case_tac "ESplitItem_from (S ! i)")
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: EValidSplit_producing_def)
    apply(erule_tac
      x="S!i"
      in ballE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "S!i\<in> set(butlast S)")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule butlast_nth_mem)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(erule_tac
      P="ESplitItem_to (S ! i) = []"
      in disjE)
    apply(rename_tac a)(*strict*)
    apply(rule disjI2)
    apply(rule_tac
      t="ESplitItem_to (S ! i)"
      and s="[]"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(erule_tac
      P="ESplitItem_ignore (S ! i) = []"
      in disjE)
    apply(rename_tac a)(*strict*)
    apply(case_tac "(length (restrict_toberemovedX (take (Suc n) S) ! Suc i))")
     apply(rename_tac a)(*strict*)
     apply(rule disjI2)
     apply(clarsimp)
     apply(rename_tac a x w' a')(*strict*)
     apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
     apply(case_tac a')
      apply(rename_tac a x w' a' q ba)(*strict*)
      prefer 2
      apply(rename_tac a x w' a' q1 ba q2)(*strict*)
      apply(clarsimp)
      apply(rename_tac a x w' q1 ba q2)(*strict*)
      apply(subgoal_tac "proper_l3_l2_seq (filterA (option_to_list (ESplitItem_elem (S ! i))) @ w' @ [cons_l3 q1 ba q2])")
       apply(rename_tac a x w' q1 ba q2)(*strict*)
       apply(rule_tac
      w="filterA (option_to_list (ESplitItem_elem (S ! i))) @ w'"
      in proper_l3_l2_seq_nol3)
       apply(rename_tac a x w' q1 ba q2)(*strict*)
       apply(force)
      apply(rename_tac a x w' q1 ba q2)(*strict*)
      apply(simp add: EValidSplitItem_belongs_def)
     apply(rename_tac a x w' a' q ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac a x w' q ba)(*strict*)
     apply(simp add: cropTol3l2_single_def)
     apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
     apply(force)
    apply(rename_tac a nat)(*strict*)
    apply(rule disjI1)
    apply(thin_tac "butn (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = [] \<or> (\<exists>w' a'. butn (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = w' @ [a'])")
    apply(rename_tac a nat)(*strict*)
    apply(erule exE)+
    apply(rename_tac a nat w' a')(*strict*)
    apply(rule_tac
      t="ESplitItem_to (S ! i)"
      and s="w'@[a']"
      in ssubst)
     apply(rename_tac a nat w' a')(*strict*)
     apply(force)
    apply(rename_tac a nat w' a')(*strict*)
    apply(rule_tac
      t="ESplitItem_ignore (S ! i)"
      and s="[]"
      in ssubst)
     apply(rename_tac a nat w' a')(*strict*)
     apply(force)
    apply(rename_tac a nat w' a')(*strict*)
    apply(rule_tac
      t="take (length (w' @ [a'])) (drop_and_crop ((w' @ [a']) @ []) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      and s="drop_and_crop ((w' @ [a']) @ []) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))"
      in ssubst)
     apply(rename_tac a nat w' a')(*strict*)
     apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
    apply(rename_tac a nat w' a')(*strict*)
    apply(subgoal_tac "proper_l3_l2_seq (w' @ [a'])")
     apply(rename_tac a nat w' a')(*strict*)
     prefer 2
     apply(subgoal_tac "proper_l3_l2_seq (filterA (option_to_list (ESplitItem_elem (S ! i))) @ w' @ [a'])")
      apply(rename_tac a nat w' a')(*strict*)
      prefer 2
      apply(simp add: EValidSplitItem_belongs_def)
     apply(rename_tac a nat w' a')(*strict*)
     apply(subgoal_tac "proper_l3_l2_seq (drop SSn SSw)" for SSn SSw)
      apply(rename_tac a nat w' a')(*strict*)
      prefer 2
      apply(rule_tac
      n="length(filterA (option_to_list (ESplitItem_elem (S ! i))))"
      and w="filterA (option_to_list (ESplitItem_elem (S ! i))) @ w' @ [a']"
      in proper_l3_l2_seq_drop)
       apply(rename_tac a nat w' a')(*strict*)
       apply(force)
      apply(rename_tac a nat w' a')(*strict*)
      apply(force)
     apply(rename_tac a nat w' a')(*strict*)
     apply(force)
    apply(rename_tac a nat w' a')(*strict*)
    apply(subgoal_tac "\<exists>q. fillL (drop_and_crop SSw SSn) q = butn SSw SSn" for SSw SSn)
     apply(rename_tac a nat w' a')(*strict*)
     prefer 2
     apply(rule_tac
      n="length (restrict_toberemovedX (take (Suc n) S) ! Suc i)"
      in fillL_exists)
      apply(rename_tac a nat w' a')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac a nat w' a')(*strict*)
     apply(force)
    apply(rename_tac a nat w' a')(*strict*)
    apply(erule exE)+
    apply(rename_tac a nat w' a' q)(*strict*)
    apply(rule_tac
      x="q"
      in exI)
    apply(rule_tac
      B="set(butn (w' @ [a']) (length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))))"
      in subset_trans)
     apply(rename_tac a nat w' a' q)(*strict*)
     apply(force)
    apply(rename_tac a nat w' a' q)(*strict*)
    apply(rule_tac
      B="set(w' @ [a'])"
      in subset_trans)
     apply(rename_tac a nat w' a' q)(*strict*)
     apply(rule set_butn_subset)
    apply(rename_tac a nat w' a' q)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
   apply(rename_tac a)(*strict*)
   apply(erule disjE)
    apply(rename_tac a)(*strict*)
    apply(rule disjI1)
    apply(rule_tac
      t="take (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(rule take_all)
     apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))=SSX" for SSX)
      apply(rename_tac a)(*strict*)
      prefer 2
      apply(rule drop_and_crop_length)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(rename_tac a w' w'a a' a'a)(*strict*)
     apply(simp add: butn_def)
     apply(clarsimp)
     apply(thin_tac "length (drop_and_crop (w' @ a' # w'a @ [a'a]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = Suc (Suc (length w' + length w'a)) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
     apply(rename_tac a w' w'a a' a'a)(*strict*)
     apply(case_tac "length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
      apply(rename_tac a w' w'a a' a'a)(*strict*)
      apply(clarsimp)
     apply(rename_tac a w' w'a a' a'a nat)(*strict*)
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac a w' w'a a' a'a nat)(*strict*)
      apply(force)
     apply(rename_tac a w' w'a a' a'a nat)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule_tac
      w="ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)"
      and n="length (restrict_toberemovedX (take (Suc n) S) ! Suc i)"
      in fillL_exists)
      apply(rename_tac a)(*strict*)
      apply(simp add: butn_def)
      apply(erule disjE)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def)
     apply(rule proper_l3_l2_seq_drop_prime)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(erule exE)+
    apply(rename_tac a w' w'a q a' a'a)(*strict*)
    apply(rule_tac
      x="q"
      in exI)
    apply(rule_tac
      B="set(butn (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      in subset_trans)
     apply(rename_tac a w' w'a q a' a'a)(*strict*)
     apply(force)
    apply(rename_tac a w' w'a q a' a'a)(*strict*)
    apply(rule_tac
      B="set(ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i))"
      in subset_trans)
     apply(rename_tac a w' w'a q a' a'a)(*strict*)
     apply(rule set_butn_subset)
    apply(rename_tac a w' w'a q a' a'a)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def)
   apply(rename_tac a)(*strict*)
   apply(rule disjI2)
   apply(erule exE)+
   apply(rename_tac a w' w'a w'b a' a'a a'b)(*strict*)
   apply(rule_tac
      t="take (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
      and s="ESplitItem_to (S ! i)"
      in ssubst)
    apply(rename_tac a w' w'a w'b a' a'a a'b)(*strict*)
    apply(simp add: drop_and_crop_def butn_def)
    apply(case_tac "length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
     apply(rename_tac a w' w'a w'b a' a'a a'b)(*strict*)
     apply(clarsimp)
     apply(rename_tac a w' w'b a' a'b)(*strict*)
     apply(simp add: cropTol3l2_def)
     apply(rule_tac
      t="butlast (w' @ a' # w'b @ [a'b])"
      in ssubst)
      apply(rename_tac a w' w'b a' a'b)(*strict*)
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac a w' w'b a' a'b)(*strict*)
     apply(force)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat)(*strict*)
    apply(clarsimp)
    apply(case_tac "Suc (length w'a) - nat")
     apply(rename_tac a w' w'a w'b a' a'a a'b nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_def)
    apply(rule conjI)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
     apply(force)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
    apply(rule conjI)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
     apply(force)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "take nata w'a=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
    apply(erule disjE)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata)(*strict*)
    apply(erule exE)+
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata w'c a'c)(*strict*)
    apply(rule_tac
      t="take nata w'a"
      and s="w'c@[a'c]"
      in ssubst)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata w'c a'c)(*strict*)
     apply(force)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata w'c a'c)(*strict*)
    apply(rule_tac
      t="butlast (w' @ a' # w'c @ [a'c])"
      in ssubst)
     apply(rename_tac a w' w'a w'b a' a'a a'b nat nata w'c a'c)(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac a w' w'a w'b a' a'a a'b nat nata w'c a'c)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w' w'a w'b a' a'a a'b)(*strict*)
   apply(simp add: EValidSplitItem_belongs_def)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!i"
      in ballE)
    apply(clarsimp)
    apply(rename_tac x y ya)(*strict*)
    apply(case_tac ya)
     apply(rename_tac x y ya a)(*strict*)
     apply(clarsimp)
     apply(rename_tac y a)(*strict*)
     apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
    apply(rename_tac x y ya ba)(*strict*)
    apply(clarsimp)
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(force)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!i"
      in ballE)
    apply(clarsimp)
    apply(rename_tac x y ya)(*strict*)
    apply(case_tac ya)
     apply(rename_tac x y ya a)(*strict*)
     apply(clarsimp)
    apply(rename_tac x y ya ba)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def option_to_list_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rule conjI)
   apply(rule restrict_PValidSplit_belongs_prods_setB)
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
  apply(rule conjI)
   apply(rule restrict_PValidSplit_belongs_prods_setA)
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
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
   apply(simp add: EValidSplitItem_belongs_def)
  apply(rule conjI)
   apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! i) @ option_to_list (ESplitItem_from (S ! i)) @ ESplitItem_ignore (S ! i))")
    prefer 2
    apply(simp add: EValidSplitItem_belongs_def)
   apply(case_tac "ESplitItem_from (S ! i)")
    apply(clarsimp)
    apply(simp add: EValidSplit_producing_def)
    apply(erule_tac
      x="S!i"
      in ballE)
     apply(force)
    apply(subgoal_tac "S!i\<in> set(butlast S)")
     apply(force)
    apply(rule butlast_nth_mem)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
   apply(case_tac "restrict_newignore (take (Suc n) S) i")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "ESplitItem_ignore (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac a)(*strict*)
    apply(erule disjE)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(simp add: cropTol3l2_def cropTol3l2_single_def)
     apply(case_tac a)
      apply(rename_tac a q ba)(*strict*)
      apply(clarsimp)
     apply(rename_tac a q1 ba q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac q1 ba q2)(*strict*)
     apply(simp add: proper_l3_l2_seq_def)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(rename_tac a w' a')(*strict*)
    apply(case_tac a)
     apply(rename_tac a w' a' q ba)(*strict*)
     apply(simp (no_asm) add: proper_l3_l2_seq_def)
     apply(clarsimp)
     apply(rename_tac w' a' q ba)(*strict*)
     apply(simp add: option_to_list_def)
     apply(subgoal_tac "False")
      apply(rename_tac w' a' q ba)(*strict*)
      apply(force)
     apply(rename_tac w' a' q ba)(*strict*)
     apply(rule_tac
      w="ESplitItem_elim (S ! i)"
      in proper_l3_l2_seq_nol2)
     apply(force)
    apply(rename_tac a w' a' q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' q1 ba q2)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def)
    apply(simp add: option_to_list_def)
    apply(rule proper_l3_seq_drop_tail_X)
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(rule_tac
      t="hd (cropTol3l2 (a # restrict_newignore (take (Suc n) S) i))"
      and s="a"
      in ssubst)
    apply(rename_tac a aa list)(*strict*)
    apply(simp add: cropTol3l2_def)
   apply(rename_tac a aa list)(*strict*)
   apply(simp add: restrict_newignore_def new_post_sig_def)
   apply(subgoal_tac "drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) = aa#list")
    apply(rename_tac a aa list)(*strict*)
    prefer 2
    apply(rule_tac
      t="aa#list"
      and s="drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! (Suc i) )))"
      in ssubst)
     apply(rename_tac a aa list)(*strict*)
     apply(force)
    apply(rename_tac a aa list)(*strict*)
    apply(rule sym)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(rename_tac a aa list)(*strict*)
   apply(thin_tac "drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = aa # list")
   apply(rename_tac a aa list)(*strict*)
   apply(subgoal_tac "proper_l3_l2_seq (SSw @ drop_and_crop SSv SSn)" for SSw SSv SSn)
    apply(rename_tac a aa list)(*strict*)
    prefer 2
    apply(rule_tac
      w="ESplitItem_elim (S ! i) @ a#[]"
      and v="ESplitItem_ignore (S ! i)"
      and n="length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))"
      in drop_and_crop_preserves_l3_l2_separation)
     apply(rename_tac a aa list)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac a aa list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
   apply(case_tac "length (ESplitItem_ignore (S ! i)) \<le> length (restrict_toberemovedX(take (Suc n) S) ! Suc i) \<or> ESplitItem_ignore (S ! i) = []")
    apply(rename_tac a aa list)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac a aa list)(*strict*)
     apply(force)
    apply(rename_tac a aa list)(*strict*)
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: EValidSplit_producing_def)
  apply(erule_tac
      x="S!i"
      in ballE_prime)
   prefer 2
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(force)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(erule_tac
      x="S!min(Suc i)n"
      in ballE)
   prefer 2
   apply(subgoal_tac "S!min(Suc i)n\<in> set(butlast S)")
    apply(force)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(clarsimp)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def restrict_newelem_def)
  apply(subgoal_tac "((ESplitItem_to (S ! i) = [] \<longrightarrow> filterA (option_to_list (Some ya)) = [] \<longrightarrow> ESplitItem_ignore (S ! i) \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (option_to_list (Some ya)) @ ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)))")
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(simp add: EValidSplitItem_belongs_def)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(erule_tac
      P="ESplitItem_to (S ! i) = [] \<longrightarrow> filterA (option_to_list (Some ya)) = [] \<longrightarrow> ESplitItem_ignore (S ! i) \<noteq> []"
      in impE)
   apply(rename_tac y ya yb yc)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac ya)
    apply(rename_tac y ya yb yc a)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya yb yc ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac y yb yc ba)(*strict*)
   apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
        apply(rename_tac y yb yc ba)(*strict*)
        apply(force)
       apply(rename_tac y yb yc ba)(*strict*)
       apply(force)
      apply(rename_tac y yb yc ba)(*strict*)
      apply(force)
     apply(rename_tac y yb yc ba)(*strict*)
     apply(force)
    apply(rename_tac y yb yc ba)(*strict*)
    apply(force)
   apply(rename_tac y yb yc ba)(*strict*)
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def restrict_newignore_def restrict_newto_def new_post_sig_def)
  apply(simp add: option_to_list_def)
  apply(rule drop_and_crop_preserves_l3_l2_separation)
   apply(rename_tac y ya yb yc)(*strict*)
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(simp add: restrict_newto_def)
  apply(case_tac "i=n")
   apply(rename_tac y ya yb yc)(*strict*)
   apply(thin_tac "PValidSplit_interline (map (\<lambda>i. \<lparr>PSplitItem_elim = ESplitItem_elim (take (Suc n) S ! i), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from (take (Suc n) S ! i)) # restrict_newignore (take (Suc n) S) i)), PSplitItem_ignore = restrict_newignore (take (Suc n) S) i, PSplitItem_elim_prods = ESplitItem_elim_prods (take (Suc n) S ! i), PSplitItem_prods = restrict_newprods G' G (take (Suc n) S) i, PSplitItem_elem = the (ESplitItem_elem (take (Suc n) S ! i)), PSplitItem_to = take (length (ESplitItem_to (take (Suc n) S ! i))) (new_post_sig (take (Suc n) S) i)\<rparr>) (nat_seq 0 n))")
   apply(rename_tac y ya yb yc)(*strict*)
   apply(clarsimp)
   apply(rename_tac y yb yc)(*strict*)
   apply(subgoal_tac "restrict_toberemoved (take (Suc n) S)! n = ESplitItem_ignore (take (Suc n) S!n)")
    apply(rename_tac y yb yc)(*strict*)
    prefer 2
    apply(rule restrict_toberemoved_at_last)
    apply(force)
   apply(rename_tac y yb yc)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (Suc n) n = n")
    apply(rename_tac y yb yc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y yb yc)(*strict*)
   apply(clarsimp)
   apply(rename_tac yb)(*strict*)
   apply(simp add: restrict_toberemovedX_def)
   apply(rule_tac
      t="(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc n"
      in ssubst)
    apply(rename_tac yb)(*strict*)
    apply(rule nth_append_beyond)
    apply(rule_tac
      t="length(restrict_toberemoved (take (Suc n) S))"
      in ssubst)
     apply(rename_tac yb)(*strict*)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(rename_tac yb)(*strict*)
    apply(force)
   apply(rename_tac yb)(*strict*)
   apply(simp add: restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="last (take (Suc n) S)"
      in ssubst)
    apply(rename_tac yb)(*strict*)
    apply(rule last_take_nth)
    apply(force)
   apply(rename_tac yb)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(subgoal_tac "i<n")
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(simp only: PValidSplit_interline_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: PValidSplit_interlineX_def)
  apply(subgoal_tac "nat_seq 0 n ! Suc i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac y ya yb yc)(*strict*)
    apply(force)
   apply(rename_tac y ya yb yc)(*strict*)
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min (Suc i) n = Suc i")
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_to (S ! i)=[]")
   apply(rename_tac y ya yb yc)(*strict*)
   apply(clarsimp)
   apply(case_tac ya)
    apply(rename_tac y ya yb yc a)(*strict*)
    apply(clarsimp)
    apply(rename_tac y yb yc a)(*strict*)
    prefer 2
    apply(rename_tac y ya yb yc ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac y yb yc ba)(*strict*)
    apply (metis EValidSplit_DERIVED_terminal_produce_produces_to)
   apply(rename_tac y yb yc a)(*strict*)
   apply(simp add: restrict_newignore_def new_post_sig_def)
   apply(subgoal_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = SSX" for SSX)
    apply(rename_tac y yb yc a)(*strict*)
    prefer 2
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(rename_tac y yb yc a)(*strict*)
   apply(clarsimp)
   apply(thin_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = drop_and_crop (ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))")
   apply(rename_tac y yb yc a)(*strict*)
   apply(subgoal_tac "length(drop_and_crop (ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i))))=SSX" for SSX)
    apply(rename_tac y yb yc a)(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac y yb yc a)(*strict*)
   apply(subgoal_tac "length(drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))=SSX" for SSX)
    apply(rename_tac y yb yc a)(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac y yb yc a)(*strict*)
   apply(case_tac "length (ESplitItem_ignore (S ! i)) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
    apply(rename_tac y yb yc a)(*strict*)
    apply(clarsimp)
   apply(rename_tac y yb yc a nat)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = SSX" for SSX)
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop (length (ESplitItem_to (S ! Suc i))) (drop_and_crop (ESplitItem_to (S ! Suc i) @ ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))) = drop_and_crop (ESplitItem_ignore (S ! Suc i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc (Suc i)))")
  apply(rename_tac y ya yb yc)(*strict*)
  apply(case_tac "drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = []")
   apply(rename_tac y ya yb yc)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(subgoal_tac "length(drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = SSX" for SSX)
   apply(rename_tac y ya yb yc)(*strict*)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(rename_tac y ya yb yc)(*strict*)
  apply(clarsimp)
  apply(case_tac "length (ESplitItem_to (S ! i)) + length (ESplitItem_ignore (S ! i)) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
   apply(rename_tac y ya yb yc)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya yb yc nat)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma restrict_PValidSplit_elim: "
  F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> i < Suc n
  \<Longrightarrow> PValidSplitItem_elim G (restrict G' G S (Suc n) ! i)"
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S!i"
      in ballE)
   prefer 2
   apply(force)
  apply(subgoal_tac "min (length S) (Suc n) = Suc n")
   prefer 2
   apply(force)
  apply(subgoal_tac "nat_seq 0 n ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 n) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_def)
  apply(simp add: PValidSplitItem_elim_def EValidSplitItem_elim_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp add: elim_map_def)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  done

lemma restrict_PValidSplit_gen: "
F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> ESplitItem_to (S ! n)\<noteq>[]
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> PValidSplitItem_belongs G' G (restrict G' G S (Suc n) ! i)
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> i < Suc n
  \<Longrightarrow> PValidSplitItem_gen G' G (restrict G' G S (Suc n) ! i)"
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S!i"
      in ballE)
   prefer 2
   apply(force)
  apply(subgoal_tac "min (length S) (Suc n) = Suc n")
   prefer 2
   apply(force)
  apply(subgoal_tac "nat_seq 0 n ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 n) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_def)
  apply(simp add: PValidSplitItem_gen_def)
  apply(subgoal_tac "(\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (ESplitItem_from (S ! i)))\<rparr> (ESplitItem_prods (S ! i)) \<lparr>cfg_conf = option_to_list (ESplitItem_elem (S ! i)) @ liftA (ESplitItem_to (S ! i))\<rparr> \<and> ((\<exists>b. Some (teB b) = ESplitItem_elem (S ! i)) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> the (ESplitItem_elem (S ! i)))) \<and> ((\<exists>A. Some (teA A) = ESplitItem_elem (S ! i)) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S ! i) = []))")
   prefer 2
   apply(simp add: EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(simp (no_asm_simp) add: restrict_def restrict_map_def restrict_len_def)
  apply(simp add: EValidSplit_producing_def)
  apply(erule_tac
      x="S!i"
      in ballE)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(subgoal_tac "S!i\<in> set(butlast S)")
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(rule butlast_nth_mem)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d y ya)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      x="(ESplitItem_prods (S ! i))"
      in exI)
  apply(rule conjI)
   apply(rename_tac d y ya)(*strict*)
   apply(simp add: concretization_def restrict_newelem_def)
   apply(case_tac "length (ESplitItem_prods (S ! i))")
    apply(rename_tac d y ya)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
   apply(rename_tac d y ya nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq 0 nat) = SSn + 1 - SSm" for SSn SSm)
    apply(rename_tac d y ya nat)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d y ya nat)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d y ya nat)(*strict*)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(rule conjI)
     apply(rename_tac d y ya nat)(*strict*)
     apply(force)
    apply(rename_tac d y ya nat)(*strict*)
    apply(clarsimp)
    apply (metis liftB_reflects_length)
   apply(rename_tac d y ya nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d y ya nat ia)(*strict*)
   apply(case_tac "ESplitItem_prods (S ! i) = []")
    apply(rename_tac d y ya nat ia)(*strict*)
    apply(clarsimp)
   apply(rename_tac d y ya nat ia)(*strict*)
   apply(subgoal_tac "nat_seq 0 (length(ESplitItem_prods (S ! i))-Suc 0) ! ia = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d y ya nat ia)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d y ya nat ia)(*strict*)
     apply(force)
    apply(rename_tac d y ya nat ia)(*strict*)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(case_tac "restrict_newignore (take (Suc n) S) i")
     apply(rename_tac d y ya nat ia)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(rename_tac d y ya nat ia a list)(*strict*)
    apply(clarsimp)
    apply (metis liftB_reflects_length less_Suc_eq_le)
   apply(rename_tac d y ya nat ia)(*strict*)
   apply(clarsimp)
   apply(case_tac "restrict_newprods G' G (take (Suc n) S) i ! ia")
    apply(rename_tac d y ya nat ia a)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprods_def restrict_newprodsX_def)
    apply(case_tac "restrict_newignore (take (Suc n) S) i = []")
     apply(rename_tac d y ya nat ia a)(*strict*)
     apply(clarsimp)
     apply(simp add: restrict_newprodsX_def)
     apply(case_tac "restrict_newprodsXX G ia (ESplitItem_prods (S ! i)) (Some ya) ((restrict_newto (take (Suc n) S) i))")
      apply(rename_tac d y ya nat ia a)(*strict*)
      apply(clarsimp)
     apply(rename_tac d y ya nat ia a)(*strict*)
     apply(clarsimp)
     apply(rename_tac d y ya nat ia)(*strict*)
     apply(rule theI_prime2)
      apply(rename_tac d y ya nat ia)(*strict*)
      apply(rule unique_edge_exists_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_enhanced)
        apply(rename_tac d y ya nat ia)(*strict*)
        apply(force)
       apply(rename_tac d y ya nat ia)(*strict*)
       apply(simp add: EValidSplitItem_belongs_def)
       apply(clarsimp)
       apply(rule_tac
      A="set(ESplitItem_prods (S ! i))"
      in set_mp)
        apply(rename_tac d y ya nat ia)(*strict*)
        apply(force)
       apply(rename_tac d y ya nat ia)(*strict*)
       apply(force)
      apply(rename_tac d y ya nat ia)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d y ya nat ia)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      xs="ESplitItem_to (S ! i)"
      in rev_cases)
      apply(rename_tac d y ya nat ia)(*strict*)
      prefer 2
      apply(rename_tac d y ya nat ia ys yb)(*strict*)
      apply(simp add: EValidSplitItem_gen_def)
      apply(clarsimp)
      apply(rename_tac d y ya nat ia ys yb da)(*strict*)
      apply(simp add: option_to_list_def)
      apply(rule notfinishingL_use)
         apply(rename_tac d y ya nat ia ys yb da)(*strict*)
         apply(rule_tac
      w="ya # liftA ys"
      in trans_der_notfinishingL)
           apply(rename_tac d y ya nat ia ys yb da)(*strict*)
           apply(force)
          apply(rename_tac d y ya nat ia ys yb da)(*strict*)
          apply(force)
         apply(rename_tac d y ya nat ia ys yb da)(*strict*)
         apply (simp only: liftA_commutes_over_concat)
         apply(clarsimp)
         apply(force)
        apply(rename_tac d y ya nat ia ys yb da)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac d y ya nat ia ys yb da)(*strict*)
       apply(force)
      apply(rename_tac d y ya nat ia ys yb da)(*strict*)
      apply(force)
     apply(rename_tac d y ya nat ia)(*strict*)
     apply(case_tac ya)
      apply(rename_tac d y ya nat ia a)(*strict*)
      apply(clarsimp)
      apply(rename_tac d y nat ia a)(*strict*)
      apply(simp add: EValidSplitItem_gen_def)
      apply(clarsimp)
      apply(rename_tac d y nat ia a da)(*strict*)
      apply(simp add: option_to_list_def)
      apply(rule notfinishingL_use)
         apply(rename_tac d y nat ia a da)(*strict*)
         apply(rule_tac
      w="[]"
      in trans_der_notfinishingL)
           apply(rename_tac d y nat ia a da)(*strict*)
           apply(force)
          apply(rename_tac d y nat ia a da)(*strict*)
          apply(force)
         apply(rename_tac d y nat ia a da)(*strict*)
         apply(clarsimp)
         apply(force)
        apply(rename_tac d y nat ia a da)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac d y nat ia a da)(*strict*)
       apply(force)
      apply(rename_tac d y nat ia a da)(*strict*)
      apply(force)
     apply(rename_tac d y ya nat ia ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac d y nat ia ba)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac d y nat ia ba)(*strict*)
      apply(force)
     apply(rename_tac d y nat ia ba)(*strict*)
     apply(rule_tac
      S="S!i"
      in EValidSplit_DERIVED_terminal_produce_produces_to)
          apply(rename_tac d y nat ia ba)(*strict*)
          apply(force)
         apply(rename_tac d y nat ia ba)(*strict*)
         apply(force)
        apply(rename_tac d y nat ia ba)(*strict*)
        apply(simp add: EValidSplitItem_gen_def)
       apply(rename_tac d y nat ia ba)(*strict*)
       apply(force)
      apply(rename_tac d y nat ia ba)(*strict*)
      apply(force)
     apply(rename_tac d y nat ia ba)(*strict*)
     apply(force)
    apply(rename_tac d y ya nat ia a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(rename_tac d y ya nat ia a)(*strict*)
     apply(force)
    apply(rename_tac d y ya nat ia a)(*strict*)
    apply (metis liftB_reflects_length teB_nth_liftB DT_two_elements.distinct(1))
   apply(rename_tac d y ya nat ia ba)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newprods_def restrict_newprodsX_def)
   apply(case_tac "restrict_newignore (take (Suc n) S) i = []")
    apply(rename_tac d y ya nat ia ba)(*strict*)
    apply(clarsimp)
    apply(simp add: restrict_newprodsX_def)
    apply(case_tac "restrict_newprodsXX G ia (ESplitItem_prods (S ! i)) (Some ya) ((restrict_newto (take (Suc n) S) i))")
     apply(rename_tac d y ya nat ia ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac d y ya nat ia ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac d y ya nat ia ba)(*strict*)
   apply(clarsimp)
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
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "X" for X)
   apply(thin_tac "restrict_newignore (take (Suc n) S) i \<noteq> []")
   apply(thin_tac "nat_seq 0 nat ! ia = ia")
   apply(thin_tac "ESplitItem_prods (S ! i) \<noteq> []")
   apply (metis liftB_reflects_length teB_nth_liftB DT_two_elements.inject(2))
  apply(rename_tac d y ya)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(subgoal_tac "\<exists>q. [teA (fillOpt (hd (cropTol3l2 (y # restrict_newignore (take (Suc n) S) i))) q)] = [teA y]")
   apply(rename_tac d y ya)(*strict*)
   prefer 2
   apply(case_tac y)
    apply(rename_tac d y ya q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac d ya q ba)(*strict*)
    apply(rule_tac
      x="None"
      in exI)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def fillOpt_def)
   apply(rename_tac d y ya q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ya q1 ba q2)(*strict*)
   apply(rule_tac
      x="Some q2"
      in exI)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def fillOpt_def fill_def)
  apply(rename_tac d y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac d y ya q)(*strict*)
  apply(rule_tac
      x="q"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "((\<exists>b. teB b = restrict_newelem (take (Suc n) S) i) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> restrict_newelem (take (Suc n) S) i)) \<and> ((\<exists>A. teA A = restrict_newelem (take (Suc n) S) i) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S ! i) = [])")
   apply(rename_tac d y ya q)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac d y ya q)(*strict*)
    apply(clarsimp)
    apply(rename_tac d y ya q ba ia)(*strict*)
    apply(simp add: restrict_newelem_def)
    apply(clarsimp)
   apply(rename_tac d y ya q)(*strict*)
   apply(clarsimp)
   apply(rename_tac d y ya q A)(*strict*)
   apply(simp add: restrict_newelem_def)
  apply(rename_tac d y ya q)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(\<exists>b. teB b = restrict_newelem (take (Suc n) S) i) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> restrict_newelem (take (Suc n) S) i)")
  apply(rename_tac d y ya q)(*strict*)
  apply(thin_tac "(\<exists>A. teA A = restrict_newelem (take (Suc n) S) i) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S ! i) = []")
  apply(rename_tac d y ya q)(*strict*)
  apply(thin_tac "(\<exists>b. teB b = ya) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> ya)")
  apply(rename_tac d y ya q)(*strict*)
  apply(thin_tac "(\<exists>A. teA A = ya) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S ! i) = []")
  apply(subgoal_tac "\<exists>c q1 q2 q3. ya # liftA (ESplitItem_to (S ! i)) = fillWithContext (restrict_newelem (take (Suc n) S) i) (restrict_newto (take (Suc n) S) i) c q1 q2 q3 \<and> ValidContext (restrict_newelem (take (Suc n) S) i) (restrict_newto (take (Suc n) S) i) c (restrict_newignore (take (Suc n) S) i) q1 q2 q3")
   apply(rename_tac d y ya q)(*strict*)
   apply(erule exE)+
   apply(rename_tac d y ya q c q1 q2 q3)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule_tac
      x="q1"
      in exI)
   apply(rule_tac
      x="q2"
      in exI)
   apply(rule_tac
      x="q3"
      in exI)
   apply(force)
  apply(rename_tac d y ya q)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA y]\<rparr> (ESplitItem_prods (S ! i)) \<lparr>cfg_conf = ya # liftA (ESplitItem_to (S ! i))\<rparr>")
  apply(rename_tac d y ya q)(*strict*)
  apply(simp add: restrict_newelem_def)
  apply(rename_tac y ya q)(*strict*)
  apply(subgoal_tac "((ESplitItem_to (S ! i) = [] \<longrightarrow> filterA (option_to_list (Some ya)) = [] \<longrightarrow> ESplitItem_ignore (S ! i) \<noteq> []) \<longrightarrow> proper_l3_l2_seq (filterA (option_to_list (Some ya)) @ ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)))")
   apply(rename_tac y ya q)(*strict*)
   prefer 2
   apply(simp add: EValidSplitItem_belongs_def)
  apply(rename_tac y ya q)(*strict*)
  apply(erule impE)
   apply(rename_tac y ya q)(*strict*)
   apply(clarsimp)
   apply(case_tac ya)
    apply(rename_tac y ya q a)(*strict*)
    prefer 2
    apply(rename_tac y ya q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac y q ba)(*strict*)
    apply(simp add: option_to_list_def)
    apply(rule_tac
      S="S!i"
      in EValidSplit_DERIVED_terminal_produce_produces_to)
         apply(rename_tac y q ba)(*strict*)
         apply(force)
        apply(rename_tac y q ba)(*strict*)
        apply(force)
       apply(rename_tac y q ba)(*strict*)
       apply(simp add: EValidSplitItem_gen_def)
      apply(rename_tac y q ba)(*strict*)
      apply(force)
     apply(rename_tac y q ba)(*strict*)
     apply(force)
    apply(rename_tac y q ba)(*strict*)
    apply(force)
   apply(rename_tac y ya q a)(*strict*)
   apply(clarsimp)
   apply(rename_tac y q a)(*strict*)
   apply(case_tac a)
    apply(rename_tac y q a qa ba)(*strict*)
    prefer 2
    apply(rename_tac y q a q1 ba q2)(*strict*)
    apply(rule EValidSplit_DERIVED_l3_produce_produces_to)
          apply(rename_tac y q a q1 ba q2)(*strict*)
          apply(force)
         apply(rename_tac y q a q1 ba q2)(*strict*)
         apply(force)
        apply(rename_tac y q a q1 ba q2)(*strict*)
        apply(force)
       apply(rename_tac y q a q1 ba q2)(*strict*)
       apply(force)
      apply(rename_tac y q a q1 ba q2)(*strict*)
      apply(force)
     apply(rename_tac y q a q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac y q a q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac y q q1 ba q2)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac y q a qa ba)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac y ya q)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "restrict_newignore (take (Suc n) S) i=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac y ya q)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac y ya q)(*strict*)
  apply(erule disjE)
   apply(rename_tac y ya q)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya q)(*strict*)
   apply(subgoal_tac "restrict_newto (take (Suc n) S) i=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac y ya q)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac y ya q)(*strict*)
   apply(erule disjE)
    apply(rename_tac y ya q)(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya q)(*strict*)
    apply(case_tac "i=n")
     apply(rename_tac y ya q)(*strict*)
     apply(clarsimp)
     apply(rename_tac y q)(*strict*)
     apply(simp add: restrict_newto_def restrict_newignore_def)
     apply(simp add: new_post_sig_def)
     apply(subgoal_tac "length(drop_and_crop (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc n))) = SSX " for SSX)
      apply(rename_tac y q)(*strict*)
      prefer 2
      apply(rule drop_and_crop_length)
     apply(rename_tac y q)(*strict*)
     apply(clarsimp)
     apply(thin_tac "drop_and_crop (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc n)) = []")
     apply(rename_tac y q)(*strict*)
     apply(case_tac "ESplitItem_to (S ! n)")
      apply(rename_tac y q)(*strict*)
      apply(clarsimp)
     apply(rename_tac y q a list)(*strict*)
     apply(simp add: restrict_toberemovedX_def)
     apply(subgoal_tac "(restrict_toberemoved (take (Suc n) S) @ [tl (ESplitItem_to (last (take (Suc n) S)) @ ESplitItem_ignore (last (take (Suc n) S)))]) ! Suc n=SSX"  for SSX)
      apply(rename_tac y q a list)(*strict*)
      prefer 2
      apply(rule nth_append_beyond)
      apply(rule_tac
      t="length(restrict_toberemoved (take (Suc n) S))"
      in ssubst)
       apply(rename_tac y q a list)(*strict*)
       apply(rule length_restrict_toberemoved)
       apply(force)
      apply(rename_tac y q a list)(*strict*)
      apply(force)
     apply(rename_tac y q a list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "last (take (Suc n) S) = SSX" for SSX)
      apply(rename_tac y q a list)(*strict*)
      prefer 2
      apply(rule last_take_nth)
      apply(force)
     apply(rename_tac y q a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q)(*strict*)
    apply(subgoal_tac "i<n")
     apply(rename_tac y ya q)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac y ya q)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(rename_tac y ya q)(*strict*)
     apply(force)
    apply(rename_tac y ya q)(*strict*)
    apply(simp add: PValidSplit_interline_def)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(simp add: PValidSplit_interlineX_def)
    apply(simp add: restrict_def restrict_map_def restrict_len_def)
   apply(rename_tac y ya q)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya q w' a')(*strict*)
   apply(subgoal_tac "ESplitItem_ignore (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac y ya q w' a')(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac y ya q w' a')(*strict*)
   apply(erule disjE)
    apply(rename_tac y ya q w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya q w' a')(*strict*)
    apply(subgoal_tac "ESplitItem_to (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac y ya q w' a')(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac y ya q w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac y ya q w' a')(*strict*)
     apply(clarsimp)
     apply(rename_tac y ya q w' a')(*strict*)
     apply(simp add: restrict_newto_def)
    apply(rename_tac y ya q w' a')(*strict*)
    apply(simp add: restrict_newto_def restrict_newignore_def new_post_sig_def)
    apply(clarsimp)
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(subgoal_tac "length(drop_and_crop (w'a @ [a'a]) (length (restrict_toberemovedX (take (Suc n) S) ! (Suc i)))) =SSX" for SSX)
     apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
     prefer 2
     apply(rule drop_and_crop_length)
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(clarsimp)
    apply(simp add: drop_and_crop_def butn_def)
    apply(subgoal_tac "Suc (length w')+length (restrict_toberemovedX (take (Suc n) S) ! (Suc i) ) = Suc (length w'a) ")
     apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(thin_tac "Suc (length w') = Suc (length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))")
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(rule_tac
      x="drop (Suc (length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (w'a@[a'a])"
      in exI)
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(rule_tac
      x="None"
      in exI)
    apply(case_tac "length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))")
     apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
     prefer 2
     apply(rename_tac y ya q w' a' w'a a'a nat)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "take (length w'a - nat) w'a=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac y ya q w' a' w'a a'a nat)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac y ya q w' a' w'a a'a nat)(*strict*)
     apply(erule disjE)
      apply(rename_tac y ya q w' a' w'a a'a nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya q w' a' w'a a'a nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac y ya q w' a' w'a a'a nat w'b a'b)(*strict*)
     apply(case_tac a'b)
      apply(rename_tac y ya q w' a' w'a a'a nat w'b a'b qa ba)(*strict*)
      apply(clarsimp)
      apply(rename_tac y ya q w' a' w'a a'a nat w'b qa ba)(*strict*)
      apply(rule_tac
      w="(case ya of teA A \<Rightarrow> [A] | teB b \<Rightarrow> [])@w'b"
      and q="qa"
      and A="ba"
      and w'="drop((length w'a-nat)) w'a"
      and a="a'a"
      in proper_l3_l2_seq_nol2)
      apply(rule_tac
      t="(((case ya of teA A \<Rightarrow> [A] | teB b \<Rightarrow> []) @ w'b) @ cons_l2 qa ba # drop ((length w'a - nat)) w'a @ [a'a])"
      and s="((case ya of teA A \<Rightarrow> [A] | teB b \<Rightarrow> []) @ w'a @ [a'a])"
      in ssubst)
       apply(rename_tac y ya q w' a' w'a a'a nat w'b qa ba)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac y ya q w' a' w'a a'a nat w'b qa ba)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="w'b @ cons_l2 qa ba # drop (length w'a - nat) w'a"
      and s="take (length w'a - nat) w'a@drop (length w'a - nat) w'a"
      in ssubst)
       apply(rename_tac y ya q w' a' w'a a'a nat w'b qa ba)(*strict*)
       apply(force)
      apply(rename_tac y ya q w' a' w'a a'a nat w'b qa ba)(*strict*)
      apply (metis append_take_drop_id)
     apply(rename_tac y ya q w' a' w'a a'a nat w'b a'b q1 ba q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac y ya q w' a' w'a a'a nat w'b q1 ba q2)(*strict*)
     apply(rule_tac
      x="Some q2"
      in exI)
     apply(rule_tac
      x="None"
      in exI)
     apply(case_tac a'a)
      apply(rename_tac y ya q w' a' w'a a'a nat w'b q1 ba q2 qa baa)(*strict*)
      prefer 2
      apply(rename_tac y ya q w' a' w'a a'a nat w'b q1 ba q2 q1a baa q2a)(*strict*)
      apply(simp add: proper_l3_l2_seq_def)
     apply(rename_tac y ya q w' a' w'a a'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(clarsimp)
     apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(rule conjI)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(simp add: fillWithContext_def)
      apply(rule conjI)
       apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
       apply(simp add: fillBOpt_def)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(simp add: fillOptL_def)
      apply(rule_tac
      t="w'a @ [cons_l2 qa baa]"
      and s="fillL (w' @ [a']) q2@drop (length w'a - nat) w'a @ [cons_l2 qa baa]"
      in ssubst)
       apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
       prefer 2
       apply(simp add: liftA_commutes_over_concat)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(clarsimp)
      apply(simp add: cropTol3l2_def cropTol3l2_single_def fill_def fillL_def appL_def)
      apply(clarsimp)
      apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa)(*strict*)
      apply(rule_tac
      t="w' @ cons_l3 q1 ba q2 # drop (length w'a - nat) w'a"
      and s="take (length w'a - nat) w'a@drop (length w'a - nat) w'a"
      in subst)
       apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa)(*strict*)
       apply(force)
      apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa)(*strict*)
      apply (metis append_take_drop_id)
     apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(simp add: ValidContext_def)
     apply(rule conjI)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(simp add: event_stack_separation_and_proper_l3_l2_seq_def fillWithContext_def)
      apply(simp add: cropTol3l2_def cropTol3l2_single_def fill_def fillL_def appL_def)
      apply(clarsimp)
      apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa)(*strict*)
      apply(simp add: fillOptL_def)
      apply(simp add: fillBOpt_def cropTol3l2_def cropTol3l2_single_def fill_def fillL_def appL_def)
      apply(case_tac ya)
       apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa a)(*strict*)
       apply(clarsimp)
       apply(rename_tac y q w' w'a nat q1 ba q2 qa baa a)(*strict*)
       apply(rule_tac
      x="[]"
      in exI)
       apply(rule_tac
      x="[]"
      in exI)
       apply(rule_tac
      x="a#w'@[cons_l3 q1 ba q2]@drop (length w'a - nat) w'a @ [cons_l2 qa baa]"
      in exI)
       apply(clarsimp)
       apply(simp add: liftA_commutes_over_concat)
       apply(rule_tac
      t="a # w' @ cons_l3 q1 ba q2 # drop (length w'a - nat) w'a @ [cons_l2 qa baa]"
      and s="a # w'a @ [cons_l2 qa baa]"
      in ssubst)
        apply(rename_tac y q w' w'a nat q1 ba q2 qa baa a)(*strict*)
        apply(rule_tac
      P="\<lambda>X. a # w' @ cons_l3 q1 ba q2 # drop (length w'a - nat) w'a @ [cons_l2 qa baa] = a # X @ [cons_l2 qa baa]"
      and s="take (length w'a - nat) w'a @ drop (length w'a - nat) w'a"
      in ssubst)
         apply(rename_tac y q w' w'a nat q1 ba q2 qa baa a)(*strict*)
         apply (metis append_take_drop_id)
        apply(rename_tac y q w' w'a nat q1 ba q2 qa baa a)(*strict*)
        apply(force)
       apply(rename_tac y q w' w'a nat q1 ba q2 qa baa a)(*strict*)
       apply(force)
      apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
      apply(rule_tac
      x="[]"
      in exI)
      apply(rule_tac
      x="[bb]"
      in exI)
      apply(rule_tac
      x="w'@[cons_l3 q1 ba q2]@drop (length w'a - nat) w'a @ [cons_l2 qa baa]"
      in exI)
      apply(clarsimp)
      apply(simp add: liftA_commutes_over_concat)
      apply(rule_tac
      t="w' @ cons_l3 q1 ba q2 # drop (length w'a - nat) w'a @ [cons_l2 qa baa]"
      and s="w'a @ [cons_l2 qa baa]"
      in ssubst)
       apply(rename_tac y q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
       apply(rule_tac
      P="\<lambda>X. w' @ cons_l3 q1 ba q2 # drop (length w'a - nat) w'a @ [cons_l2 qa baa] = X @ [cons_l2 qa baa]"
      and s="take (length w'a - nat) w'a @ drop (length w'a - nat) w'a"
      in ssubst)
        apply(rename_tac y q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
        apply (metis append_take_drop_id)
       apply(rename_tac y q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
       apply(force)
      apply(rename_tac y q w' w'a nat q1 ba q2 qa baa bb)(*strict*)
      apply(force)
     apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(rule conjI)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(simp add: ValidFillBO_def ValidFillO_def)
      apply(case_tac ya)
       apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa a)(*strict*)
       apply(clarsimp)
       apply(rename_tac y q w' a' w'a nat w'b q1 ba q2 qa baa a)(*strict*)
       apply(case_tac a)
        apply(rename_tac y q w' a' w'a nat w'b q1 ba q2 qa baa a qb bb)(*strict*)
        apply(clarsimp)
        apply(rename_tac y q w' a' w'a nat w'b q1 ba q2 qa baa qb bb)(*strict*)
        apply(simp add: ValidFillO_def)
       apply(rename_tac y q w' a' w'a nat w'b q1 ba q2 qa baa a q1a bb q2a)(*strict*)
       apply(clarsimp)
       apply(rename_tac y q w' a' w'a nat w'b q1 ba q2 qa baa q1a bb q2a)(*strict*)
       apply(simp add: ValidFillO_def)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa bb)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(rule conjI)
      apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
      apply(simp add: ValidFillOL_def)
      apply(simp add: cropTol3l2_def cropTol3l2_single_def fillOpt_def)
      apply(clarsimp)
      apply(rename_tac y ya q w' w'a nat q1 ba q2 qa baa)(*strict*)
      apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
      apply(clarsimp)
      apply(erule_tac
      x="w'"
      in allE)
      apply(force)
     apply(rename_tac y ya q w' a' w'a nat w'b q1 ba q2 qa baa)(*strict*)
     apply(simp add: ValidFillOL_def)
    apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def fillOpt_def)
    apply(clarsimp)
    apply(rename_tac y ya q w' a'a)(*strict*)
    apply(case_tac a'a)
     apply(rename_tac y ya q w' a'a qa ba)(*strict*)
     prefer 2
     apply(rename_tac y ya q w' a'a q1 ba q2)(*strict*)
     apply(simp add: proper_l3_l2_seq_def)
    apply(rename_tac y ya q w' a'a qa ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya q w' qa ba)(*strict*)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule conjI)
     apply(rename_tac y ya q w' qa ba)(*strict*)
     apply(simp add: fillWithContext_def fillOptL_def fillBOpt_def)
    apply(rename_tac y ya q w' qa ba)(*strict*)
    apply(simp add: ValidContext_def)
    apply(simp add: fillWithContext_def fillOptL_def fillBOpt_def)
    apply(rule conjI)
     apply(rename_tac y ya q w' qa ba)(*strict*)
     apply(simp add: event_stack_separation_and_proper_l3_l2_seq_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(case_tac ya)
      apply(rename_tac y ya q w' qa ba a)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' qa ba a)(*strict*)
      apply(rule_tac
      x="[]"
      in exI)
      apply(rule_tac
      x="a#w'@[cons_l2 qa ba]"
      in exI)
      apply(simp add: liftA_commutes_over_concat)
     apply(rename_tac y ya q w' qa ba baa)(*strict*)
     apply(rule_tac
      x="[baa]"
      in exI)
     apply(rule_tac
      x="w'@[cons_l2 qa ba]"
      in exI)
     apply(simp add: liftA_commutes_over_concat)
    apply(rename_tac y ya q w' qa ba)(*strict*)
    apply(rule conjI)
     apply(rename_tac y ya q w' qa ba)(*strict*)
     apply(simp add: ValidFillBO_def ValidFillO_def ValidFillOL_def)
     apply(case_tac ya)
      apply(rename_tac y ya q w' qa ba a)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' qa ba a)(*strict*)
      apply(case_tac a)
       apply(rename_tac y q w' qa ba a qb baa)(*strict*)
       apply(clarsimp)
       apply(rename_tac y q w' qa ba qb baa)(*strict*)
       apply(simp add: ValidFillO_def)
      apply(rename_tac y q w' qa ba a q1 baa q2)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' qa ba q1 baa q2)(*strict*)
      apply(simp add: ValidFillO_def)
     apply(rename_tac y ya q w' qa ba baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q w' qa ba)(*strict*)
    apply(rule conjI)
     apply(rename_tac y ya q w' qa ba)(*strict*)
     apply(simp add: ValidFillBO_def ValidFillOL_def)
    apply(rename_tac y ya q w' qa ba)(*strict*)
    apply(simp add: ValidFillBO_def ValidFillOL_def)
   apply(rename_tac y ya q w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
   apply(case_tac a'a)
    apply(rename_tac y ya q w' a' w'a a'a qa ba)(*strict*)
    prefer 2
    apply(rename_tac y ya q w' a' w'a a'a q1 ba q2)(*strict*)
    apply(simp add: proper_l3_l2_seq_def)
   apply(rename_tac y ya q w' a' w'a a'a qa ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(simp add: restrict_newto_def new_post_sig_def restrict_newignore_def)
   apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = SSX " for SSX)
    apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
    prefer 2
    apply(rule drop_and_crop_length)
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "Suc (length w')+length (restrict_toberemovedX (take (Suc n) S) ! Suc i) = Suc (length (ESplitItem_to (S ! i)) + length w'a) ")
    apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(thin_tac "Suc (length w') = Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "Suc (length (ESplitItem_to (S ! i)) + length w'a) \<le> length (ESplitItem_to (S ! i))+ length (restrict_toberemovedX (take (Suc n) S) ! Suc i)")
    apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(thin_tac "Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i) \<le> length (ESplitItem_to (S ! i))")
   apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
   apply(clarsimp)
   apply(simp add: drop_and_crop_def butn_def)
   apply(case_tac a')
    apply(rename_tac y ya q w' a' w'a qa ba qb baa)(*strict*)
    prefer 2
    apply(rename_tac y ya q w' a' w'a qa ba q1 baa q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya q w' w'a qa ba q1 baa q2)(*strict*)
    apply(simp add: cropTol3l2_def)
    apply(case_tac "ESplitItem_to (S ! i) = []")
     apply(rename_tac y ya q w' w'a qa ba q1 baa q2)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q w' w'a qa ba q1 baa q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya q w'a qa ba q1 baa q2)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def fillOpt_def)
    apply(case_tac "last (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))")
     apply(rename_tac y ya q w'a qa ba q1 baa q2 qb bb)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q w'a qa ba q1 baa q2 q1a bb q2a)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya q w' a' w'a qa ba qb baa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
   apply(rule_tac
      x="drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i))"
      in exI)
   apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="last_back_state(take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i)))"
      in exI)
   apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule conjI)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(simp add: fillWithContext_def fillOptL_def)
    apply(rule conjI)
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(simp add: fillBOpt_def)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(case_tac "last_back_state (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i)))")
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "False")
      apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
      apply(force)
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(subgoal_tac "(take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i)))= []")
      apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(rule last_back_state_empty)
     apply(force)
    apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="fillL (w' @ [cons_l2 qb baa]) a"
      and s="take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i))"
      in ssubst)
     apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
     prefer 2
     apply(rule_tac
      t="liftA (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! (Suc i))) (ESplitItem_to (S ! i))) @ liftA (drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))"
      and s="liftA((take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))) @ (drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))))"
      in ssubst)
      apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
      apply(simp only: liftA_commutes_over_concat)
     apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
     apply(rule_tac
      f="liftA"
      in arg_cong)
     apply (metis append_take_drop_id)
    apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
    apply(rule_tac
      t="w'@[cons_l2 qb baa]"
      and s="cropTol3l2 (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))"
      in ssubst)
     apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
     apply(force)
    apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
    apply(rule append_last_back_state_for_proper_l3_seq)
     apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
     apply(force)
    apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
    apply(rule proper_l3_seq_take)
    apply(rule proper_l3_l2_seq_proper_l3_seq_slice)
    apply(force)
   apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
   apply(simp add: ValidContext_def)
   apply(rule conjI)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(simp add: ValidFillBO_def)
     apply(case_tac ya)
      apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
      apply(case_tac a)
       apply(rename_tac y q w' w'a qa ba qb baa a qc bb)(*strict*)
       apply(clarsimp)
       apply(rename_tac y q w' w'a qa ba qb baa qc bb)(*strict*)
       apply(simp add: ValidFillO_def)
      apply(rename_tac y q w' w'a qa ba qb baa a q1 bb q2)(*strict*)
      apply(clarsimp)
      apply(rename_tac y q w' w'a qa ba qb baa q1 bb q2)(*strict*)
      apply(simp add: ValidFillO_def)
     apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(rule conjI)
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(simp add: ValidFillOL_def)
     apply(clarsimp)
     apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
     apply(clarsimp)
     apply(erule_tac
      x="w'"
      in allE)
     apply(force)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(simp add: ValidFillOL_def)
   apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
   apply(rule_tac
      x="w'a @ [cons_l2 qa ba]"
      in exI)
   apply(simp add: fillWithContext_def fillBOpt_def fillOptL_def)
   apply(case_tac "last_back_state (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))")
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(force)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(subgoal_tac "(take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))= []")
     apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
    apply(rule last_back_state_empty)
    apply(force)
   apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="fillL (w' @ [cons_l2 qb baa]) a"
      and s="take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))"
      in ssubst)
    apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
    prefer 2
    apply(rule_tac
      t="liftA (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))) @ liftA (drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))) @ liftA (w'a @ [cons_l2 qa ba])"
      and s="liftA((take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i))) @ (drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))@w'a @ [cons_l2 qa ba])"
      in ssubst)
   apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
   apply(simp only: liftA_commutes_over_concat)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(rule_tac
    t="take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)) @ drop (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)) @ w'a @ [cons_l2 qa ba]"
    and s=" (ESplitItem_to (S ! i)) @ w'a @ [cons_l2 qa ba]"
    in ssubst)
   apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_def)
  apply(case_tac ya)
   apply(rename_tac y ya q w' w'a qa ba qb baa a aa)(*strict*)
   apply(rule_tac
    x="[]"
    in exI)
   apply(rule_tac
    x="aa#ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]"
    in exI)
   apply(clarsimp)
  apply(rename_tac y ya q w' w'a qa ba qb baa a bb)(*strict*)
  apply(rule_tac
    x="[bb]"
    in exI)
  apply(rule_tac
    x="ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]"
    in exI)
  apply(clarsimp)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(rule_tac
    t="w'@[cons_l2 qb baa]"
    and s="cropTol3l2 (take (Suc (length (ESplitItem_to (S ! i)) + length w'a) - length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) (ESplitItem_to (S ! i)))"
    in ssubst)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(rule append_last_back_state_for_proper_l3_seq)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(rule proper_l3_seq_take)
  apply(rule proper_l3_l2_seq_proper_l3_seq_slice)
  apply(force)
  apply(rename_tac y ya q)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a')(*strict*)
  apply(subgoal_tac "ESplitItem_ignore (S ! i)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
  apply(rename_tac y ya q w' a')(*strict*)
  prefer 2
  apply(rule case_list)
  apply(rename_tac y ya q w' a')(*strict*)
  apply(erule disjE)
  apply(rename_tac y ya q w' a')(*strict*)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! i)) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))=SSX" for SSX)
  apply(rename_tac y ya q w' a')(*strict*)
  prefer 2
  apply(rule drop_and_crop_length)
  apply(rename_tac y ya q w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a' w'a a'a)(*strict*)
  apply(case_tac a'a)
  apply(rename_tac y ya q w' a' w'a a'a qa ba)(*strict*)
  prefer 2
  apply(rename_tac y ya q w' a' w'a a'a q1 ba q2)(*strict*)
  apply(simp add: proper_l3_l2_seq_def)
  apply(rename_tac y ya q w' a' w'a a'a qa ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = SSX" for SSX)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule drop_and_crop_length)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(rule_tac
    x="None"
    in exI)
  apply(rule_tac
    x="None"
    in exI)
  apply(rule_tac
    x="None"
    in exI)
  apply(rule conjI)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: fillWithContext_def fillBOpt_def fillOptL_def)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(rule take_unchanged_prefix_of_drop_and_crop)
  apply(clarsimp)
  apply(subgoal_tac "length SSw - SSn = length SSv" for SSw SSn SSv)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule_tac
    v="w' @ [a']"
    and n="length(ESplitItem_to (S ! i))"
    and w="(drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
    in drop_length_prime)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: ValidContext_def)
  apply(rule conjI)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule conjI)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: ValidFillBO_def)
  apply(case_tac ya)
   apply(rename_tac y ya q w' a' w'a qa ba a)(*strict*)
   apply(clarsimp)
   apply(rename_tac y q w' a' w'a qa ba a)(*strict*)
   apply(case_tac a)
    apply(rename_tac y q w' a' w'a qa ba a qb baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac y q w' a' w'a qa ba qb baa)(*strict*)
    apply(simp add: ValidFillO_def)
   apply(rename_tac y q w' a' w'a qa ba a q1 baa q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac y q w' a' w'a qa ba q1 baa q2)(*strict*)
   apply(simp add: ValidFillO_def)
  apply(rename_tac y ya q w' a' w'a qa ba baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(rule conjI)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(simp add: ValidFillOL_def)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: ValidFillOL_def)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: fillWithContext_def fillBOpt_def fillOptL_def)
  apply(rule_tac
    t="take (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
    and s="ESplitItem_to (S ! i)"
    in subst)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(rule take_unchanged_prefix_of_drop_and_crop)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = SSX" for SSX)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule drop_and_crop_length)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(simp add: fillWithContext_def fillBOpt_def fillOptL_def)
  apply(subgoal_tac "length SSw - SSn = length SSv" for SSw SSn SSv)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule_tac
    v="w' @ [a']"
    and n="length(ESplitItem_to (S ! i))"
    and w="(drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))"
    in drop_length_prime)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(subgoal_tac "drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i))) = (drop_and_crop (w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))")
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  prefer 2
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac y ya q w' a' w'a qa ba)(*strict*)
  apply(clarsimp)
  apply(case_tac a')
  apply(rename_tac y ya q w' a' w'a qa ba qb baa)(*strict*)
  prefer 2
  apply(rename_tac y ya q w' a' w'a qa ba q1 baa q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' w'a qa ba q1 baa q2)(*strict*)
  apply(thin_tac "fillOpt (hd (cropTol3l2 (y # w' @ [cons_l3 q1 baa q2]))) q = y")
  apply(simp add: drop_and_crop_def cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac y ya w' w'a qa ba q1 baa q2)(*strict*)
  apply(case_tac "butn (w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)) = []")
  apply(rename_tac y ya w' w'a qa ba q1 baa q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya w' w'a qa ba q1 baa q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya w'a qa ba q1 baa q2)(*strict*)
  apply(simp add: drop_and_crop_def cropTol3l2_def cropTol3l2_single_def)
  apply(case_tac "last (butn (w'a @ [cons_l2 qa ba]) (length (restrict_toberemovedX (take (Suc n) S) ! Suc i)))")
  apply(rename_tac y ya w'a qa ba q1 baa q2 q bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya w'a qa ba q1 baa q2 q1a bb q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' a' w'a qa ba qb baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya q w' w'a qa ba qb baa)(*strict*)
  apply(simp add: event_stack_separation_and_proper_l3_l2_seq_def)
  apply(case_tac ya)
  apply(rename_tac y ya q w' w'a qa ba qb baa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(rule_tac
    x="a#ESplitItem_to (S ! i)@w'@[cons_l2 qb baa]"
    in exI)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "proper_l3_l2_seq (SSw1 @ SSw3 @ [cons_l2 SSq2 SSA2])" for SSw1 SSw3 SSq2 SSA2)
  apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
  prefer 2
  apply(rule_tac
    ?w1.0="a # ESplitItem_to (S ! i)"
    in proper_l3_l2_seq_preserved_by_drop_and_crop)
   apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
   apply(force)
  apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
  apply(force)
  apply(rename_tac y q w' w'a qa ba qb baa a)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
  apply(rule_tac
    x="[bb]"
    in exI)
  apply(rule_tac
    x="ESplitItem_to (S ! i)@w'@[cons_l2 qb baa]"
    in exI)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "proper_l3_l2_seq (SSw1 @ SSw3 @ [cons_l2 SSq2 SSA2])" for SSw1 SSw3 SSq2 SSA2)
  apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
  prefer 2
  apply(rule_tac
    ?w1.0="ESplitItem_to (S ! i)"
    in proper_l3_l2_seq_preserved_by_drop_and_crop)
  apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
  apply(force)
  apply(rename_tac y ya q w' w'a qa ba qb baa bb)(*strict*)
  apply(force)
  done

lemma restrict_PValidSplit_ValidItem: "
  F2LR1inputx G G'
  \<Longrightarrow> Suc n < length S
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> n < length (Esplit_signature S)
  \<Longrightarrow> length (Esplit_signature S) \<le> length S
  \<Longrightarrow> PValidSplit_interline (restrict G' G S (Suc n))
  \<Longrightarrow> length (restrict G' G S (Suc n)) = Suc n
  \<Longrightarrow> EValidSplit_interline S
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> EValidSplit_initial G S
  \<Longrightarrow> EValidSplit_to_empty G S
  \<Longrightarrow> EValidSplit_final G S
  \<Longrightarrow> EValidSplit_producing G S
  \<Longrightarrow> EValidSplit_produce_or_elim G S
  \<Longrightarrow> EValidSplit_ValidItem G S
  \<Longrightarrow> PValidSplit_ValidItem G' G (restrict G' G S (Suc n))"
  apply(simp add: PValidSplit_ValidItem_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: PValidSplitItem_def)
  apply(case_tac "ESplitItem_from (S ! n)")
   apply(rename_tac i)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!n"
      in ballE)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "S!n \<in> set(butlast S)")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac i)(*strict*)
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i w' a')(*strict*)
   apply(subgoal_tac "(w' @ [a']) ! n = SSX" for SSX)
    apply(rename_tac i w' a')(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i w' a')(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(subgoal_tac "ESplitItem_to (S!n) \<noteq> []")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(case_tac "ESplitItem_to (S!n) = []")
    apply(rename_tac i a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(clarsimp)
   apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
        apply(rename_tac i a)(*strict*)
        apply(force)
       apply(rename_tac i a)(*strict*)
       apply(force)
      apply(rename_tac i a)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac i a)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
   apply(rename_tac i a)(*strict*)
   apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac i a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac i a)(*strict*)
   apply(rule restrict_PValidSplit_belongs)
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
  apply(rename_tac i a)(*strict*)
  apply(rule conjI)
   apply(rename_tac i a)(*strict*)
   apply(rule restrict_PValidSplit_elim)
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
  apply(rule restrict_PValidSplit_gen)
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
  apply(rename_tac i a)(*strict*)
  apply(force)
  done

theorem restrict_preserves_ValidSplit: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G S
  \<Longrightarrow> Suc n<length S
  \<Longrightarrow> S'=restrict G' G S (Suc n)
  \<Longrightarrow> ESplitItem_elem (S ! n) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S'"
  apply(subgoal_tac "n<(length(Esplit_signature S))")
   prefer 2
   apply(subgoal_tac "length(Esplit_signature S)\<le>length S")
    prefer 2
    apply(rule Esplit_signature_length_max)
   apply(clarsimp)
   apply(subgoal_tac " length SSS = length (Esplit_signature SSS) \<or> length SSS = Suc (length (Esplit_signature SSS)) \<and> SSS' = []" for SSS SSS')
    prefer 2
    apply(rule_tac
      S'="[]"
      in EValidSplit_Esplit_signature_length)
    apply(force)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(subgoal_tac "length (Esplit_signature S) \<le> length S")
   prefer 2
   apply(rule Esplit_signature_length_max)
  apply(subgoal_tac "n<length S")
   prefer 2
   apply(force)
  apply(subgoal_tac "length S'=Suc n")
   prefer 2
   apply(clarsimp)
   apply(rule length_of_restrict)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: PValidSplit_def EValidSplit_def)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S ! n)")
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="S!n"
      in ballE)
    apply(force)
   apply(subgoal_tac "S!n \<in> set(butlast S)")
    apply(force)
   apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(erule disjE)
    apply(force)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(subgoal_tac "(w' @ [a']) ! n = SSX" for SSX)
    apply(rename_tac w' a')(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "ESplitItem_to (S!n) \<noteq> []")
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(case_tac "ESplitItem_to (S!n) = []")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac a)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
   apply(rename_tac a)(*strict*)
   apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
  apply(rename_tac a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac a)(*strict*)
   apply(rule restrict_PValidSplit_interline)
                apply(rename_tac a)(*strict*)
                apply(force)
               apply(rename_tac a)(*strict*)
               apply(force)
              apply(rename_tac a)(*strict*)
              apply(force)
             apply(rename_tac a)(*strict*)
             apply(force)
            apply(rename_tac a)(*strict*)
            apply(force)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule restrict_PValidSplit_notEmpty)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule restrict_PValidSplit_initial)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule restrict_PValidSplit_to_empty)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule restrict_PValidSplit_final)
                 apply(rename_tac a)(*strict*)
                 apply(rule F2LR1input_implies_split_TSstructure)
                 apply(simp add: F2LR1input_def)
                 apply(force)
                apply(rename_tac a)(*strict*)
                apply(force)
               apply(rename_tac a)(*strict*)
               apply(force)
              apply(rename_tac a)(*strict*)
              apply(force)
             apply(rename_tac a)(*strict*)
             apply(force)
            apply(rename_tac a)(*strict*)
            apply(force)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule restrict_PValidSplit_ValidItem)
                 apply(rename_tac a)(*strict*)
                 apply(force)
                apply(rename_tac a)(*strict*)
                apply(force)
               apply(rename_tac a)(*strict*)
               apply(rule F2LR1input_implies_split_TSstructure)
               apply(simp add: F2LR1input_def)
               apply(force)
              apply(rename_tac a)(*strict*)
              apply(force)
             apply(rename_tac a)(*strict*)
             apply(force)
            apply(rename_tac a)(*strict*)
            apply(force)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

theorem equal_split_prefix_hlp3: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf = v @ [teB b] @ x1\<rparr>)
  \<Longrightarrow> EValidSplit G (S1 @ S1')
  \<Longrightarrow> length S1 = length (v @ [teB b])
  \<Longrightarrow> v @ [teB b] = Esplit_signature S1
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> S1R = restrict G' G (S1 @ S1') (length (v @ [teB b]))
  \<Longrightarrow> ESplitItem_elem ((S1 @ S1') ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S1R"
  apply(clarsimp)
  apply(rule_tac
      n="length v"
      and S="(S1 @ S1')"
      in restrict_preserves_ValidSplit)
       apply(force)
      apply(force)
     prefer 2
     apply(rule_tac
      t="Esplit_signature S1"
      and s="v @ [teB b]"
      in ssubst)
      apply(force)
     apply(simp (no_asm))
     apply(simp add: Esplit_signature_def)
     apply(case_tac S1')
      prefer 2
      apply(rename_tac a list)(*strict*)
      apply(rule_tac
      t="foldl (@) [] (map (option_to_list \<circ> ESplitItem_elem) S1)"
      and s="v @ [teB b]"
      in ssubst)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(simp (no_asm))
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "False")
      apply(force)
     apply(simp add: EValidSplit_def)
     apply(clarsimp)
     apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      prefer 2
      apply(rule case_list)
     apply(erule disjE)
      apply(clarsimp)
     apply(clarsimp)
     apply(rename_tac w' a')(*strict*)
     apply(simp add: EValidSplit_final_def)
     apply(clarsimp)
     apply(simp add: EValidSplit_produce_or_elim_def)
     apply(clarsimp)
     apply(case_tac a')
     apply(rename_tac w' a' ESplitItem_elima ESplitItem_froma ESplitItem_ignorea ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema ESplitItem_toa)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema)(*strict*)
     apply(case_tac ESplitItem_elema)
      apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema)(*strict*)
      apply(clarsimp)
      apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods)(*strict*)
      apply(simp add: option_to_list_def)
      apply(subgoal_tac "False")
       apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods)(*strict*)
       apply(force)
      apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods)(*strict*)
      apply (metis Esplit_signature_def Esplit_signature_length_max Suc_n_not_le_n length_Suc map_map)
     apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods ESplitItem_elema a)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
     apply(simp add: option_to_list_def)
     apply(clarsimp)
     apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods)(*strict*)
     apply(case_tac ESplitItem_froma)
      apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods)(*strict*)
      apply(clarsimp)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods)(*strict*)
      apply(simp add: EValidSplit_to_empty_def)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prodsa)(*strict*)
      apply(simp add: EValidSplit_ValidItem_def)
      apply(clarsimp)
      apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prodsa ESplitItem_prodsa)(*strict*)
      apply(clarsimp)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prodsa ESplitItem_prodsa d)(*strict*)
      apply(simp add: option_to_list_def)
      apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
       apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prodsa ESplitItem_prodsa d)(*strict*)
       prefer 2
       apply(rule_tac cfgLM_trans_der_from_empty)
       apply(force)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prodsa ESplitItem_prodsa d)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' ESplitItem_elima ESplitItem_froma ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
     apply(simp add: EValidSplit_ValidItem_def EValidSplitItem_def)
     apply(clarsimp)
     apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
          apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
          apply(force)
         apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
         apply(force)
        apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
        apply(force)
       apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
       apply(force)
      apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
      apply(force)
     apply(rename_tac w' ESplitItem_elima ESplitItem_elim_prods ESplitItem_prods a)(*strict*)
     apply(force)
    apply(force)
   apply(rule_tac
      t="length (Esplit_signature S1)"
      and s="Suc (length v)"
      in ssubst)
    prefer 2
    apply(force)
   apply(rule_tac
      t="Esplit_signature S1"
      and s="v @ [teB b]"
      in ssubst)
    apply(force)
   apply(simp (no_asm))
  apply(force)
  done

lemma PValidSplit_construct_derivation1: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S @ S')
  \<Longrightarrow> length S = Suc (length v)
  \<Longrightarrow> v @ [teB b] = Esplit_signature S
  \<Longrightarrow> ESplitItem_elem ((S @ S') ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G (restrict G' G (S @ S') (Suc (length v)))
  \<Longrightarrow> length (Esplit_signature S) = Suc (length v)
  \<Longrightarrow> length (nat_seq 0 (length v)) = Suc (length v)
  \<Longrightarrow> n<Suc(length v)
  \<Longrightarrow> cfgLM.trans_der_list G ds
  (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (Esplit_signature S)) \<pi>s
  (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)
  \<Longrightarrow> \<exists>\<pi> d q1 q2 c.
  let SRn = restrict G' G (S @ S') (Suc (length v)) ! n in
  ValidPreContext (PSplitItem_from SRn) (PSplitItem_ignore SRn) q1 q2
  \<and> cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (PSplitItem_elim SRn @ fillWithPreContext (PSplitItem_from SRn) (PSplitItem_ignore SRn) q1 q2 @ c)\<rparr>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n"
      in EValidSplit_construct_derivation)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi> d)(*strict*)
  apply(simp add: Let_def)
  apply(rule_tac
      x="\<pi>"
      in exI)
  apply(rule_tac
      x="d"
      in exI)
  apply(subgoal_tac "\<exists>q1 q2. ValidPreContext (PSplitItem_from (restrict G' G (S @ S') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S @ S') (Suc (length v)) ! n)) q1 q2 \<and> (\<exists>c. \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (ESplitItem_elim (S ! n) @ option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr>= \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (PSplitItem_elim (restrict G' G (S @ S') (Suc (length v)) ! n) @ fillWithPreContext (PSplitItem_from (restrict G' G (S @ S') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S @ S') (Suc (length v)) ! n)) q1 q2 @ c)\<rparr>)")
   apply(rename_tac \<pi> d)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi> d q1 q2 c)(*strict*)
   apply(rule_tac
      x="q1"
      in exI)
   apply(rule_tac
      x="q2"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi> d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (ESplitItem_elim (S ! n) @ option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n))\<rparr>")
  apply(rename_tac \<pi> d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>q1 q2. ValidPreContext (PSplitItem_from (restrict G' G (S @ S') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S @ S') (Suc (length v)) ! n)) q1 q2 \<and> (\<exists>c. (option_to_list (ESplitItem_from (S ! n)) @ ESplitItem_ignore (S ! n)) = (fillWithPreContext (PSplitItem_from (restrict G' G (S @ S') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S @ S') (Suc (length v)) ! n)) q1 q2 @ c))")
   apply(clarsimp)
   apply(rename_tac q1 q2 c)(*strict*)
   apply(rule_tac
      x="q1"
      in exI)
   apply(rule_tac
      x="q2"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule_tac
      f="liftA"
      in arg_cong)
   apply(clarsimp)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length v) ! n = SSX" for SSX)
    apply(rename_tac q1 q2 c)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac q1 q2 c)(*strict*)
     apply(force)
    apply(rename_tac q1 q2 c)(*strict*)
    apply(force)
   apply(rename_tac q1 q2 c)(*strict*)
   apply(clarsimp)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length v) ! n = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S ! n)")
   apply(subgoal_tac "False")
    apply(force)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(case_tac "n=length v")
    prefer 2
    apply(erule_tac
      x="S!n"
      in ballE)
     apply(clarsimp)
    apply(subgoal_tac "S ! n \<in> set (butlast (S @ S'))")
     apply(force)
    apply(thin_tac "S ! n \<notin> set (butlast (S @ S'))")
    apply(subgoal_tac "n<length v")
     prefer 2
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "S'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
     apply(subgoal_tac "S=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      prefer 2
      apply(rule case_list)
     apply(erule disjE)
      apply(clarsimp)
     apply(clarsimp)
     apply(rename_tac w' a')(*strict*)
     apply(subgoal_tac "(w' @ [a']) ! n = w'!n")
      apply(rename_tac w' a')(*strict*)
      prefer 2
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac w' a')(*strict*)
     apply(force)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(rule_tac
      t="butlast (S @ w' @ [a'])"
      in ssubst)
     apply(rename_tac w' a')(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "(S@S')!length v=S!length v")
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(clarsimp)
   apply(simp add: EValidSplit_ValidItem_def)
   apply(erule_tac
      x="S!length v"
      and P="\<lambda>X. EValidSplitItem G X"
      in ballE)
    apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(simp add: option_to_list_def)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac d)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "restrict_newignore S n=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "EValidSplitItem_belongs G (S ! n)")
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      x="S ! n"
      in ballE)
    apply(rename_tac a)(*strict*)
    apply(simp add: EValidSplitItem_def)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
    apply(rename_tac a q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac q ba)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def option_to_list_def fillWithPreContext_def ValidPreContext_def fillOptL_def fillL_def ValidFillO_def ValidFillOL_def)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule_tac
      x="None"
      in exI)
    apply(clarsimp)
    apply(simp add: fillOpt_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule proper_l3_l2_seqI)
   apply(rename_tac a q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 ba q2)(*strict*)
   apply(rule_tac
      x="Some q2"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! n) @ option_to_list (Some (cons_l3 q1 ba q2)) @ ESplitItem_ignore (S ! n))")
    apply(rename_tac q1 ba q2)(*strict*)
    prefer 2
    apply(simp add: EValidSplitItem_belongs_def)
   apply(rename_tac q1 ba q2)(*strict*)
   apply(subgoal_tac "ESplitItem_ignore (S ! n)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac q1 ba q2)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac q1 ba q2)(*strict*)
   apply(erule disjE)
    apply(rename_tac q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(simp add: fillOpt_def cropTol3l2_def cropTol3l2_single_def option_to_list_def fillWithPreContext_def ValidPreContext_def fillOptL_def fillL_def ValidFillO_def ValidFillOL_def fill_def)
    apply(rule_tac
      x="[cons_l2 q2 ba]"
      in exI)
    apply(rule proper_l3_l2_seqI2)
   apply(rename_tac q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 ba q2 w' a')(*strict*)
   apply(simp add: fillOpt_def cropTol3l2_def cropTol3l2_single_def option_to_list_def fillWithPreContext_def ValidPreContext_def fillOptL_def fillL_def ValidFillO_def ValidFillOL_def fill_def)
   apply(rule_tac
      x="[cons_l2 q2 ba]"
      in exI)
   apply(rule proper_l3_l2_seqI2)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w' a')(*strict*)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def option_to_list_def)
  apply(subgoal_tac "proper_l3_l2_seq (ESplitItem_elim (S ! n) @ option_to_list (Some a) @ ESplitItem_ignore (S ! n))")
   apply(rename_tac a w' a')(*strict*)
   prefer 2
   apply(simp add: EValidSplitItem_belongs_def)
  apply(rename_tac a w' a')(*strict*)
  apply(subgoal_tac "ESplitItem_ignore (S ! n)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac a w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac a w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac a w' a')(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_newignore_def new_post_sig_def)
   apply(subgoal_tac "False")
    apply(rename_tac a w' a')(*strict*)
    apply(force)
   apply(rename_tac a w' a')(*strict*)
   apply(subgoal_tac "drop (length (ESplitItem_to (S ! n))) (drop_and_crop (ESplitItem_to (S ! n)) (length (restrict_toberemovedX S ! Suc n))) = []")
    apply(rename_tac a w' a')(*strict*)
    apply(force)
   apply(rename_tac a w' a')(*strict*)
   apply(rule drop_drop_and_crop_empty)
   apply(force)
  apply(rename_tac a w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac a w' a' w'a a'a)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w' a' w'a a'a q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a' w'a a'a q ba)(*strict*)
   apply(simp add: option_to_list_def)
   apply(rule proper_l3_l2_seq_nol2_prime)
    apply(rename_tac w' a' w'a a'a q ba)(*strict*)
    apply(force)
   apply(rename_tac w' a' w'a a'a q ba)(*strict*)
   apply(force)
  apply(rename_tac a w' a' w'a a'a q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a' w'a a'a q1 ba q2)(*strict*)
  apply(rule_tac
      x="None"
      in exI)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "drop (length (ESplitItem_to (S ! n))) (drop_and_crop (ESplitItem_to (S ! n) @ w'a @ [a'a]) (length (restrict_toberemovedX S ! Suc n))) = drop_and_crop (w'a @ [a'a]) (length (restrict_toberemovedX S ! Suc n))")
   apply(rename_tac w' a' w'a a'a q1 ba q2)(*strict*)
   prefer 2
   apply (metis cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac w' a' w'a a'a q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop (length (ESplitItem_to (S ! n))) (drop_and_crop (ESplitItem_to (S ! n) @ w'a @ [a'a]) (length (restrict_toberemovedX S ! Suc n))) = w' @ [a']")
  apply(rename_tac w' a' w'a a'a q1 ba q2)(*strict*)
  apply(case_tac a'a)
   apply(rename_tac w' a' w'a a'a q1 ba q2 q baa)(*strict*)
   prefer 2
   apply(rename_tac w' a' w'a a'a q1 ba q2 q1a baa q2a)(*strict*)
   apply(simp add: proper_l3_l2_seq_def)
  apply(rename_tac w' a' w'a a'a q1 ba q2 q baa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a' w'a q1 ba q2 q baa)(*strict*)
  apply(case_tac a')
   apply(rename_tac w' a' w'a q1 ba q2 q baa qa bb)(*strict*)
   prefer 2
   apply(rename_tac w' a' w'a q1 ba q2 q baa q1a bb q2a)(*strict*)
   apply(simp add: drop_and_crop_def cropTol3l2_def)
   apply(case_tac "butn (w'a @ [cons_l2 q baa]) (length (restrict_toberemovedX S ! Suc n)) = []")
    apply(rename_tac w' a' w'a q1 ba q2 q baa q1a bb q2a)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a' w'a q1 ba q2 q baa q1a bb q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w'a q1 ba q2 q baa q1a bb q2a)(*strict*)
   apply(simp add: cropTol3l2_single_def)
   apply(case_tac "last (butn (w'a @ [cons_l2 q baa]) (length (restrict_toberemovedX S ! Suc n)))")
    apply(rename_tac w'a q1 ba q2 q baa q1a bb q2a qa bc)(*strict*)
    apply(clarsimp)
   apply(rename_tac w'a q1 ba q2 q baa q1a bb q2a q1b bc q2b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' w'a q1 ba q2 q baa qa bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb)(*strict*)
  apply(case_tac "length (restrict_toberemovedX S ! Suc n)")
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb)(*strict*)
   apply(clarsimp)
   apply(simp add: drop_and_crop_def butn_def)
   apply(simp add: drop_and_crop_def cropTol3l2_def)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac w' q1 ba q2 qa bb)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(simp add: ValidPreContext_def fillWithPreContext_def fillOpt_def fillOptL_def ValidFillOL_def ValidFillO_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(simp add: option_to_list_def)
   apply(rule proper_l3_l2_seq_drop_prime)
    apply(rename_tac w' q1 ba q2 qa bb)(*strict*)
    apply(force)
   apply(rename_tac w' q1 ba q2 qa bb)(*strict*)
   apply(force)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>q. fillL (drop_and_crop SSw SSn) q = butn SSw SSn" for SSw SSn)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
   prefer 2
   apply(rule_tac
      w="w'a @ [cons_l2 q baa]"
      and n="Suc nat"
      in fillL_exists)
    apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
    apply(force)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
   apply(rule_tac w="ESplitItem_elim (S ! n) @ option_to_list (Some (cons_l3 q1 ba q2))" in proper_l3_l2_seq_drop_prime)
    apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
    apply(force)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
   apply(force)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
  apply(rule_tac
      x="Some qb"
      in exI)
  apply(simp add: ValidPreContext_def fillWithPreContext_def fillOpt_def fillOptL_def ValidFillOL_def ValidFillO_def)
  apply(rule conjI)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
   apply(rule_tac
      x="takeB (Suc nat) (w'a @ [cons_l2 q baa])"
      in exI)
   apply(rule_tac
      t="butn (w'a @ [cons_l2 q baa]) (Suc nat) @ takeB (Suc nat) (w'a @ [cons_l2 q baa])"
      and s="w'a@[cons_l2 q baa]"
      in ssubst)
    apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
    apply(simp add: takeB_def butn_def)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
   apply(rule_tac w="ESplitItem_elim (S ! n)" in proper_l3_l2_seq_drop_prime)
    apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
    apply(force)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
  apply(rule conjI)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
   apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
   apply(force)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
  apply(rule_tac
      x="takeB (Suc nat) (w'a @ [cons_l2 q baa])"
      in exI)
  apply(rule_tac
      t="butn (w'a @ [cons_l2 q baa]) (Suc nat) @ takeB (Suc nat) (w'a @ [cons_l2 q baa])"
      and s="w'a@[cons_l2 q baa]"
      in ssubst)
   apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
   apply(simp add: takeB_def butn_def)
  apply(rename_tac w' w'a q1 ba q2 q baa qa bb nat qb)(*strict*)
  apply(force)
  done

lemma equal_split_prefix_hlp1_elim_eq_updated: "
       F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S1 @ S1')
  \<Longrightarrow> EValidSplit G (S2 @ S2')
  \<Longrightarrow> length S1 = Suc (length v)
  \<Longrightarrow> length S2 = Suc (length v)
  \<Longrightarrow> Esplit_signature S2 = Esplit_signature S1
  \<Longrightarrow> v @ [teB b] = Esplit_signature S1
  \<Longrightarrow> ESplitItem_elem ((S1 @ S1') ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G (restrict G' G (S1 @ S1') (Suc (length v)))
  \<Longrightarrow> ESplitItem_elem ((S2 @ S2') ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G (restrict G' G (S2 @ S2') (Suc (length v)))
  \<Longrightarrow> n \<le> length v
  \<Longrightarrow> length (Esplit_signature S1) = Suc (length v)
  \<Longrightarrow> length (nat_seq 0 (length v)) = Suc (length v)
  \<Longrightarrow> nat_seq 0 (length v) ! n = n
  \<Longrightarrow> PSplitItem_elem (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = Esplit_signature S1 ! n
  \<Longrightarrow> PSplitItem_elem (restrict G' G (S2 @ S2') (Suc (length v)) ! n) = Esplit_signature S1 ! n
  \<Longrightarrow> PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)
  \<Longrightarrow> ESplitItem_elim (S1 ! n) = PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)
  \<Longrightarrow> ESplitItem_elim (S2 ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)
  \<Longrightarrow> teB a = Esplit_signature S1 ! n
  \<Longrightarrow> ESplitItem_elem (S2 ! n) = Some (Esplit_signature S1 ! n)
  \<Longrightarrow> ESplitItem_elem (S1 ! n) = Some (Esplit_signature S1 ! n)
  \<Longrightarrow> strict_prefix (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) (PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n))
  \<Longrightarrow> False"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?S1.0="[]"
      in trans_der_list_construct_elimininating_derivation_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ds \<pi>s fw)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      in PValidSplit_construct_derivation1)
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
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c)(*strict*)
  apply(simp add: Let_def)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c ca aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c aa list)(*strict*)
  apply(rename_tac A As)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
  apply(subgoal_tac "PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)=A")
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and ?d1.0="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      and f="\<lambda>x. x!length(PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in applyFunctionBack)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
    apply(rule_tac
      t="(PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) ! length (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
   apply(rule_tac
      t="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and s="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ A # As"
      in ssubst)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c A As)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As)(*strict*)
  apply(case_tac "PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(\<forall>x\<in> set (restrict G' G (S2 @ S2') (Suc (length v))). PValidSplitItem G' G x)")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    prefer 2
    apply(simp add: PValidSplit_ValidItem_def PValidSplit_def)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(erule_tac
      x="restrict G' G (S2 @ S2') (Suc (length v)) ! n"
      in ballE)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    prefer 2
    apply(subgoal_tac "restrict G' G (S2 @ S2') (Suc (length v)) ! n \<in> set (restrict G' G (S2 @ S2') (Suc (length v)))")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    apply(thin_tac "restrict G' G (S2 @ S2') (Suc (length v)) ! n \<notin> set (restrict G' G (S2 @ S2') (Suc (length v)))")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    apply(rule nth_mem)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(subgoal_tac "proper_l3_l2_seq (PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    prefer 2
    apply(simp add: PValidSplitItem_def PValidSplitItem_belongs_def)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(subgoal_tac "proper_l3_l2_seq ((PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l2 q ba # As) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    prefer 2
    apply(rule_tac
      s="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and t="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l2 q ba # As"
      in subst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(rule_tac q="q" and A="ba" and wx="As@PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)" and w="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)" in proper_l3_l2_seq_nol2_prime)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    apply(rule_tac
      t="(PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l2 q ba # As @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
      and s="((PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l2 q ba # As) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q ba)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(rule_tac
      A="PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)"
      in use_CFGprodXORelim)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    apply(simp add: CFG_not_end_nterm_def)
    apply(rule_tac
      x="d"
      in exI)
    apply(rule conjI)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def cfgLM.trans_der_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      x="length \<pi>"
      in exI)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a e)(*strict*)
    apply(simp add: fillWithPreContext_def liftA_commutes_over_concat)
    apply(rule_tac
      t="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and s="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l3 q1a ba q2a # As"
      in ssubst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a e)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a e)(*strict*)
    apply(thin_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l3 q1a ba q2a # As = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a e)(*strict*)
    apply(simp add: liftA_commutes_over_concat)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
    apply(rule_tac
      x="liftB (foldl (@) [] (take n fw)) @ liftA (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in exI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
    apply(rule_tac
      x="liftA (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q2) @ liftA c"
      in exI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
     apply(case_tac q1)
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
      apply(simp add: fillOpt_def)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e aa)(*strict*)
     apply(simp add: fillOpt_def fill_def)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
    apply(clarsimp)
    apply(case_tac c)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
     prefer 2
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e aa list)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c q1a ba q2a e)(*strict*)
    apply(clarsimp)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
    apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = []")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
     prefer 2
     apply(rule fillOptL_reflects_empty)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "PValidSplitItem_belongs G' G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
     prefer 2
     apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
      prefer 2
      apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
      apply(clarsimp)
      apply(erule_tac
      x="restrict G' G (S1 @ S1') (Suc (length v)) ! n"
      and A="set (restrict G' G (S1 @ S1') (Suc (length v)))"
      and P="\<lambda>x. PValidSplitItem G' G x"
      in ballE)
       apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
       apply(clarsimp)
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
      apply(subgoal_tac "restrict G' G (S1 @ S1') (Suc (length v)) ! n \<in> set (restrict G' G (S1 @ S1') (Suc (length v)))")
       apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
       apply(force)
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
      apply(thin_tac "restrict G' G (S1 @ S1') (Suc (length v)) ! n \<notin> set (restrict G' G (S1 @ S1') (Suc (length v)))")
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
      apply(rule nth_mem)
      apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
      apply(force)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
     apply(simp add: PValidSplitItem_def)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
    apply(subgoal_tac "proper_l3_l2_seq (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ [cons_l3 q1a ba q2a] @ [])")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
     prefer 2
     apply(simp only: PValidSplitItem_belongs_def)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 q1a ba q2a e)(*strict*)
    apply(simp add: proper_l3_l2_seq_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "PValidSplitItem_elim G (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    prefer 2
    apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     prefer 2
     apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
      A="set (restrict G' G (S2 @ S2') (Suc (length v)))"
      and x="restrict G' G (S2 @ S2') (Suc (length v)) ! n"
      and P="\<lambda>X. PValidSplitItem G' G X"
      in ballE)
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
      apply(clarsimp)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(subgoal_tac "restrict G' G (S2 @ S2') (Suc (length v)) ! n \<in> set (restrict G' G (S2 @ S2') (Suc (length v)))")
      apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
      apply(force)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(thin_tac "restrict G' G (S2 @ S2') (Suc (length v)) ! n \<notin> set (restrict G' G (S2 @ S2') (Suc (length v)))")
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(rule nth_mem)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    apply(simp add: PValidSplitItem_def)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
   apply(simp add: PValidSplitItem_elim_def)
   apply(subgoal_tac "PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) = ESplitItem_elim (S2 ! n)")
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
   apply(erule conjE)+
   apply(unfold elim_map_def)
   apply(erule_tac
      x="length(PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in allE)
   apply(erule impE)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    apply(rule_tac
      t="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and s="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l3 q1a ba q2a # As"
      in subst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
   apply(erule exE)+
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(rule_tac
      x="map the (get_labels da na)"
      in exI)
   apply(simp (no_asm) add: cfgLM.trans_der_def)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(rule_tac
      t="length (get_labels da na)"
      and s="na"
      in ssubst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(rule_tac
      G="G"
      in cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(blast)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule conjI)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(clarify)
    apply(rule_tac
      t="cons_l3 q1a ba q2a"
      and s="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) ! length (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in ssubst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(rule_tac
      t="PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)"
      and s="PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ cons_l3 q1a ba q2a # As"
      in subst)
     apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      t="length (get_labels da na)"
      and s="na"
      in ssubst)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(rule_tac
      t="\<lparr>cfg_conf=[]\<rparr>"
      and s="\<lparr>cfg_conf=liftB (map (\<lambda>x. []) (PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) ! length (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)))\<rparr>"
      in ssubst)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(simp (no_asm))
   apply(rule_tac
      t="map (\<lambda>x. []) (PSplitItem_elim_prods (restrict G' G (S2 @ S2') (Suc (length v)) ! n)) ! length (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n))"
      in ssubst)
    apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
    apply(rule nth_map)
    apply (metis ConsApp Suc_length append_assoc drop_length_append less_eq_Suc_le_raw)
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a da na e)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB (foldl (@) [] (take n fw)) @ liftA (PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q1 q2 @ c)\<rparr>")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "EValidSplit G (S2 @ S2')")
  apply(thin_tac "length S2 = Suc (length v)")
  apply(thin_tac "ESplitItem_elem ((S2 @ S2') ! length v) = Some (teB b)")
  apply(thin_tac "PValidSplit G' G (restrict G' G (S2 @ S2') (Suc (length v)))")
  apply(thin_tac "ESplitItem_elem (S2 ! n) = Some (Esplit_signature S1 ! n)")
  apply(thin_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S2 @ S2') (Suc (length v)) ! n) # PSplitItem_ignore (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "ESplitItem_elim (S2 ! n) = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "ValidPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q1 q2")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n) @ PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! n) # As = PSplitItem_elim (restrict G' G (S2 @ S2') (Suc (length v)) ! n)")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(thin_tac "ESplitItem_elim (S1 ! n) = PSplitItem_elim (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(subgoal_tac "PValidSplitItem G' G (restrict G' G (S1 @ S1') (Suc (length v)) ! n)")
   apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
   prefer 2
   apply(simp add: PValidSplit_def PValidSplit_ValidItem_def)
   apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="restrict G' G (S1 @ S1') (Suc (length v)) ! n"
      in ballE)
    apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
    prefer 2
    apply(subgoal_tac "restrict G' G (S1 @ S1') (Suc (length v)) ! n \<in> set (restrict G' G (S1 @ S1') (Suc (length v)))")
     apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
     apply(force)
    apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
    apply(rule nth_mem)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(force)
   apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
   apply(force)
  apply(rename_tac ds \<pi>s fw \<pi> d q1 q2 c As q1a ba q2a)(*strict*)
  apply(simp add: PValidSplitItem_def PValidSplitItem_gen_def)
  apply(rename_tac ds \<pi>s fw q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="\<pi>"
      in exI)
  apply(rule_tac
      x="a"
      in exI)
  apply(simp add: fillWithContext_def)
  apply(rule_tac
      x="liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q2) @ liftA (fillOptL c q3)"
      in exI)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
  apply(rule_tac
      t="Esplit_signature S1 ! n # liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q2) @ liftA (fillOptL c q3)"
      and s="fillBOpt (Esplit_signature S1 ! n) q1 # liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! n)) q2) @ liftA (fillOptL c q3)"
      in ssubst)
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
   prefer 2
   apply(rule_tac
      t="cons_l3 q1a ba q2a"
      and s="fillOpt (cons_l3 q1a ba q2a) q"
      in ssubst)
    apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
   apply(simp add: fillOpt_def fill_def)
   apply(case_tac q)
    apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
    apply(clarsimp)
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3 aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d c q1 q2 q3 aa)(*strict*)
   apply(simp add: fillOpt_def fill_def)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
  apply(clarsimp)
  apply(simp add: fillBOpt_def)
  apply(case_tac q1)
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q1 q2 q3 aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q2 q3 aa)(*strict*)
  apply(simp add: fillB_def)
  apply(case_tac "Esplit_signature S1 ! n")
   apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q2 q3 aa aaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac ds \<pi>s fw q1a ba q2a \<pi> d q c q2 q3 aa baa)(*strict*)
  apply(clarsimp)
  done

lemma restrict_toberemovedX_last: "
  Suc n = length S
  \<Longrightarrow> restrict_toberemovedX S ! Suc n = tl (ESplitItem_to (S!n) @ ESplitItem_ignore (S!n))"
  apply(simp add: restrict_toberemovedX_def)
  apply(rule_tac
      t="last S"
      and s="S!n"
      in ssubst)
   apply(rule last_nth3)
   apply(force)
  apply(rule nth_append_beyond)
  apply(rule_tac
      t="length(restrict_toberemoved S)"
      in ssubst)
   apply(rule length_restrict_toberemoved)
   apply(force)
  apply(force)
  done

lemma ignore_toberemoved_suffix: "
  S\<noteq>[]
  \<Longrightarrow> Suc i\<le>length S
  \<Longrightarrow> suffix (ESplitItem_ignore(S!i)) ((restrict_toberemoved S)!i)"
  apply(simp add: restrict_toberemoved_def enforceSuffix_def)
  apply(subgoal_tac "nat_seq 0 (length S - Suc 0) ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length S-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(simp add: takeB_def)
  apply(rule_tac
      x="take (length (ESplitItem_ignore (S ! i)) - Min (enforceSuffixS (map ESplitItem_ignore S) i)) (ESplitItem_ignore (S ! i))"
      in exI)
  apply (metis append_take_drop_id)
  done

lemma restrict_toberemoved_smaller: "
    i\<le>k
  \<Longrightarrow> k< length S
    \<Longrightarrow> length (restrict_toberemoved S ! i) \<le> length (restrict_toberemoved S ! k)"
  apply(simp add: restrict_toberemoved_def)
  apply(simp add: restrict_toberemoved_def enforceSuffix_def takeB_def)
  apply(subgoal_tac "nat_seq 0 (length S-Suc 0) ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "nat_seq 0 (length S- Suc 0) ! k = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length S-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule_tac
      t="length (ESplitItem_ignore (S ! i)) - (length (ESplitItem_ignore (S ! i)) - Min (enforceSuffixS (map ESplitItem_ignore S) i))"
      and s="Min (enforceSuffixS (map ESplitItem_ignore S) i)"
      in ssubst)
   apply(rule diff_diff_cancel)
   apply(rule Lattices_Big.linorder_class.Min_le)
    apply(rule enforceSuffixS_finite)
   apply(simp add: enforceSuffixS_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rule_tac
      t="length (ESplitItem_ignore (S ! k)) - (length (ESplitItem_ignore (S ! k)) - Min (enforceSuffixS (map ESplitItem_ignore S) k))"
      and s="Min (enforceSuffixS (map ESplitItem_ignore S) k)"
      in ssubst)
   apply(rule diff_diff_cancel)
   apply(rule Lattices_Big.linorder_class.Min_le)
    apply(rule enforceSuffixS_finite)
   apply(simp add: enforceSuffixS_def)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
  apply(rule enforceSuffixS_Min_Min)
   apply(force)
  apply(force)
  done

lemma toberemoved_suffix: "
  S\<noteq>[]
  \<Longrightarrow> Suc i<length S
  \<Longrightarrow> w1@ESplitItem_ignore (S ! i) = w2@ESplitItem_ignore (S ! Suc i)
  \<Longrightarrow> suffix ((restrict_toberemoved S)!(Suc i)) ((restrict_toberemoved S)!i)"
  apply(simp add: suffix_def)
  apply(subgoal_tac "length (restrict_toberemoved S ! i) \<le> length (restrict_toberemoved S ! (Suc i))")
   prefer 2
   apply(rule restrict_toberemoved_smaller)
    apply(force)
   apply(force)
  apply(subgoal_tac "restrict_toberemoved S ! i = takeB (length(restrict_toberemoved S ! (Suc i))) (ESplitItem_ignore (S ! i))")
   prefer 2
   apply(rule restrict_toberemoved_direct_computation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "suffix (ESplitItem_ignore(S!i)) ((restrict_toberemoved S)!i)")
   prefer 2
   apply(rule ignore_toberemoved_suffix)
    apply(force)
   apply(force)
  apply(subgoal_tac "suffix (ESplitItem_ignore(S!(Suc i))) ((restrict_toberemoved S)!(Suc i))")
   prefer 2
   apply(rule ignore_toberemoved_suffix)
    apply(force)
   apply(force)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(simp only: takeB_def)
  apply(subgoal_tac "length (drop (length (ESplitItem_ignore (S ! i)) - length (restrict_toberemoved S ! Suc i)) (ESplitItem_ignore (S ! i))) = (length (ESplitItem_ignore (S ! i))) - ((length (ESplitItem_ignore (S ! i)) - length (restrict_toberemoved S ! Suc i)))")
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix w1 w2 \<or> prefix w2 w1")
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac c ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca cb)(*strict*)
  apply(subgoal_tac "prefix cb ca \<or> prefix ca cb")
   apply(rename_tac c ca cb)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c ca cb)(*strict*)
  apply(erule disjE)
   apply(rename_tac c ca cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac c ca cb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca cc)(*strict*)
  apply(case_tac "length (ESplitItem_ignore (S ! i)) - length (restrict_toberemoved S ! Suc i)")
   apply(rename_tac c ca cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca cc)(*strict*)
   apply(rule_tac
      x="cc"
      in exI)
   apply(clarsimp)
  apply(rename_tac c ca cc nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (ESplitItem_ignore (S ! i)) \<le> length (restrict_toberemoved S ! Suc i) + Suc nat")
   apply(rename_tac c ca cc nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c ca cc nat)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (ESplitItem_ignore (S ! i)) - Suc nat \<le> length (restrict_toberemoved S ! Suc i)")
  apply(rename_tac c ca cc nat)(*strict*)
  apply(rule_tac
      t="restrict_toberemoved S ! Suc i"
      and s="cc @ ESplitItem_ignore (S ! i)"
      in ssubst)
   apply(rename_tac c ca cc nat)(*strict*)
   apply(force)
  apply(rename_tac c ca cc nat)(*strict*)
  apply(rule_tac
      x="cc@take (Suc nat) (ESplitItem_ignore (S ! i))"
      in exI)
  apply(clarsimp)
  done

lemma restrict_toberemoved_suffix: "
  Suc i < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> (restrict_toberemoved S ! Suc i) \<sqsupseteq> (restrict_toberemoved S ! i)"
  apply(subgoal_tac "EValidSplit_interline (S @ S2)")
   prefer 2
   apply(simp add: EValidSplit_def)
  apply(thin_tac "EValidSplit G (S @ S2)")
  apply(simp add: EValidSplit_interline_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "(S@S2)!i=S!i")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S@S2)!Suc i=S!Suc i")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc i) @ option_to_list (ESplitItem_from (S ! Suc i))"
      and ?w1.0="ESplitItem_to (S ! i)"
      in toberemoved_suffix)
    apply(force)
   apply(force)
  apply(force)
  done

lemma ESplitItem_ignore_restrict_toberemoved_suffix: "
  i\<le>k
  \<Longrightarrow> k < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> suffix (ESplitItem_ignore (S ! k)) (restrict_toberemoved S ! i)"
  apply(induct "k-i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply (metis gr_implies_not0 ignore_toberemoved_suffix length_0_conv less_eq_Suc_le)
  apply(rename_tac x i)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(subgoal_tac "suffix ((restrict_toberemoved S ! Suc i)) ((restrict_toberemoved S ! i))")
   apply(rename_tac x i)(*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(thin_tac "ESplitItem_ignore (S ! k) \<sqsupseteq> (restrict_toberemoved S ! Suc i)")
  apply(subgoal_tac "Suc x+i=k")
   apply(rename_tac x i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(thin_tac "Suc x=k-i")
  apply(clarsimp)
  apply(rule restrict_toberemoved_suffix)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  done

lemma ESplitItem_ignore_decompose: "
  i < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> ESplitItem_to (S ! (length S-Suc 0)) \<noteq> []
  \<Longrightarrow> ESplitItem_ignore (S ! i) = fillOptL (restrict_newignore S i) (last_back_state_if_l3_nonterminal (take (length (restrict_newignore S i)) (ESplitItem_ignore (S ! i)))) @ restrict_toberemoved S ! i"
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
      t="drop (length (ESplitItem_to (S ! i))) (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      and s="X" for X
      in ssubst)
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
   apply(rule drop_and_crop_length)
  apply(clarsimp)
  apply(case_tac "Suc i=length S")
   apply(clarsimp)
   apply(case_tac "length S")
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(simp add: restrict_toberemovedX_def)
   apply(rule_tac
      t="((restrict_toberemoved S @ [tl (ESplitItem_to (last S) @ ESplitItem_ignore (last S))]) ! Suc i)"
      in ssubst)
    apply(rule nth_append_beyond)
    apply(rule_tac
      t="length(restrict_toberemoved S)"
      in ssubst)
     apply(rule length_restrict_toberemoved)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac
      t="last S"
      and s="S!i"
      in ssubst)
    apply(rule last_nth3)
    apply(force)
   apply(simp add: drop_and_crop_def butn_def)
   apply(rule_tac
      t="(length (ESplitItem_ignore (S ! i)) - (length (ESplitItem_to (S ! i)) + length (ESplitItem_ignore (S ! i)) - Suc 0))"
      and s="0"
      in ssubst)
    apply(case_tac "ESplitItem_to (S ! i)")
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: cropTol3l2_def)
   apply(simp add: fillOptL_def)
   apply(simp add: last_back_state_if_l3_nonterminal_def)
   apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last SSS)" for SSS)
    prefer 2
    apply(rule_tac
      S="S"
      in restrict_toberemoved_last_is_ignore)
    apply(force)
   apply(rule_tac
      t="S ! i"
      and s="last S"
      in ssubst)
    apply(rule last_nth_prime)
    apply(force)
   apply(rule_tac
      t="restrict_toberemoved S ! i"
      and s="last (restrict_toberemoved S)"
      in ssubst)
    apply(rule last_nth_prime)
    apply(simp add: restrict_toberemoved_def enforceSuffix_def)
    apply(subgoal_tac "length(nat_seq 0 i) = SSX" for SSX)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(force)
   apply(force)
  apply(subgoal_tac "Suc i<length S")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(case_tac "length S")
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "restrict_toberemoved S ! i = takeB (length(restrict_toberemoved S ! (Suc i))) (ESplitItem_ignore (S ! i))")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc i) @ option_to_list (ESplitItem_from (S ! Suc i))"
      and ?w1.0="ESplitItem_to (S ! i)"
      in restrict_toberemoved_direct_computation)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "EValidSplit_interline (S @ S2)")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(rename_tac nat)(*strict*)
   apply(thin_tac "EValidSplit G (S @ S2)")
   apply(simp add: EValidSplit_interline_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "(S@S2)!i=S!i")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "(S@S2)!Suc i=S!Suc i")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(simp add: EValidSplit_interlineX_def)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(simp add: takeB_def)
  apply(rule_tac
      t="fillOptL (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i))) (last_back_state_if_l3_nonterminal (take (length (ESplitItem_ignore (S ! i)) - length (restrict_toberemovedX S ! Suc i)) (ESplitItem_ignore (S ! i))))"
      and s="take (length (ESplitItem_ignore (S ! i)) - length (restrict_toberemoved S ! Suc i)) (ESplitItem_ignore (S ! i))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule append_take_drop_id)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i))"
      in fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length (ESplitItem_ignore (S ! i)) - length (restrict_toberemovedX S ! Suc i)"
      and s="length (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="length (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(rule drop_and_crop_length)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length (ESplitItem_ignore (S ! i)) - length (restrict_toberemoved S ! Suc i)"
      and s="length (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length (drop_and_crop (ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="restrict_toberemovedX S ! Suc i"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma e_derivation_can_be_embedded_minimally_hlp3: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S1 @ S1')
  \<Longrightarrow> v @ [teB b] = Esplit_signature S1
  \<Longrightarrow> ESplitItem_elem (S1 ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G (restrict G' G (S1 @ S1') (Suc (length v)))
  \<Longrightarrow> i \<le> length v
  \<Longrightarrow> S1' \<noteq> []
  \<Longrightarrow> length (Esplit_signature S1) = Suc (length v)
  \<Longrightarrow> length S1 = Suc (length v)
  \<Longrightarrow> length (nat_seq 0 (length v)) = Suc (length v)
  \<Longrightarrow> nat_seq 0 (length v) ! length v = length v
  \<Longrightarrow> (S1 @ S1') ! i = S1 ! i
  \<Longrightarrow> (S1 @ S1') ! Suc i = S1 ! Suc i
  \<Longrightarrow> (S1 @ S1') ! length v = S1 ! length v
  \<Longrightarrow> ESplitItem_from (S1 ! i) = Some a
  \<Longrightarrow> nat_seq 0 (length v) ! i = i
  \<Longrightarrow> nat_seq 0 (length v) ! Suc i = Suc i
  \<Longrightarrow> \<exists>d. cfgLMMIy G d (liftA (a # drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) (liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))) []"
  apply(subgoal_tac "EValidSplitItem G (S1 ! i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(subgoal_tac "EValidSplitItem G (S1 ! Suc i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      x="S1!Suc i"
      in ballE)
    apply(force)
   apply(subgoal_tac "S1!Suc i\<in> set S1")
    apply(force)
   apply(rule nth_mem)
   apply (metis Suc_lessI length_greater_0_conv less_Suc_eq_le nth_append_2_prime_prime nth_mem set_append set_append_contra2)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_interline_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac "i=length v")
    apply(clarsimp)
   apply(subgoal_tac "i<length v")
    prefer 2
    apply(force)
   apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(thin_tac "EValidSplitItem_elim G (S1 ! i)")
  apply(thin_tac "EValidSplitItem_gen G (S1 ! Suc i)")
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_elim_def EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule elim_map_to_trans_der_cfgLMMIy)
      apply(rename_tac d)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac d)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "elim_map G (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_elim_prods (S1 ! Suc i)) (map (\<lambda>x. []) (ESplitItem_elim_prods (S1 ! Suc i)))")
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "(\<exists>b. Some (teB b) = ESplitItem_elem (S1 ! i)) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S1 ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> the (ESplitItem_elem (S1 ! i)))")
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "(\<exists>A. Some (teA A) = ESplitItem_elem (S1 ! i)) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S1 ! i) = []")
  apply(rename_tac d da)(*strict*)
  apply(subgoal_tac "ESplitItem_elem (S1 ! i) = Some (SSv ! i)" for SSv)
   apply(rename_tac d da)(*strict*)
   prefer 2
   apply(rule Esplit_signature_take_prefix_closureise)
     apply(rename_tac d da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d da)(*strict*)
    apply(force)
   apply(rename_tac d da)(*strict*)
   apply(force)
  apply(rename_tac d da)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d da)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="liftA (option_to_list (Some a))"
      and G="G"
      and ?v1.0="[]"
      and ?v2.0="option_to_list (Some (Esplit_signature S1 ! i))"
      and ?v4.0="liftA (ESplitItem_to (S1 ! i))"
      and ?d1.0="d"
      and ?d2.0="ds!i"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d da)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac d da)(*strict*)
    prefer 2
    apply(rule_tac
      t="option_to_list (Some (Esplit_signature S1 ! i))"
      and s="[Esplit_signature S1 ! i]"
      in ssubst)
     apply(rename_tac d da)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac d da)(*strict*)
    apply(force)
   apply(rename_tac d da)(*strict*)
   apply(rule_tac
      t="\<lparr>cfg_conf = liftB [] @ option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>"
      and s="\<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>"
      in ssubst)
    apply(rename_tac d da)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac d da)(*strict*)
   apply(force)
  apply(rename_tac d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>")
  apply(rename_tac d da db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (ds ! i) \<lparr>cfg_conf = [Esplit_signature S1 ! i]\<rparr> (\<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac d da db)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da db)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="liftA(drop (length(ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
      and ?d1.0="db"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac d da db)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(rename_tac da db)(*strict*)
     apply(force)
    apply(rename_tac d da db)(*strict*)
    apply(clarsimp)
    apply(rename_tac da db)(*strict*)
    apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
    apply(clarsimp)
    apply (simp add: setB_liftA)
    apply(rule_tac
      B="setA (liftA ((ESplitItem_elim (S1 ! Suc i))))"
      in subset_trans)
     apply(rename_tac da db)(*strict*)
     apply(simp add: setA_liftA_set_drop_subset)
    apply(rename_tac da db)(*strict*)
    apply (simp add: setA_liftA)
   apply(rename_tac d da db)(*strict*)
   apply(force)
  apply(rename_tac d da db)(*strict*)
  apply(clarsimp)
  apply(rename_tac da db d)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>")
   apply(rename_tac da db d)(*strict*)
   prefer 2
   apply(rule_tac
      t="(liftA (ESplitItem_elim (S1 ! Suc i)@drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))))"
      and s="liftA (ESplitItem_to (S1 ! i) @drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
      in ssubst)
    apply(rename_tac da db d)(*strict*)
    apply(rule_tac
      f="liftA"
      in arg_cong)
    apply(subgoal_tac "X" for X)
     apply(rename_tac da db d)(*strict*)
     prefer 2
     apply(rule_tac
      ?w1.0="ESplitItem_elim (S1 ! Suc i)"
      and ?w2.0="ESplitItem_to (S1 ! i)"
      in shortest_dropper)
     apply(force)
    apply(rename_tac da db d)(*strict*)
    apply(force)
   apply(rename_tac da db d)(*strict*)
   apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac da db d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>")
  apply(rename_tac da db d)(*strict*)
  apply(subgoal_tac "option_to_list (Some a) = [a]")
   apply(rename_tac da db d)(*strict*)
   prefer 2
   apply(simp add: option_to_list_def)
  apply(rename_tac da db d)(*strict*)
  apply(clarsimp)
  apply(thin_tac "option_to_list (Some a) = [a]")
  apply(case_tac "foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) = []")
   apply(rename_tac da db d)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_elim (S1 ! Suc i)=[]")
    apply(rename_tac da db d)(*strict*)
    prefer 2
    apply(simp add: cfgLMMIy_def cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac da db d e ea)(*strict*)
    apply(case_tac "ESplitItem_elim (S1 ! Suc i)")
     apply(rename_tac da db d e ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac da db d e ea aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac da db d)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="d"
      in exI)
   apply(simp add: cfgLMMIy_def)
   apply(simp add: cfgLMMIyX_def)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_prods (S1 ! i) @ \<pi>s ! i=[]")
    apply(rename_tac da db d)(*strict*)
    apply(force)
   apply(rename_tac da db d)(*strict*)
   apply(rule applicable_with_empty_source)
   apply(force)
  apply(rename_tac da db d)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i)) \<or> SSX" for SSX)
   apply(rename_tac da db d)(*strict*)
   prefer 2
   apply(rule_tac
      b="option_to_list (ESplitItem_from (S1 ! Suc i)) @ ESplitItem_ignore (S1 ! Suc i)"
      in mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac da db d)(*strict*)
  apply(erule disjE)
   apply(rename_tac da db d)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac da db d c)(*strict*)
   apply(subgoal_tac "liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))=[]")
    apply(rename_tac da db d c)(*strict*)
    prefer 2
    apply(rule_tac
      t="ESplitItem_to (S1 ! i)"
      and s="ESplitItem_elim (S1 ! Suc i) @ c"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac da db d c)(*strict*)
   apply(rule_tac
      t="ESplitItem_to (S1 ! i)"
      and s="ESplitItem_elim (S1 ! Suc i) @ c"
      in ssubst)
    apply(rename_tac da db d c)(*strict*)
    apply(force)
   apply(rename_tac da db d c)(*strict*)
   apply(simp (no_asm))
   apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i))\<rparr>")
   apply(rename_tac da db d c)(*strict*)
   apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i)) @ liftA c\<rparr>")
    apply(rename_tac da db d c)(*strict*)
    prefer 2
    apply(rule_tac
      t="\<lparr>cfg_conf = [teA a]\<rparr>"
      and s="\<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(rule_tac
      t="ESplitItem_to (S1 ! i)"
      and s="ESplitItem_elim (S1 ! Suc i) @ c"
      in ssubst)
      apply(rename_tac da db d c)(*strict*)
      apply(force)
     apply(rename_tac da db d c)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac da db d c)(*strict*)
    apply(rule_tac
      t="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i)) @ liftA c\<rparr>"
      and s="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(rule_tac
      t="ESplitItem_to (S1 ! i)"
      and s="ESplitItem_elim (S1 ! Suc i) @ c"
      in ssubst)
      apply(rename_tac da db d c)(*strict*)
      apply(force)
     apply(rename_tac da db d c)(*strict*)
     apply(simp (no_asm))
     apply(rename_tac da d c)(*strict*)
     apply(simp add: liftA_commutes_over_concat)
     apply(rule_tac
      t="ESplitItem_to (S1 ! i)"
      and s="ESplitItem_elim (S1 ! Suc i) @ c"
      in ssubst)
      apply(rename_tac da d c)(*strict*)
      apply(force)
     apply(rename_tac da d c)(*strict*)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rename_tac da db d c)(*strict*)
    apply(force)
   apply(rename_tac da db d c)(*strict*)
   apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>")
   apply(rename_tac da db d c)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac da db d c)(*strict*)
    prefer 2
    apply(rule_tac
      ?\<pi>1.0="ESplitItem_prods (S1 ! i) @ \<pi>s ! i"
      and ?v2.0="liftA (ESplitItem_elim (S1 ! Suc i))"
      and ?w1.0="[teA a]"
      and G="G"
      and ?v1.0="fw!i"
      and ?v4.0="liftA c"
      and ?d1.0="d"
      and ?d2.0="da"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac da db d c)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac da db d c)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(simp add: cfgLMMIy_def)
    apply(force)
   apply(rename_tac da db d c)(*strict*)
   apply(clarsimp)
   apply(rename_tac da d c db)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(simp add: cfgLMMIy_def)
   apply(simp add: cfgLMMIyX_def)
   apply(clarsimp)
   apply(subgoal_tac "(ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)))=[]")
    apply(rename_tac da d c db)(*strict*)
    apply(force)
   apply(rename_tac da d c db)(*strict*)
   apply(rule applicable_with_empty_source)
   apply(force)
  apply(rename_tac da db d)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac da db d c)(*strict*)
  apply(rule_tac
      t="ESplitItem_elim (S1 ! Suc i)"
      and s="ESplitItem_to (S1 ! i) @ c"
      in ssubst)
   apply(rename_tac da db d c)(*strict*)
   apply(force)
  apply(rename_tac da db d c)(*strict*)
  apply(rule_tac
      t="drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_to (S1 ! i) @ c)"
      and s="c"
      in ssubst)
   apply(rename_tac da db d c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac da db d c)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA c\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i))\<rparr>")
   apply(rename_tac da db d c)(*strict*)
   prefer 2
   apply(rule_tac
      t="\<lparr>cfg_conf = teA a # liftA c\<rparr>"
      and s="\<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
      in ssubst)
    apply(rename_tac da db d c)(*strict*)
    apply(rule_tac
      t="ESplitItem_elim (S1 ! Suc i)"
      and s="ESplitItem_to (S1 ! i) @ c"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac da db d c)(*strict*)
   apply(rule_tac
      t="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i))\<rparr>"
      and s="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
      in ssubst)
    apply(rename_tac da db d c)(*strict*)
    apply(rule_tac
      t="ESplitItem_elim (S1 ! Suc i)"
      and s="ESplitItem_to (S1 ! i) @ c"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(simp (no_asm))
    apply(simp (no_asm) add: liftA_commutes_over_concat)
   apply(rename_tac da db d c)(*strict*)
   apply(force)
  apply(rename_tac da db d c)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>")
  apply(rename_tac da db d c)(*strict*)
  apply(rule_tac
      t="drop (length (ESplitItem_to (S1 ! i) @ c)) (ESplitItem_to (S1 ! i))"
      and s="[]"
      in ssubst)
   apply(rename_tac da db d c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac da db d c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac da db d c)(*strict*)
   prefer 2
   apply(rule_tac
      ?\<pi>1.0="ESplitItem_prods (S1 ! i) @ \<pi>s ! i"
      and ?\<alpha>1.0="fw!i"
      and ?w3.0="liftA (ESplitItem_to (S1 ! i))"
      and ?w2.0="liftA c"
      and ?\<pi>2.0="(foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)))"
      and ?\<alpha>2.0="[]"
      and ?A1.0="teA a"
      and G="G"
      and ?d1.0="db"
      and ?d2.0="da"
      in concat_cfgLM_trans_der_cfgLMMIy)
        apply(rename_tac da db d c)(*strict*)
        apply(simp add: split_TSstructure_def)
       apply(rename_tac da db d c)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac da db d c)(*strict*)
      apply(force)
     apply(rename_tac da db d c)(*strict*)
     apply(rule_tac
      t="liftA (ESplitItem_to (S1 ! i)) @ liftA c"
      and s="liftA (ESplitItem_elim (S1 ! Suc i))"
      in ssubst)
      apply(rename_tac da db d c)(*strict*)
      apply(rule_tac
      t="ESplitItem_elim (S1 ! Suc i)"
      and s="ESplitItem_to (S1 ! i) @ c"
      in ssubst)
       apply(rename_tac da db d c)(*strict*)
       apply(force)
      apply(rename_tac da db d c)(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac da db d c)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(rule_tac
      t="liftA (ESplitItem_to (S1 ! i)) @ liftA c"
      and s="liftA(ESplitItem_elim (S1 ! Suc i))"
      in ssubst)
     apply(rename_tac da db d c)(*strict*)
     apply(rule_tac
      t="ESplitItem_elim (S1 ! Suc i)"
      and s="ESplitItem_to (S1 ! i) @ c"
      in ssubst)
      apply(rename_tac da db d c)(*strict*)
      apply(force)
     apply(rename_tac da db d c)(*strict*)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rename_tac da db d c)(*strict*)
    apply(case_tac "ESplitItem_elim (S1 ! Suc i)=[]")
     apply(rename_tac da db d c)(*strict*)
     prefer 2
     apply(case_tac "ESplitItem_elim (S1 ! Suc i)")
      apply(rename_tac da db d c)(*strict*)
      apply(force)
     apply(rename_tac da db d c aa list)(*strict*)
     apply(force)
    apply(rename_tac da db d c)(*strict*)
    apply(clarsimp)
   apply(rename_tac da db d c)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = teA a # liftA c\<rparr> \<in> cfg_configurations G")
    apply(rename_tac da db d c)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac da db d c)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
    apply(rename_tac da db d c)(*strict*)
    apply(force)
   apply(rename_tac da db d c)(*strict*)
   apply(force)
  apply(rename_tac da db d c)(*strict*)
  apply(force)
  done

lemma restrict_toberemoved_restrict_toberemoved_suffix: "
  i\<le>k
  \<Longrightarrow> k < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> suffix (restrict_toberemoved S ! k) (restrict_toberemoved S ! i)"
  apply(induct "k-i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
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
  apply(subgoal_tac "suffix ((restrict_toberemoved S ! Suc i)) ((restrict_toberemoved S ! i))")
   apply(rename_tac x i)(*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule restrict_toberemoved_suffix)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  done

lemma toberemoved_suffix_X: "
  S\<noteq>[]
  \<Longrightarrow> Suc i<length S
  \<Longrightarrow> w1@ESplitItem_ignore (S ! i) = w2@ESplitItem_ignore (S ! Suc i)
  \<Longrightarrow> suffix ((restrict_toberemovedX S)!(Suc i)) ((restrict_toberemovedX S)!i)"
  apply(rule_tac
      t="restrict_toberemovedX S ! Suc i"
      in ssubst)
   apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
   apply(force)
  apply(rule_tac
      t="restrict_toberemovedX S ! i"
      in ssubst)
   apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
   apply(force)
  apply(rule toberemoved_suffix)
    apply(force)+
  done

lemma restrict_toberemoved_suffix_X: "
  Suc i < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> (restrict_toberemovedX S ! Suc i) \<sqsupseteq> (restrict_toberemovedX S ! i)"
  apply(subgoal_tac "EValidSplit_interline (S @ S2)")
   prefer 2
   apply(simp add: EValidSplit_def)
  apply(thin_tac "EValidSplit G (S @ S2)")
  apply(simp add: EValidSplit_interline_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "(S@S2)!i=S!i")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S@S2)!Suc i=S!Suc i")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc i) @ option_to_list (ESplitItem_from (S ! Suc i))"
      and ?w1.0="ESplitItem_to (S ! i)"
      in toberemoved_suffix_X)
    apply(force)
   apply(force)
  apply(force)
  done

lemma restrict_toberemoved_restrict_toberemoved_suffix_X: "
  i\<le>k
  \<Longrightarrow> k < length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> suffix (restrict_toberemovedX S ! k) (restrict_toberemovedX S ! i)"
  apply(induct "k-i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
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
  apply(subgoal_tac "suffix ((restrict_toberemovedX S ! Suc i)) ((restrict_toberemovedX S ! i))")
   apply(rename_tac x i)(*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule restrict_toberemoved_suffix_X)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  done

lemma restrict_toberemoved_restrict_toberemoved_suffix_X2: "
  i\<le>k
  \<Longrightarrow> k \<le> length S
  \<Longrightarrow> EValidSplit G (S @ S2)
  \<Longrightarrow> ESplitItem_to (last S) \<noteq> []
  \<Longrightarrow> S \<noteq> []
  \<Longrightarrow> suffix (restrict_toberemovedX S ! k) (restrict_toberemovedX S ! i)"
  apply(case_tac "k=length S")
   prefer 2
   apply(rule restrict_toberemoved_restrict_toberemoved_suffix_X)
     apply(force)+
  apply(case_tac "i=k")
   apply(clarsimp)
   apply(simp add: suffix_def)
  apply(clarsimp)
  apply(simp add: restrict_toberemovedX_def)
  apply(rule_tac
      t="(restrict_toberemoved S @ [tl (ESplitItem_to (last S) @ ESplitItem_ignore (last S))]) ! length S"
      in ssubst)
   apply(rule nth_append_beyond)
   apply(rule_tac
      t="length(restrict_toberemoved S)"
      in ssubst)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(force)
  apply(rule_tac
      t="(restrict_toberemoved S @ [tl (ESplitItem_to (last S)) @ ESplitItem_ignore (last S)]) ! i"
      in ssubst)
   apply(rule nth_append_1)
   apply(rule_tac
      t="length(restrict_toberemoved S)"
      in ssubst)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(force)
  apply(subgoal_tac "i<length S")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      xs="S"
      in rev_cases)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      b="(restrict_toberemoved (ys @ [y]) ! length ys)"
      in suffix_trans)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
     apply(rename_tac ys y)(*strict*)
     apply(force)
    apply(rename_tac ys y)(*strict*)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      t="(restrict_toberemoved (ys @ [y]) @ [tl (ESplitItem_to y) @ ESplitItem_ignore y]) ! Suc (length ys)"
      in ssubst)
   apply(rename_tac ys y)(*strict*)
   apply(rule nth_append_beyond)
   apply(rule_tac
      t="length(restrict_toberemoved SSX)" for SSX
      in ssubst)
    apply(rename_tac ys y)(*strict*)
    apply(rule length_restrict_toberemoved)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      t="restrict_toberemoved (ys @ [y]) ! length ys"
      in ssubst)
   apply(rename_tac ys y)(*strict*)
   apply(rule restrict_toberemoved_at_last)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      t="(ys @ [y]) ! length ys"
      in ssubst)
   apply(rename_tac ys y)(*strict*)
   apply(rule nth_append_beyond)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(case_tac "ESplitItem_to y")
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rename_tac ys y a list)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac ys y)(*strict*)
  apply(force)
  done

lemma restrict_toberemoved_equal: "
  Suc i<length S
  \<Longrightarrow> w@ESplitItem_ignore (S ! (Suc i))= ESplitItem_ignore (S ! i)
  \<Longrightarrow> restrict_toberemoved S ! i =restrict_toberemoved S ! (Suc i)"
  apply(subgoal_tac "nat_seq 0 (length S - Suc 0) ! (Suc i) = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length S-Suc 0)) = SSn + 1 - SSm" for SSn SSm)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length S- Suc 0) ! i = (SSn)+(SSi)" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: restrict_toberemoved_def)
  apply(simp add: enforceSuffix_def)
  apply(clarsimp)
  apply(subgoal_tac "Min (enforceSuffixS (map ESplitItem_ignore S) (Suc i)) = Min (enforceSuffixS (map ESplitItem_ignore S) i)")
   apply(subgoal_tac "Min (enforceSuffixS (map ESplitItem_ignore S) i) \<le> length(ESplitItem_ignore (S ! i))")
    apply(subgoal_tac "Min (enforceSuffixS (map ESplitItem_ignore S) i) \<le> length (ESplitItem_ignore (S ! Suc i))")
     apply(rule_tac
      t="ESplitItem_ignore (S ! i)"
      and s="w @ ESplitItem_ignore (S ! Suc i)"
      in ssubst)
      apply(force)
     apply(thin_tac "w @ ESplitItem_ignore (S ! Suc i) = ESplitItem_ignore (S ! i)")
     apply(simp add: takeB_def)
    apply(rule enforceSuffixS_smaller)
     apply(force)
    apply(force)
   apply(rule enforceSuffixS_smaller)
    apply(force)
   apply(force)
  apply(rule order_antisym)
   prefer 2
   apply(rule enforceSuffixS_Min_Min)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>A. enforceSuffixS (map ESplitItem_ignore S) i = A \<union>{length(ESplitItem_ignore (S ! (Suc i))),length(ESplitItem_ignore (S ! i))} \<and> enforceSuffixS (map ESplitItem_ignore S) (Suc i) = A \<union>{length(ESplitItem_ignore (S ! Suc i))} ")
   prefer 2
   apply(rule_tac
      x="enforceSuffixS (map ESplitItem_ignore S) (Suc (Suc i))"
      in exI)
   apply(rule conjI)
    apply(rule order_antisym)
     apply(simp add: enforceSuffixS_def)
     apply(clarsimp)
     apply(rename_tac ia)(*strict*)
     apply(case_tac ia)
      apply(rename_tac ia)(*strict*)
      apply(clarsimp)
     apply(rename_tac ia nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat)(*strict*)
     apply(case_tac nat)
      apply(rename_tac nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac nat nata)(*strict*)
     apply(clarsimp)
     apply(rename_tac nata)(*strict*)
     apply(rule_tac
      x="nata"
      in exI)
     apply(force)
    apply(clarsimp)
    apply(simp add: enforceSuffixS_def)
    apply(rule conjI)
     apply(rule_tac
      x="Suc 0"
      in exI)
     apply(force)
    apply(rule conjI)
     apply(rule_tac
      x="0"
      in exI)
     apply(force)
    apply(clarsimp)
    apply(rename_tac ia)(*strict*)
    apply(rule_tac
      x="Suc (Suc ia)"
      in exI)
    apply(force)
   apply(rule order_antisym)
    apply(simp add: enforceSuffixS_def)
    apply(clarsimp)
    apply(rename_tac ia)(*strict*)
    apply(case_tac ia)
     apply(rename_tac ia)(*strict*)
     apply(clarsimp)
    apply(rename_tac ia nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat)(*strict*)
    apply(rule_tac
      x="nat"
      in exI)
    apply(force)
   apply(clarsimp)
   apply(simp add: enforceSuffixS_def)
   apply(rule conjI)
    apply(rule_tac
      x="0"
      in exI)
    apply(force)
   apply(clarsimp)
   apply(rename_tac ia)(*strict*)
   apply(rule_tac
      x="Suc ia"
      in exI)
   apply(force)
  apply(erule exE)+
  apply(rename_tac A)(*strict*)
  apply(rule_tac
      t="enforceSuffixS (map ESplitItem_ignore S) (Suc i)"
      and s="A \<union> {length (ESplitItem_ignore (S ! Suc i))}"
      in ssubst)
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(rule_tac
      t="enforceSuffixS (map ESplitItem_ignore S) i"
      and s="A \<union> {length (ESplitItem_ignore (S ! Suc i)), length (ESplitItem_ignore (S ! i))}"
      in ssubst)
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(subgoal_tac "Min (A \<union> {length (ESplitItem_ignore (S ! Suc i))}) = Min (A \<union> {length (ESplitItem_ignore (S ! Suc i)), length (ESplitItem_ignore (S ! i))})")
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(rule insert_larger_in_Min_set2)
   apply(rename_tac A)(*strict*)
   apply(rule_tac
      B="enforceSuffixS (map ESplitItem_ignore S) (Suc i)"
      in finite_subset)
    apply(rename_tac A)(*strict*)
    apply(force)
   apply(rename_tac A)(*strict*)
   apply(rule enforceSuffixS_finite)
  apply(rename_tac A)(*strict*)
  apply(rule_tac
      t="ESplitItem_ignore (S ! i)"
      and s="w @ ESplitItem_ignore (S ! Suc i)"
      in ssubst)
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(thin_tac "w @ ESplitItem_ignore (S ! Suc i) = ESplitItem_ignore (S ! i)")
  apply(force)
  done

theorem e_derivation_can_be_embedded_minimally: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S1@S1')
  \<Longrightarrow> length S1 = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S1
  \<Longrightarrow> x1 = Esplit_signature S1'
  \<Longrightarrow> S1R=restrict G' G (S1@S1') (length (v@[teB b]))
  \<Longrightarrow> ESplitItem_elem ((S1@S1') ! (length v)) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G S1R
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
  \<Longrightarrow> RSi = restrict G' G (S1 @ S1') (Suc n) ! i
  \<Longrightarrow> RSn = restrict G' G (S1 @ S1') (Suc n) ! n
  \<Longrightarrow> p_ignore_i = PSplitItem_ignore RSi
  \<Longrightarrow> p_from_i = PSplitItem_from RSi
  \<Longrightarrow> p_to_n = PSplitItem_to RSn
  \<Longrightarrow> q1 = last_back_state_if_l3_nonterminal (e_from_i)
  \<Longrightarrow> q2 = last_back_state_if_l3_nonterminal (take (length (p_ignore_i)) e_ignore_i)
  \<Longrightarrow> q = last_back_state_if_l3_nonterminal (take(Suc 0)(e_to_n))
  \<Longrightarrow> c' = drop (length (p_ignore_i)) e_ignore_i
  \<Longrightarrow> tbRi = restrict_toberemoved S1 ! i
  \<Longrightarrow> tbRn = restrict_toberemoved S1 ! n
  \<Longrightarrow> c = (tl(e_to_n))@butn tbRn (length tbRi)
  \<Longrightarrow> \<exists>p_d.
  ((fillWithPreContext p_from_i p_ignore_i q1 q2) @ c' = (e_from_i@e_ignore_i))
  \<and> (((fillOptL (p_to_n) q@c)) @ c' = e_to_n@e_ignore_n)
  \<and> (cfgLMMIP G p_d (liftA(fillWithPreContext p_from_i p_ignore_i q1 q2)) e_\<pi> (liftB(\<alpha>@[b])) (liftA(fillOptL (p_to_n) q@c)))
  \<and> (q1=last_back_state_if_l3_nonterminal (e_from_i))
  \<and> (p_ignore_i = [] \<longrightarrow> (
        c'=e_ignore_i
        \<and> (\<exists>e_d v. cfgLM.trans_der G e_d \<lparr>cfg_conf=liftA(e_from_i)\<rparr> e_\<pi> \<lparr>cfg_conf=liftB \<alpha>@[teB b]@v\<rparr>)))
  \<and> (p_ignore_i \<noteq> [] \<longrightarrow> (
        (\<exists>e_d1 e_d2 v e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2.
        e_\<pi>=e_\<pi>1@e_\<pi>2
        \<and> \<alpha>=\<alpha>1@\<alpha>2
        \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf=liftA(e_from_i@butlast(fillOptL (p_ignore_i) q2))\<rparr> e_\<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
        \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf=[teA(last(fillOptL (p_ignore_i) q2))]\<rparr> e_\<pi>2 \<lparr>cfg_conf=liftB \<alpha>2@[teB b]@v\<rparr>
  )))"
  apply(subgoal_tac "S1'\<noteq>[]")
   prefer 2
   apply(clarsimp)
   apply(simp add: EValidSplit_def)
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
   apply(simp add: EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(simp add: EValidSplitItem_def)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_elem a' = Some (teB b)")
    apply(rename_tac w' a')(*strict*)
    apply(case_tac "ESplitItem_from a'")
     apply(rename_tac w' a')(*strict*)
     apply(simp add: EValidSplitItem_gen_def)
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
    apply(rename_tac w' a' a)(*strict*)
    apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
         apply(rename_tac w' a' a)(*strict*)
         apply(force)
        apply(rename_tac w' a' a)(*strict*)
        apply(force)
       apply(rename_tac w' a' a)(*strict*)
       apply(force)
      apply(rename_tac w' a' a)(*strict*)
      apply(force)
     apply(rename_tac w' a' a)(*strict*)
     apply(force)
    apply(rename_tac w' a' a)(*strict*)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply (metis lists_rest.nth_shift length_Suc nth_Cons_Suc nth_last_of_one)
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
  apply(induct "(length v)-i" arbitrary: i e_d)
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
    apply(erule exE)+
    apply(rename_tac w' a')(*strict*)
    apply(rule_tac
      t="S1'"
      and s="w'@[a']"
      in ssubst)
     apply(rename_tac w' a')(*strict*)
     apply(force)
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
   apply(rule context_conjI)
    apply(rename_tac a)(*strict*)
    apply(simp add: fillWithPreContext_def)
    apply(subgoal_tac "fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! length v))) (ESplitItem_ignore ((S1 @ S1') ! length v)))) = take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! length v))) (ESplitItem_ignore ((S1 @ S1') ! length v))")
     apply(rename_tac a)(*strict*)
     apply(subgoal_tac "option_to_list (ESplitItem_from ((S1 @ S1') ! length v)) = [fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (option_to_list (ESplitItem_from ((S1 @ S1') ! length v))))]")
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(simp add: option_to_list_def)
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
     apply(clarsimp)
     apply(subgoal_tac "restrict_newignore S1 (length v)=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac a)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac a)(*strict*)
     apply(erule disjE)
      apply(rename_tac a)(*strict*)
      apply(clarsimp)
      apply(simp add: cropTol3l2_def cropTol3l2_single_def)
      apply(case_tac a)
       apply(rename_tac a q ba)(*strict*)
       apply(clarsimp)
       apply(rename_tac q ba)(*strict*)
       apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def)
      apply(rename_tac a q1 ba q2)(*strict*)
      apply(clarsimp)
      apply(rename_tac q1 ba q2)(*strict*)
      apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def fill_def)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(rename_tac a w' a')(*strict*)
     apply(simp add: cropTol3l2_def cropTol3l2_single_def)
     apply(case_tac a)
      apply(rename_tac a w' a' q ba)(*strict*)
      apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def fill_def)
     apply(rename_tac a w' a' q1 ba q2)(*strict*)
     apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def fill_def)
    apply(rename_tac a)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(clarsimp)
    apply(rule fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
    apply(simp add: restrict_newignore_def new_post_sig_def)
    apply(rule_tac
      t="drop (length (ESplitItem_to (S1 ! length v))) (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (restrict_toberemovedX S1 ! Suc (length v))))"
      and s="X" for X
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(rule cropTol3l2_drop_butn_drop_and_crop)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc (length v)) (length v) = []")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply (metis Nat.lessI nat_seqEmpty)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(thin_tac "nat_seq (Suc (length v)) (length v) = []")
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "length (ESplitItem_ignore (S1 ! length v)) = length (restrict_toberemoved S1 ! (length v))")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_toberemoved_def enforceSuffix_def enforceSuffixS_def)
    apply(clarsimp)
    apply(simp add: takeB_def)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "ESplitItem_to (S1!length v) \<noteq> []")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(case_tac "ESplitItem_to (S1!length v) = []")
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac a)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
     apply(clarsimp)
     apply(erule_tac
      x="S1!length v"
      in ballE)
      apply(rename_tac a)(*strict*)
      apply(simp add: EValidSplitItem_def)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(subgoal_tac "PSplitItem_elem (restrict G' G (S1 @ S1') (Suc (length v)) ! length v) = (teB b)")
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def restrict_newelem_def)
     apply(clarsimp)
    apply(rename_tac a)(*strict*)
    apply(subgoal_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! length v) = []")
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def restrict_newignore_def)
     apply(clarsimp)
     apply(simp add: new_post_sig_def)
     apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (restrict_toberemovedX S1 ! Suc (length v))))=SSX" for SSX)
      apply(rename_tac a)(*strict*)
      prefer 2
      apply(rule drop_and_crop_length)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "length (restrict_toberemoved S1 ! length v) \<le> length (restrict_toberemovedX S1 ! Suc (length v))")
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(simp (no_asm) add: restrict_toberemovedX_def)
     apply(rule_tac
      t="(restrict_toberemoved S1 @ [tl (ESplitItem_to (last S1) @ ESplitItem_ignore (last S1))]) ! Suc (length v)"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(rule nth_append_beyond)
      apply(rule_tac
      t="length(restrict_toberemoved SSX)" for SSX
      in ssubst)
       apply(rename_tac a)(*strict*)
       apply(rule length_restrict_toberemoved)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="last S1"
      and s="S1!length v"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(rule last_nth3)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      j="length (ESplitItem_ignore (S1 ! length v))"
      in le_trans)
      apply(rename_tac a)(*strict*)
      apply(rule restrict_toberemoved_smaller_than_ignore)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(case_tac "ESplitItem_to (S1 ! length v)")
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a aa list)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
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
    apply(rule conjI)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule conjI)
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
      apply(rule_tac
      x="d"
      in exI)
      apply(rule_tac
      x="liftA (ESplitItem_to (S1 ! length v))"
      in exI)
      apply(simp add: option_to_list_def)
     apply(rename_tac a)(*strict*)
     apply(force)
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
    apply(rule_tac
      x="d"
      in exI)
    apply(simp add: option_to_list_def)
    apply(simp only: cfgLMMIP_def)
    apply(rule conjI)
     apply(rename_tac a d)(*strict*)
     apply(force)
    apply(rename_tac a d)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d)(*strict*)
     apply(simp add: cfgLMMIyX_def)
     apply(clarsimp)
     apply(subgoal_tac "ESplitItem_prods (S1 ! length v) = []")
      apply(rename_tac a d)(*strict*)
      prefer 2
      apply(rule applicable_with_empty_source)
      apply(force)
     apply(rename_tac a d)(*strict*)
     apply(force)
    apply(rename_tac a d)(*strict*)
    apply(simp add: cfgLMMPX_def)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' da c)(*strict*)
    apply(erule_tac
      x="length \<pi>'"
      in allE)
    apply(subgoal_tac "length \<pi>' <length (ESplitItem_prods (S1 ! length v))")
     apply(rename_tac a d \<pi>' da c)(*strict*)
     prefer 2
     apply(rule strict_prefix_length)
     apply(force)
    apply(rename_tac a d \<pi>' da c)(*strict*)
    apply(simp add: strict_prefix_def)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' da c ca)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (length \<pi>') = Some (pair e c)")
     apply(rename_tac a d \<pi>' da c ca)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      m="length(ESplitItem_prods (S1 ! length v))"
      in cfgLM.pre_some_position_is_some_position)
       apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
       apply(force)
      apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
     apply(subgoal_tac "length \<pi>' <length (ESplitItem_prods (S1 ! length v))")
      apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac a d \<pi>' da c ca e ea)(*strict*)
     apply(rule strict_prefix_length)
     apply(simp add: strict_prefix_def)
     apply(force)
    apply(rename_tac a d \<pi>' da c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' da c ca e cb)(*strict*)
    apply(case_tac cb)
    apply(rename_tac a d \<pi>' da c ca e cb cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d \<pi>' da c ca e cfg_confa)(*strict*)
    apply(rename_tac w)
    apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
    apply(subgoal_tac "w=teB b#c")
     apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
    apply(subgoal_tac "d (length \<pi>') = da (length \<pi>')")
     apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
     prefer 2
     apply(rule_tac
      ?\<pi>2.0="ca"
      in cfgLM_trans_der_coincide)
         apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
        apply(force)
       apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
       apply(force)
      apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
      apply(force)
     apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
     apply(force)
    apply(rename_tac a d \<pi>' da c ca e w)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac a)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(simp (no_asm) add: restrict_newto_def restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="restrict_toberemovedX S1 ! Suc (length v)"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(rule restrict_toberemovedX_last)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (ESplitItem_to (S1 ! length v)) - Suc 0 + length (restrict_toberemoved S1 ! length v)))"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(rule drop_and_crop_length)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac "ESplitItem_to (S1 ! length v)")
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(clarsimp)
   apply(simp add: butn_def)
   apply(simp add: drop_and_crop_def butn_def)
   apply(simp add: cropTol3l2_def)
   apply(case_tac aa)
    apply(rename_tac a aa list q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac a list q ba)(*strict*)
    apply(simp add: fillOptL_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def)
   apply(rename_tac a aa list q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list q1 ba q2)(*strict*)
   apply(simp add: fillOptL_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fillL_def appL_def fill_def)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x i)(*strict*)
   prefer 2
   apply(rule_tac
      i="Suc i"
      and G="G"
      in e_derivation_at_tail_exists)
                      apply(rename_tac x i)(*strict*)
                      apply(force)
                     apply(rename_tac x i)(*strict*)
                     apply(force)
                    apply(rename_tac x i)(*strict*)
                    apply(force)
                   apply(rename_tac x i)(*strict*)
                   apply(force)
                  apply(rename_tac x i)(*strict*)
                  apply(force)
                 apply(rename_tac x i)(*strict*)
                 apply(force)
                apply(rename_tac x i)(*strict*)
                apply(force)
               apply(rename_tac x i)(*strict*)
               apply(force)
              apply(rename_tac x i)(*strict*)
              apply(force)
             apply(rename_tac x i)(*strict*)
             apply(force)
            apply(rename_tac x i)(*strict*)
            apply(force)
           apply(rename_tac x i)(*strict*)
           apply(force)
          apply(rename_tac x i)(*strict*)
          apply(force)
         apply(rename_tac x i)(*strict*)
         apply(force)
        apply(rename_tac x i)(*strict*)
        apply(force)
       apply(rename_tac x i)(*strict*)
       apply(force)
      apply(rename_tac x i)(*strict*)
      apply(force)
     apply(rename_tac x i)(*strict*)
     apply(force)
    apply(rename_tac x i)(*strict*)
    apply(force)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule exE)+
  apply(rename_tac x i e_d)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e_d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e_d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d)(*strict*)
  apply(subgoal_tac "(S1 @ S1') ! i = S1!i")
   apply(rename_tac x i e_d p_d)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x i e_d p_d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(S1 @ S1') ! Suc i = S1!Suc i")
   apply(rename_tac x i e_d p_d)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x i e_d p_d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(S1 @ S1') ! length v = S1!length v")
   apply(rename_tac x i e_d p_d)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x i e_d p_d)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from (S1!i)")
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac x i e_d p_d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(erule_tac
      x="S1!i"
      in ballE)
    apply(rename_tac x i e_d p_d)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(subgoal_tac "S1!i \<in> set (butlast (S1 @ S1'))")
    apply(rename_tac x i e_d p_d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(thin_tac "S1 ! i \<notin> set (butlast (S1 @ S1'))")
   apply(subgoal_tac "S1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac x i e_d p_d)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(erule disjE)
    apply(rename_tac x i e_d p_d)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d p_d w' a')(*strict*)
   apply(rule_tac
      t="(w' @ [a']) ! i"
      and s="w'!i"
      in ssubst)
    apply(rename_tac x i e_d p_d w' a')(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac x i e_d p_d w' a')(*strict*)
   apply(rule in_butlast)
   apply(force)
  apply(rename_tac x i e_d p_d a)(*strict*)
  apply(case_tac "ESplitItem_from (S1 ! Suc i)")
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac x i e_d p_d a)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(erule_tac
      x="(S1@S1')!Suc i"
      in ballE)
    apply(rename_tac x i e_d p_d a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(subgoal_tac "(S1 @ S1') ! Suc i \<in> set (butlast (S1 @ S1'))")
    apply(rename_tac x i e_d p_d a)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(thin_tac "(S1 @ S1') ! Suc i \<notin> set (butlast (S1 @ S1'))")
   apply(subgoal_tac "S1'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac x i e_d p_d a)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(erule disjE)
    apply(rename_tac x i e_d p_d a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d a)(*strict*)
   apply(erule exE)+
   apply(rename_tac x i e_d p_d a w' a')(*strict*)
   apply(rule_tac
      t="S1'"
      and s="w'@[a']"
      in ssubst)
    apply(rename_tac x i e_d p_d a w' a')(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a w' a')(*strict*)
   apply(rule_tac
      t="butlast (S1 @ w' @ [a'])"
      in ssubst)
    apply(rename_tac x i e_d p_d a w' a')(*strict*)
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x i e_d p_d a w' a')(*strict*)
   apply(rule_tac
      t="(S1 @ w' @ [a']) ! Suc i"
      and s="(S1 @ w') ! Suc i"
      in ssubst)
    apply(rename_tac x i e_d p_d a w' a')(*strict*)
    apply(rule_tac
      t="S1 @ w' @ [a']"
      and s="(S1 @ w') @ [a']"
      in ssubst)
     apply(rename_tac x i e_d p_d a w' a')(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a w' a')(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac x i e_d p_d a w' a')(*strict*)
   apply(rule nth_mem)
   apply(force)
  apply(rename_tac x i e_d p_d a aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length v) ! i = SSX" for SSX)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa)(*strict*)
  apply(subgoal_tac "nat_seq 0 (length v) ! (Suc i) = SSX" for SSX)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa)(*strict*)
  apply(case_tac "ESplitItem_from ((S1 @ S1') ! length v)")
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(simp add: EValidSplit_def EValidSplit_producing_def)
   apply(clarsimp)
   apply(erule_tac
      x="(S1@S1')!length v"
      in ballE)
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(subgoal_tac "(S1 @ S1') ! length v \<in> set (butlast (S1 @ S1'))")
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(thin_tac "(S1 @ S1') ! length v \<notin> set (butlast (S1 @ S1'))")
   apply(subgoal_tac "S1'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac x i e_d p_d a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d a aa)(*strict*)
   apply(erule exE)+
   apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
   apply(rule_tac
      t="S1'"
      and s="w'@[a']"
      in ssubst)
    apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
   apply(rule_tac
      t="butlast (S1 @ w' @ [a'])"
      in ssubst)
    apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
   apply(rule_tac
      t="(S1 @ w' @ [a']) ! length v"
      and s="(S1 @ w') ! length v"
      in ssubst)
    apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
    apply(rule_tac
      t="S1 @ w' @ [a']"
      and s="(S1 @ w') @ [a']"
      in ssubst)
     apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac x i e_d p_d a aa w' a')(*strict*)
   apply(rule nth_mem)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(subgoal_tac "ESplitItem_to (S1!length v) \<noteq> []")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   prefer 2
   apply(case_tac "ESplitItem_to (S1!length v) = []")
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(clarsimp)
   apply(rule EValidSplit_DERIVED_terminal_produce_produces_to)
        apply(rename_tac x i e_d p_d a aa ab)(*strict*)
        apply(force)
       apply(rename_tac x i e_d p_d a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x i e_d p_d a aa ab)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(clarsimp)
    apply(erule_tac
      x="S1!length v"
      in ballE)
     apply(rename_tac x i e_d p_d a aa ab)(*strict*)
     apply(simp add: EValidSplitItem_def)
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (Some aa))\<rparr> (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ teB b # va\<rparr>)")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "cfgLMMIP G p_d (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(simp (no_asm) add: fillWithPreContext_def)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(simp (no_asm) add: option_to_list_def)
   apply(rule conjI)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(rule fillOpt_hd_and_last_back_state)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(rule_tac
      t="fillOptL (restrict_newignore S1 i) (last_back_state_if_l3_nonterminal (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
      and s="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
      in ssubst)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(rule fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
    apply(simp add: restrict_newignore_def new_post_sig_def)
    apply(rule cropTol3l2_drop_butn_drop_and_crop)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (Some aa))\<rparr> (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ teB b # va\<rparr>)")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "cfgLMMIP G p_d (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(rule_tac
      t="ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)"
      and s="fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
      in ssubst)
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(simp (no_asm) add: fillWithPreContext_def)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(subgoal_tac "restrict_toberemoved S1 ! length v=ESplitItem_ignore (S1 ! length v)")
    apply(rename_tac x i e_d a aa ab)(*strict*)
    prefer 2
    apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last SSS)" for SSS)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     prefer 2
     apply(rule_tac
      S="S1"
      in restrict_toberemoved_last_is_ignore)
     apply(force)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(rule_tac
      t="S1 ! length v"
      and s="last S1"
      in ssubst)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply (rule last_nth_prime)
     apply(force)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(rule_tac
      t="restrict_toberemoved S1 ! length v"
      and s="last (restrict_toberemoved S1)"
      in ssubst)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply (rule last_nth_prime)
     apply (metis gr0_conv_Suc length_restrict_toberemoved less_not_refl list.size(3))
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(subgoal_tac "restrict_newignore S1 (length v) = []")
    apply(rename_tac x i e_d a aa ab)(*strict*)
    prefer 2
    apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
    apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (restrict_toberemovedX S1 ! Suc (length v))))"
      in ssubst)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply(rule drop_and_crop_length)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="restrict_toberemovedX S1 ! Suc (length v)"
      in ssubst)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply(rule restrict_toberemovedX_last)
     apply(force)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(rule_tac
      t="length (restrict_newignore S1 (length v))"
      and s="0"
      in ssubst)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(clarsimp)
   apply(thin_tac "fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)")
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(thin_tac "cfgLMMP G e_d (liftA (option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)))")
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(rule ignore_parts_in_relation)
                apply(rename_tac x i e_d a aa ab)(*strict*)
                apply(force)
               apply(rename_tac x i e_d a aa ab)(*strict*)
               apply(force)
              apply(rename_tac x i e_d a aa ab)(*strict*)
              apply(fold suffix_def)
              apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
                apply(rename_tac x i e_d a aa ab)(*strict*)
                apply(force)
               apply(rename_tac x i e_d a aa ab)(*strict*)
               apply(force)
              apply(rename_tac x i e_d a aa ab)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a aa ab)(*strict*)
             apply(rule restrict_toberemoved_suffix)
              apply(rename_tac x i e_d a aa ab)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a aa ab)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a aa ab)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa ab)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab)(*strict*)
      apply(rule ESplitItem_ignore_decompose)
        apply(rename_tac x i e_d a aa ab)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab)(*strict*)
   apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab)(*strict*)
  apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (Some aa))\<rparr> (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ teB b # va\<rparr>)")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(simp add: fillWithPreContext_def)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def fillWithPreContext_def option_to_list_def)
  apply(clarsimp)
  apply(subgoal_tac "option_to_list (Some a) = [a]")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def fillWithPreContext_def option_to_list_def)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(thin_tac "option_to_list (Some a) = [a]")
  apply(subgoal_tac "option_to_list (Some aa) = [aa]")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def fillWithPreContext_def option_to_list_def)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(thin_tac "option_to_list (Some aa) = [aa]")
  apply(subgoal_tac "SSw=take SSn (ESplitItem_ignore (S1 ! Suc i))" for SSw SSn)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(rule append_take_drop_id_C)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ESplitItem_ignore (S1 ! Suc i)")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule_tac
    t="(fillOpt (hd (cropTol3l2 (a # restrict_newignore S1 i))) (last_back_state_if_l3_nonterminal [a]))"
    and s="a"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(subgoal_tac "restrict_newignore S1 i=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(erule disjE)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(clarsimp)
   apply(simp add: fillOpt_def)
   apply(case_tac "last_back_state_if_l3_nonterminal [a]")
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i e_d p_d aa ab)(*strict*)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def)
    apply(case_tac "PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)")
     apply(rename_tac x i e_d p_d aa ab q ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac x i e_d p_d aa ab q1 ba q2)(*strict*)
    apply(clarsimp)
   apply(rename_tac x i e_d p_d a aa ab ac)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d p_d aa ab ac)(*strict*)
   apply(case_tac "PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)")
    apply(rename_tac x i e_d p_d aa ab ac q ba)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fill_def)
   apply(rename_tac x i e_d p_d aa ab ac q1 ba q2)(*strict*)
   apply(simp add: cropTol3l2_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fill_def)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab w' a')(*strict*)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fill_def fillOpt_def)
  apply(case_tac a)
   apply(rename_tac x i e_d p_d a aa ab w' a' q ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab w' a' q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d aa ab w' a' q1 ba q2)(*strict*)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def last_back_state_if_l3_nonterminal_def fill_def fillOpt_def)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule_tac
    t="fillOptL (restrict_newignore S1 i) (last_back_state_if_l3_nonterminal (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
    and s="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(subgoal_tac "nat_seq (Suc i) (length v) = (Suc i) # nat_seq (Suc (Suc i)) (length v)")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(rule nat_seq_pullout)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="foldl (@) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "cfgLMMIP G p_d (teA aa # liftA (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) ((liftA (take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl(ESplitItem_to (S1 ! length v))@ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)))))")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(rule_tac
    t="(liftA (take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl(ESplitItem_to (S1 ! length v))@ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))"
    and s="liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)))"
    in ssubst)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(simp add: liftA_commutes_over_concat)
  apply(rule sym)
  apply(simp (no_asm) add: restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (restrict_toberemovedX S1 ! Suc (length v))))"
    in ssubst)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(rule restrict_toberemovedX_last)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_to (S1 ! length v)")
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab ac list)(*strict*)
  apply(clarsimp)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule fillOptL_with_take)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(thin_tac "cfgLMMIP G p_d (teA aa # liftA (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLMMIy G d (liftA (a # drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) (liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))) []")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(rule e_derivation_can_be_embedded_minimally_hlp3)
                    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
                    apply(force)
                   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
                   apply(force)
                  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
                  apply(force)
                 apply(rename_tac x i e_d p_d a aa ab)(*strict*)
                 apply(force)
                apply(rename_tac x i e_d p_d a aa ab)(*strict*)
                apply(force)
               apply(rename_tac x i e_d p_d a aa ab)(*strict*)
               apply(force)
              apply(rename_tac x i e_d p_d a aa ab)(*strict*)
              apply(force)
             apply(rename_tac x i e_d p_d a aa ab)(*strict*)
             apply(force)
            apply(rename_tac x i e_d p_d a aa ab)(*strict*)
            apply(force)
           apply(rename_tac x i e_d p_d a aa ab)(*strict*)
           apply(force)
          apply(rename_tac x i e_d p_d a aa ab)(*strict*)
          apply(force)
         apply(rename_tac x i e_d p_d a aa ab)(*strict*)
         apply(force)
        apply(rename_tac x i e_d p_d a aa ab)(*strict*)
        apply(force)
       apply(rename_tac x i e_d p_d a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x i e_d p_d a aa ab)(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_interline_def)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(erule_tac
    x="i"
    in allE)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal [a]) = a")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)) = ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)) = ESplitItem_ignore (S1 ! i)")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOpt (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal [aa]) = aa")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) = take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule restrict_toberemovedX_last)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule_tac
    t="drop i (take (length v) fw)"
    and s=" fw!i#drop (Suc i) (take (length v) fw) "
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule e_derivation_at_tail_exists_hlp1)
    apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
    apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
   apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
   apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="foldl (@) (fw ! i) (drop (Suc i) (take (length v) fw))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(clarsimp)
  apply(simp add: liftB_commutes_over_concat)
  apply(rule_tac
    t="butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))"
    and s=" butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)) "
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule double_suffix_butn_decomposition)
   apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
   apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
     apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
    apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(subgoal_tac " \<forall>w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3. (w2=aa # (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) \<longrightarrow> (\<alpha>2=foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]) \<longrightarrow> (w2'=take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))) \<longrightarrow> (w1= a # (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) \<longrightarrow> (w1'=drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))) \<longrightarrow> (\<alpha>1=fw ! i) \<longrightarrow> (w3= a # (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))) \<longrightarrow> (w3'=take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))) \<longrightarrow> (\<exists>R2 R1. set (R1 @ R2) \<subseteq> cfg_nonterminals G \<and> (R1 = [] \<or> R2 = []) \<and> CON [] (liftA R1) (liftA w1) = (liftA w3) \<and> CON [] (liftA R1) (liftB \<alpha>1@liftA w1') = CON (liftB \<alpha>1) (liftA R2) (liftA w2) \<and> CON (liftB \<alpha>1) (liftA R2) ((liftB \<alpha>2)@(liftA w2')) = (liftB(\<alpha>1@\<alpha>2))@(liftA w3')) ")
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  prefer 2
  apply(rule allI)+
  apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(rule impI)+
  apply(rule_tac
    x="butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))"
    in exI)
  apply(thin_tac "cfgLMMIP G p_d (teA aa # liftA (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ [teB b]) (liftA (take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(thin_tac "cfgLMMIy G d (teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) (liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))) []")
  apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i)) \<or> SSX" for SSX)
   apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
   prefer 2
   apply(rule_tac
    b="option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(erule disjE)
  (*strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i))*)
   apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
   apply(thin_tac "ESplitItem_from (S1 ! length v) = Some ab")
   apply(simp add: strict_prefix_def)
   apply(rename_tac x i e_d a aa w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(case_tac c)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(blast)
   apply(rename_tac x i e_d a aa c ab list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d a aa ab list)(*strict*)
   apply(rename_tac w)
   apply(rename_tac x i e_d a aa ab w)(*strict*)
   apply(subgoal_tac "ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i) = (ESplitItem_elim (S1 ! Suc i) @ ab # w) @ ESplitItem_ignore (S1 ! i)")
    apply(rename_tac x i e_d a aa ab w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i e_d a aa ab w)(*strict*)
   apply(simp (no_asm_use))
   apply(clarsimp)
   apply(subgoal_tac "aa = ab \<and> ESplitItem_ignore (S1 ! Suc i) = w @ ESplitItem_ignore (S1 ! i)")
    apply(rename_tac x i e_d a aa ab w)(*strict*)
    prefer 2
    apply(simp add: option_to_list_def)
   apply(rename_tac x i e_d a aa ab w)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(thin_tac "option_to_list (Some ab) = [ab]")
   apply(rule_tac
    t="ESplitItem_to (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ ab # w"
    in ssubst)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(simp (no_asm))
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
   apply(clarsimp)
   apply(rule_tac
    x="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    in exI)
   apply(clarsimp)
   apply(simp add: CON_def)
   apply(simp add: liftB_commutes_over_concat)
   apply(rule_tac
    t="[teA a]"
    and s="teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
    in ssubst)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ ab # w"
    in ssubst)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(simp add: liftA_commutes_over_concat)
   apply(rule conjI)
    apply(rename_tac x i e_d a ab w)(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac x i e_d a ab w)(*strict*)
     prefer 2
     apply(rule conjI)
      apply(rename_tac x i e_d a ab w)(*strict*)
      prefer 2
      apply(subgoal_tac "liftA (w @ (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))) = liftA (take (length (restrict_newignore S1 (Suc i))) w @ (take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i))) @ (butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))))")
       apply(rename_tac x i e_d a ab w)(*strict*)
       apply(simp add: liftA_commutes_over_concat)
      apply(rename_tac x i e_d a ab w)(*strict*)
      apply(rule_tac
    f="liftA"
    in arg_cong)
      apply(rename_tac ignoreDiffiSi)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s=" butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! Suc i)) "
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
       apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)) (length (restrict_toberemovedX S1 ! Suc i)))"
    in ssubst)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule drop_and_crop_length)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule restrict_toberemovedX_last)
        apply(force)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc i"
    in ssubst)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
        apply(force)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(simp add: butn_def)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) ignoreDiffiSi @ take (length (restrict_newignore S1 (Suc i)) - length ignoreDiffiSi) (ESplitItem_ignore (S1 ! i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))"
    and s="(take (length (restrict_newignore S1 (Suc i))) ignoreDiffiSi @ take (length (restrict_newignore S1 (Suc i)) - length ignoreDiffiSi) (ESplitItem_ignore (S1 ! i))) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="(take (length (restrict_newignore S1 (Suc i))) ignoreDiffiSi @ take (length (restrict_newignore S1 (Suc i)) - length ignoreDiffiSi) (ESplitItem_ignore (S1 ! i)))"
    and s="(take (length (restrict_newignore S1 (Suc i))) (ignoreDiffiSi @ ESplitItem_ignore (S1 ! i)))"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="ignoreDiffiSi @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(rule_tac
    m="length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_newignore S1 (Suc i))"
    in take_butn2)
       apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
       apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! Suc i) @ ESplitItem_ignore (S1 ! Suc i)) (length (restrict_toberemovedX S1 ! Suc (Suc i))))"
    in ssubst)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule drop_and_crop_length)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="ignoreDiffiSi"
    and s="butn (ESplitItem_ignore (S1 ! Suc i)) (length(ESplitItem_ignore (S1 ! i)))"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(simp add: butn_def)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule_tac
    t="butn (ESplitItem_ignore (S1 ! Suc i)) (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_newignore S1 (Suc i)))"
    and s="butn (ESplitItem_ignore (S1 ! Suc i)) (length (restrict_toberemovedX S1 ! (Suc (Suc i))))"
    in ssubst)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def butn_def)
       apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! Suc i) @ ESplitItem_ignore (S1 ! Suc i)) (length (restrict_toberemovedX S1 ! Suc (Suc i))))"
    in ssubst)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule drop_and_crop_length)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(simp (no_asm))
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(rule merging_lemma1_prime)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
              apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
             apply(force)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(rule_tac
    t="restrict_toberemoved S1 ! Suc i"
    in subst)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(rule restrict_toberemoved_restrict_toberemoved_suffix_X2)
               apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
               apply(force)
              apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
             apply(force)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(rule_tac
    t="last S1"
    and s="S1!length v"
    in ssubst)
             apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
             apply(rule last_nth3)
             apply(force)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [ab]"
    in restrict_toberemoved_direct_computation)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(case_tac "Suc i<length v")
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(subgoal_tac "EValidSplit_interlineX (S1 ! Suc i) (S1 ! Suc (Suc i))")
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           prefer 2
           apply(simp add: EValidSplit_def EValidSplit_interline_def)
           apply(clarsimp)
           apply(erule_tac
    x="Suc i"
    in allE)
           apply(erule impE)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(rule_tac
    t="S1!Suc i"
    and s="(S1@S1')!Suc i"
    in subst)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(rule nth_append_1)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(rule_tac
    t="S1!Suc (Suc i)"
    and s="(S1@S1')!Suc (Suc i)"
    in subst)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(rule nth_append_1)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule_tac
    t="min (Suc (Suc i)) (length S1 - Suc 0)"
    and s="Suc(Suc i)"
    in ssubst)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(simp (no_asm_use) only: EValidSplit_interlineX_def)
          apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (Suc i)"
    in ssubst)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! Suc i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc (Suc i)) @ option_to_list (ESplitItem_from (S1 ! Suc (Suc i)))"
    in restrict_toberemoved_direct_computation)
            apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(subgoal_tac "Suc i = length v")
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (Suc i)"
    in ssubst)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule restrict_toberemovedX_last)
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(rule_tac
    t="takeB (length (tl (ESplitItem_to (S1 ! Suc i) @ ESplitItem_ignore (S1 ! Suc i)))) (ESplitItem_ignore (S1 ! Suc i))"
    and s="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(simp add: takeB_def)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(subgoal_tac "restrict_toberemoved S1 ! length v=ESplitItem_ignore (S1 ! length v)")
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          prefer 2
          apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last SSS)" for SSS)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           prefer 2
           apply(rule_tac
    S="S1"
    in restrict_toberemoved_last_is_ignore)
           apply(force)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule_tac
    t="S1 ! length v"
    and s="last S1"
    in ssubst)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply (metis last_nth2 append_Nil diff_Suc_Suc diff_self_eq_0 minus_nat.diff_0 rev_rev_ident take_0 take_drop_rev3 take_drop_split)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(rule_tac
    t="restrict_toberemoved S1 ! length v"
    and s="last (restrict_toberemoved S1)"
    in ssubst)
           apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
           apply (metis last_nth_prime restrict_toberemoved_at_last)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(simp add: takeB_def)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
          apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
         apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab ignoreDiffiSi)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(simp add: restrict_newignore_def new_post_sig_def)
     apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)) (length (restrict_toberemovedX S1 ! Suc i)))"
    in ssubst)
      apply(rename_tac x i e_d a ab w)(*strict*)
      apply(rule drop_and_crop_length)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(subgoal_tac "X" for X)
      apply(rename_tac x i e_d a ab w)(*strict*)
      prefer 2
      apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [ab]"
    and S="S1"
    and i="i"
    in restrict_toberemoved_direct_computation)
        apply(rename_tac x i e_d a ab w)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac x i e_d a ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc i"
    in ssubst)
      apply(rename_tac x i e_d a ab w)(*strict*)
      apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
      apply(force)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(simp add: butn_def takeB_def)
     apply(clarsimp)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(rule_tac
    B="set (restrict_toberemoved S1 ! Suc i)"
    in subset_trans)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(rule set_butn_subset)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac x i e_d a ab w)(*strict*)
     prefer 2
     apply(rule_tac
    i="Suc i"
    and k="Suc i"
    in ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac x i e_d a ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a ab w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(rule_tac
    B="set (ESplitItem_ignore (S1 ! Suc i))"
    in subset_trans)
     apply(rename_tac x i e_d a ab w)(*strict*)
     apply(simp only: suffix_def)
     apply(erule exE)+
     apply(rename_tac x i e_d a ab w c)(*strict*)
     apply(rule_tac
    t="w @ ESplitItem_ignore (S1 ! i)"
    and s="c @ restrict_toberemoved S1 ! Suc i"
    in ssubst)
      apply(rename_tac x i e_d a ab w c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a ab w c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
     apply(rename_tac x i e_d a ab w)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(thin_tac "ESplitItem_ignore (S1 ! Suc i) = w @ ESplitItem_ignore (S1 ! i)")
    apply(thin_tac "ESplitItem_ignore (S1 ! Suc i) \<sqsupseteq> (restrict_toberemoved S1 ! Suc i)")
    apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(rule_tac
    B="set ((ESplitItem_ignore (S1 ! i)))"
    in subset_trans)
    apply(rename_tac x i e_d a ab w)(*strict*)
    apply(rule List.set_take_subset)
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(subgoal_tac "EValidSplitItem G (S1!i)")
    apply(rename_tac x i e_d a ab w)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(rename_tac x i e_d a ab w)(*strict*)
   apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(rename_tac x i e_d p_d a aa ab d w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac x i e_d a aa ab w1 w2 w1' \<alpha>1 \<alpha>2 w2' w3' w3)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
   apply(rename_tac x i e_d a aa ab c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(rule_tac
    t="drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_to (S1 ! i) @ c)"
    and s="c"
    in ssubst)
   apply(rename_tac x i e_d a aa ab c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(rule_tac
    t="drop (length (ESplitItem_to (S1 ! i) @ c)) (ESplitItem_to (S1 ! i))"
    and s="[]"
    in ssubst)
   apply(rename_tac x i e_d a aa ab c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(thin_tac "ESplitItem_from (S1 ! length v) = Some ab")
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)) (length (restrict_toberemovedX S1 ! Suc i)))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab c)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac x i e_d a aa ab c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! Suc i) @ ESplitItem_ignore (S1 ! Suc i)) (length (restrict_toberemovedX S1 ! Suc (Suc i))))"
    in ssubst)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(rule drop_and_crop_length)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(clarsimp)
  apply(simp add: liftA_commutes_over_concat CON_def)
  apply(simp add: liftB_commutes_over_concat CON_def)
  apply(rule_tac
    x=" aa # (take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i))) @ (butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)))"
    in exI)
  apply(rule conjI)
   apply(rename_tac x i e_d a aa c)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac x i e_d a aa c)(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac x i e_d a aa c)(*strict*)
     prefer 2
     apply(simp add: liftA_commutes_over_concat CON_def)
     apply(rule_tac
    t="liftA c @ teA aa # liftA (take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i))) @ liftA (butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)))"
    and s="liftA(c@aa#(take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i)))@(butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))))"
    in ssubst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(simp add: liftA_commutes_over_concat)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    f="liftA"
    in arg_cong)
     apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
     apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ c @ aa # take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))"
    and s="(ESplitItem_to (S1 ! i) @ c) @ (aa # take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)))"
    in ssubst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ c"
    and s="ESplitItem_elim (S1 ! Suc i)"
    in ssubst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    v="drop (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemoved S1 ! Suc i)) (ESplitItem_ignore (S1 ! i))"
    in append_injr)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    t="(ESplitItem_to (S1 ! i) @ take (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_ignore (S1 ! i))) @ drop (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemoved S1 ! Suc i)) (ESplitItem_ignore (S1 ! i))"
    and s="ESplitItem_to (S1 ! i) @ESplitItem_ignore (S1 ! i)"
    in subst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(simp (no_asm))
      apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc i"
    in ssubst)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
       apply(force)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule_tac
    P="\<lambda>X. (ESplitItem_elim (S1 ! Suc i) @ aa # take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))) @ drop (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemoved S1 ! Suc i)) (ESplitItem_ignore (S1 ! i)) = ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ X"
    and s=" take (length (ESplitItem_ignore (S1 ! Suc i)) - length (restrict_toberemovedX S1 ! Suc (Suc i))) (ESplitItem_ignore (S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)) @ drop (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemoved S1 ! Suc i)) (ESplitItem_ignore (S1 ! i))"
    in ssubst)
      apply(rename_tac x i e_d a aa c)(*strict*)
      prefer 2
      apply(simp add: option_to_list_def)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule merging_lemma2_prime)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
            apply(rename_tac x i e_d a aa c)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a aa c)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(rule_tac
    t="restrict_toberemoved S1 ! Suc i"
    in subst)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(rule restrict_toberemoved_restrict_toberemoved_suffix_X2)
             apply(rename_tac x i e_d a aa c)(*strict*)
             apply(force)
            apply(rename_tac x i e_d a aa c)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a aa c)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(rule_tac
    t="last S1"
    and s="S1!length v"
    in ssubst)
           apply(rename_tac x i e_d a aa c)(*strict*)
           apply(rule last_nth3)
           apply(force)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [aa]"
    in restrict_toberemoved_direct_computation)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(simp add: option_to_list_def)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(case_tac "Suc i<length v")
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(subgoal_tac "EValidSplit_interlineX (S1 ! Suc i) (S1 ! Suc (Suc i))")
         apply(rename_tac x i e_d a aa c)(*strict*)
         prefer 2
         apply(simp add: EValidSplit_def EValidSplit_interline_def)
         apply(clarsimp)
         apply(erule_tac
    x="Suc i"
    in allE)
         apply(erule impE)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(rule_tac
    t="S1!Suc i"
    and s="(S1@S1')!Suc i"
    in subst)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(rule nth_append_1)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(rule_tac
    t="S1!Suc (Suc i)"
    and s="(S1@S1')!Suc (Suc i)"
    in subst)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(rule nth_append_1)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (Suc i)"
    in ssubst)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(rule restrict_toberemovedX_equals_restrict_toberemoved)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule_tac
    t="min (Suc (Suc i)) (length v)"
    and s="Suc(Suc i)"
    in ssubst)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(simp (no_asm_use) only: EValidSplit_interlineX_def)
        apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! Suc i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc (Suc i)) @ option_to_list (ESplitItem_from (S1 ! Suc (Suc i)))"
    in restrict_toberemoved_direct_computation)
          apply(rename_tac x i e_d a aa c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(subgoal_tac "Suc i = length v")
        apply(rename_tac x i e_d a aa c)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(rule_tac
    t="min (Suc (Suc i)) (length v)"
    and s="length S1-Suc 0"
    in ssubst)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "restrict_toberemoved S1 ! length v=ESplitItem_ignore (S1 ! length v)")
        apply(rename_tac x i e_d a aa c)(*strict*)
        prefer 2
        apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last SSS)" for SSS)
         apply(rename_tac x i e_d a aa c)(*strict*)
         prefer 2
         apply(rule_tac
    S="S1"
    in restrict_toberemoved_last_is_ignore)
         apply(force)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule_tac
    t="S1 ! length v"
    and s="last S1"
    in ssubst)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply (metis last_nth2 append_Nil diff_Suc_Suc diff_self_eq_0 minus_nat.diff_0 rev_rev_ident take_0 take_drop_rev3 take_drop_split)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule_tac
    t="restrict_toberemoved S1 ! length v"
    and s="last (restrict_toberemoved S1)"
    in ssubst)
         apply(rename_tac x i e_d a aa c)(*strict*)
         apply (metis last_nth_prime restrict_toberemoved_at_last)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(rule restrict_toberemovedX_last)
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(simp add: takeB_def)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
        apply(rename_tac x i e_d a aa c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac x i e_d a aa c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(clarsimp)
    apply(simp add: butn_def)
    apply(clarsimp)
    apply(subgoal_tac "restrict_toberemoved S1 ! i =restrict_toberemoved S1 ! (Suc i)")
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(rule_tac
    w="c@option_to_list (Some aa)"
    in restrict_toberemoved_equal)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ c @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    and s="(ESplitItem_to (S1 ! i) @ c) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(rule_tac
    B="set (restrict_toberemoved S1 ! Suc i)"
    in subset_trans)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(rule set_butn_subset)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x i e_d a aa c)(*strict*)
    prefer 2
    apply(rule_tac
    i="Suc i"
    and k="Suc i"
    in ESplitItem_ignore_restrict_toberemoved_suffix)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(rule_tac
    B="set (ESplitItem_ignore (S1 ! Suc i))"
    in subset_trans)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(simp only: suffix_def)
    apply(erule exE)+
    apply(rename_tac x i e_d a aa c ca)(*strict*)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    and s="ca @ restrict_toberemoved S1 ! Suc i"
    in ssubst)
     apply(rename_tac x i e_d a aa c ca)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa c ca)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
    apply(rename_tac x i e_d a aa c)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(rule_tac
    B="set (aa # (ESplitItem_ignore (S1 ! Suc i)) @ (restrict_toberemoved S1 ! Suc i) )"
    in subset_trans)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(simp (no_asm))
   apply(rule conjI)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(rule_tac
    B="set ((ESplitItem_ignore (S1 ! Suc i)) )"
    in subset_trans)
     apply(rename_tac x i e_d a aa c)(*strict*)
     apply(rule List.set_take_subset)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(rule_tac
    B="set (restrict_toberemoved S1 ! Suc i)"
    in subset_trans)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(rule set_butn_subset)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(rule_tac
    B="set (aa # (ESplitItem_ignore (S1 ! Suc i)) )"
    in subset_trans)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(simp (no_asm))
   apply(rule conjI)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x i e_d a aa c)(*strict*)
    prefer 2
    apply(rule_tac
    i="Suc i"
    and k="Suc i"
    in ESplitItem_ignore_restrict_toberemoved_suffix)
      apply(rename_tac x i e_d a aa c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x i e_d a aa c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c)(*strict*)
   apply(simp only: suffix_def)
   apply(erule exE)+
   apply(rename_tac x i e_d a aa c ca)(*strict*)
   apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    and s="ca @ restrict_toberemoved S1 ! Suc i"
    in ssubst)
    apply(rename_tac x i e_d a aa c ca)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa c ca)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
   apply(rename_tac x i e_d a aa c)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i e_d a aa c)(*strict*)
  apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d p_d a aa ab d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
  prefer 2
  apply(rule_tac
    ?w2.0="aa # (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))) "
    and ?\<alpha>2.0="foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b]"
    and ?w2'.0="take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))"
    and ?w1.0="a # (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
    and ?w1'.0="drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))"
    and ?\<alpha>1.0="fw ! i"
    and ?w3.0="a # (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))"
    and ?w3'.0="take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i))"
    and G="G"
    and ?R1.0="R1"
    and ?R2.0="R2"
    and ?d1.0="d"
    and ?d2.0="p_d"
    and ?\<pi>1.0="ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))"
    and ?\<pi>2.0="ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
    in cfgLMMIy_cfgLMMIP_concatenation)
            apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
            apply(simp add: split_TSstructure_def)
           apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
           prefer 6
           apply(simp add: liftB_commutes_over_concat)
          apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
          apply(force)
         apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
         apply(force)
        apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
        prefer 4
        apply(force)
       apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
     prefer 4
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
    prefer 2
    apply(case_tac "ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))")
     apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
     prefer 2
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 ac list)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplitItem G (S1!i)")
     apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
     prefer 2
     apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
    apply(simp only: EValidSplitItem_def EValidSplitItem_gen_def)
    apply(clarsimp)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(case_tac "ESplitItem_elem (S1 ! i)")
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(clarsimp)
     apply(simp add: EValidSplit_def EValidSplit_producing_def)
     apply(clarsimp)
     apply(erule_tac
    x="S1!i"
    in ballE)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(subgoal_tac "S1 ! i \<in> set (butlast (S1 @ S1'))")
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(thin_tac "S1 ! i \<notin> set (butlast (S1 @ S1'))")
     apply(subgoal_tac "S1'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(erule_tac
    P="S1' = []"
    in disjE)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(erule exE)+
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
     apply(rule_tac
    t="S1'"
    and s="w'@[a']"
    in ssubst)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
     apply(rule_tac
    t="butlast (S1 @ w' @ [a'])"
    and s="S1 @ w'"
    in ssubst)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
    apply(clarsimp)
    apply(erule_tac
    x="i"
    in allE)
    apply(clarsimp)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(case_tac "fw!i")
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "ESplitItem_elem (S1 ! i) = Some (SSv ! SSn)" for SSv SSn)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
     prefer 2
     apply(rule Esplit_signature_take_prefix_closureise)
       apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
   prefer 2
   apply(case_tac "ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))")
    apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
    prefer 2
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 ac list)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
    apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
    prefer 2
    apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
   apply(simp only: EValidSplitItem_def EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(case_tac "ESplitItem_elem (S1 ! Suc i)")
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_def EValidSplit_producing_def)
    apply(clarsimp)
    apply(erule_tac
    x="S1!Suc i"
    in ballE)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(subgoal_tac "S1 ! Suc i \<in> set (butlast (S1 @ S1'))")
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(thin_tac "S1 ! Suc i \<notin> set (butlast (S1 @ S1'))")
    apply(subgoal_tac "S1'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(erule_tac
    P="S1' = []"
    in disjE)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(erule exE)+
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
    apply(rule_tac
    t="S1'"
    and s="w'@[a']"
    in ssubst)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
    apply(rule_tac
    t="butlast (S1 @ w' @ [a'])"
    and s="S1 @ w'"
    in ssubst)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da w' a')(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac)(*strict*)
   apply(clarsimp)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
   apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
   apply(clarsimp)
   apply(erule_tac
    x="Suc i"
    in allE)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(erule impE)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
   apply(clarsimp)
   apply(case_tac "fw!Suc i")
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_elem (S1 ! Suc i) = Some (SSv ! SSn)" for SSv SSn)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
    prefer 2
    apply(rule Esplit_signature_take_prefix_closureise)
      apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
     apply(force)
    apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
    apply(force)
   apply(rename_tac x i e_d p_d a aa ab d R2 R1 da ac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1)(*strict*)
  apply(erule exE)+
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(rule_tac
    x="d3"
    in exI)
  apply(rule_tac
    t="(teA a # liftA (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
    and s="(liftA (a # take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  apply(rule_tac
    t="liftA (fillOptL (restrict_newto S1 (length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)))"
    and s="liftA (take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ butn (restrict_toberemoved S1 ! Suc i) (length (restrict_toberemoved S1 ! i)))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(clarsimp)
  apply(simp (no_asm) add: restrict_newto_def restrict_newignore_def new_post_sig_def)
  apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(rule restrict_toberemovedX_last)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="length (drop_and_crop (ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)) (length (ESplitItem_to (S1 ! length v)) - Suc 0 + length (ESplitItem_ignore (S1 ! length v))))"
    in ssubst)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(rule drop_and_crop_length)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_to (S1 ! length v)")
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3)(*strict*)
  apply(force)
  apply(rename_tac x i e_d p_d a aa ab d R2 R1 d3 ac list)(*strict*)
  apply(clarsimp)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule fillOptL_with_take)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(rule conjI)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "cfgLMMIP G p_d (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (Some aa))\<rparr> (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ teB b # va\<rparr>)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(subgoal_tac "cfgLMMIP G p_da (liftA([a])) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) (liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b])) (liftA(take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v))@tl (ESplitItem_to (S1 ! length v)) @butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  prefer 2
  apply(rule_tac
    t="[a]"
    and s="(fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (option_to_list (Some a))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))))"
    in ssubst)
   apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
   apply(simp add: fillWithPreContext_def)
   apply(rename_tac x i e_d a aa ab p_da)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x i e_d a aa ab p_da)(*strict*)
    apply(simp add: option_to_list_def)
    apply(case_tac a)
     apply(rename_tac x i e_d a aa ab p_da q ba)(*strict*)
     apply(simp add: fillOpt_def cropTol3l2_def last_back_state_if_l3_nonterminal_def cropTol3l2_single_def)
    apply(rename_tac x i e_d a aa ab p_da q1 ba q2)(*strict*)
    apply(simp add: fillOpt_def cropTol3l2_def last_back_state_if_l3_nonterminal_def cropTol3l2_single_def fill_def)
   apply(rename_tac x i e_d a aa ab p_da)(*strict*)
   apply(simp add: fillOptL_def fillOpt_def cropTol3l2_def last_back_state_if_l3_nonterminal_def cropTol3l2_single_def fill_def)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(rule_tac
    t="(liftA(take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v))@tl (ESplitItem_to (S1 ! length v)) @butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))"
    and s="(liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v))) (ESplitItem_to (S1 ! length v)))) @tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))"
    in ssubst)
   apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
   prefer 2
   apply(rule_tac
    t="fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v))) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))"
    and s="(fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i)))"
    in ssubst)
    apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i e_d a aa ab p_da)(*strict*)
    apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
    apply(clarsimp)
    apply(simp only: restrict_newto_def new_post_sig_def)
    apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
     apply(rename_tac x i e_d a aa ab p_da)(*strict*)
     apply(rule restrict_toberemovedX_last)
     apply(force)
    apply(rename_tac x i e_d a aa ab p_da)(*strict*)
    apply(simp add: drop_and_crop_def butn_def)
    apply(case_tac "ESplitItem_to (S1 ! length v)")
     apply(rename_tac x i e_d a aa ab p_da)(*strict*)
     apply(clarsimp)
    apply(rename_tac x i e_d a aa ab p_da ac list)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_def)
   apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
   apply(force)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(rule_tac
    f="liftA"
    in arg_cong)
  apply(simp (no_asm))
  apply(rule sym)
  apply(simp only: restrict_newto_def new_post_sig_def)
  apply(rule_tac
    t="restrict_toberemovedX S1 ! Suc (length v)"
    in ssubst)
   apply(rename_tac x i e_d a aa ab p_da)(*strict*)
   apply(rule restrict_toberemovedX_last)
   apply(force)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(case_tac "ESplitItem_to (S1 ! length v)")
   apply(rename_tac x i e_d a aa ab p_da)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da ac list)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rule_tac
    t="[cropTol3l2_single ac]"
    and s="cropTol3l2 [ ac]"
    in ssubst)
   apply(rename_tac x i e_d a aa ab p_da ac list)(*strict*)
   apply(simp add: cropTol3l2_def)
  apply(rename_tac x i e_d a aa ab p_da ac list)(*strict*)
  apply(rule fillOptL_cropTol3l2_last_back_state_if_l3_nonterminal)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "cfgLMMIP G p_da (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (option_to_list (Some a))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) (liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(rule_tac
    x="p_da"
    in exI)
  apply(rule_tac
    x="liftA (take (length (restrict_newto S1 (length v))) (ESplitItem_to (S1 ! length v)) @tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i)))"
    in exI)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(simp add: cfgLMMIP_def)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac x i e_d p_d a aa ab)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "cfgLMMIP G p_d (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))))) (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop (Suc i) (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i))))")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (option_to_list (Some aa))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)))) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! Suc i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i)) = ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (option_to_list (Some a))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)) = option_to_list (Some a) @ ESplitItem_ignore (S1 ! i)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i)) @ drop (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)) = ESplitItem_to (S1 ! length v) @ ESplitItem_ignore (S1 ! length v)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(case_tac "restrict_newignore S1 (Suc i) \<noteq> []")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) = [] \<longrightarrow> (\<exists>e_d va. cfgLM.trans_der G e_d \<lparr>cfg_conf = liftA (option_to_list (Some aa))\<rparr> (ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) \<lparr>cfg_conf = liftB (foldl (@) [] (drop (Suc i) (take (length v) fw))) @ teB b # va\<rparr>)")
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(erule impE)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(subgoal_tac "nat_seq (Suc i) (length v) = Suc i#nat_seq (Suc (Suc i)) (length v)")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  prefer 2
  apply(rule nat_seq_pullout)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "nat_seq (Suc i) (length v) = Suc i # nat_seq (Suc (Suc i)) (length v)")
  apply(rule_tac
    t="foldl (@) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="drop i (take (length v) fw)"
    and s=" fw!i#drop (Suc i) (take (length v) fw) "
    in ssubst)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(rule e_derivation_at_tail_exists_hlp1)
    apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
    apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
   apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
   apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="foldl (@) (fw ! i) (drop (Suc i) (take (length v) fw))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  apply(rule_tac
    t=" (fillOptL (restrict_newignore S1 i) (last_back_state_if_l3_nonterminal (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))))"
    and s="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(rule_tac
    n="length (restrict_toberemovedX S1 ! Suc i)"
    in fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  prefer 2
  apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
    and s="fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(rule sym)
   apply(rule_tac
    n="length (restrict_toberemovedX S1 ! Suc(Suc i))"
    in fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
   apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr>")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  prefer 2
  apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))"
    and s="fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
   apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
   apply(clarsimp)
   apply(rule sym)
   apply(rule_tac
    n="length (restrict_toberemovedX S1 ! Suc(Suc i))"
    in fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
   apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr>")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLMMIy G d (liftA (a # drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) (liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))) []")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  prefer 2
  apply(rule e_derivation_can_be_embedded_minimally_hlp3)
                    apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
                    apply(force)
                   apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
                   apply(force)
                  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
                  apply(force)
                 apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
                 apply(force)
                apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
                apply(force)
               apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
               apply(force)
              apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
             apply(force)
            apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(thin_tac "cfgLMMIP G p_da (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (option_to_list (Some a))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))) (liftB (foldl (@) [] (drop i (take (length v) fw))) @ [teB b]) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))")
  apply(rename_tac x i e_d a aa ab p_da e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(simp add: cfgLMMIy_def)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_interline_def)
  apply(clarsimp)
  apply(erule_tac
    x="i"
    in allE)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(clarsimp)
  apply(thin_tac "cfgLMMIyX G d (teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)))")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(subgoal_tac "strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i)) \<or> SSX" for SSX)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  prefer 2
  apply(rule_tac
    b="option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in mutual_strict_prefix_prefix)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(erule disjE)
  (*strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i))*)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(thin_tac "ESplitItem_from (S1 ! length v) = Some ab")
  apply(simp add: strict_prefix_def)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(case_tac c)
   apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(blast)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c ab list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab list)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i) = (ESplitItem_elim (S1 ! Suc i) @ ab # w) @ ESplitItem_ignore (S1 ! i)")
   apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(simp (no_asm_use))
  apply(clarsimp)
  apply(subgoal_tac "aa = ab \<and> ESplitItem_ignore (S1 ! Suc i) = w @ ESplitItem_ignore (S1 ! i)")
   apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(thin_tac "option_to_list (Some ab) = [ab]")
  apply(rule_tac
    e="e_\<pi>2"
    in exI_5)
  apply(rule_tac
    d="ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ e_\<pi>1"
    in exI_4)
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(rule_tac
    c="va"
    in exI_3)
  apply(rule_tac
    b="e_d2"
    in exI_2)
  apply(clarsimp)
  apply(rule_tac
    c="\<alpha>2"
    in exI_3)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(rule_tac
    t="last (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))"
    and s="last (take (length (restrict_newignore S1 (Suc i))) w @ take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i)))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) w @ take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i))"
    and s="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule take_butn2)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    and s="butn (ESplitItem_ignore (S1 ! (Suc i))) (length(restrict_toberemoved S1 ! (Suc i)))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule take_butn2)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule last_of_newignore_is_preserved1)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(rule_tac
    newi="restrict_newignore S1 i"
    in ssuffix_from_suffix_for_ignore)
         apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
         apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(rule ESplitItem_ignore_decompose)
           apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(simp (no_asm))
        apply(rule sym)
        apply(rule fillOptL_length)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
         apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
        apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
      apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule restrict_toberemoved_direct_computation)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (take (length (restrict_newignore S1 (Suc i))) w @ take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>")
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(thin_tac "ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2")
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA a]\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ab # w)\<rparr>")
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(rule_tac
    t="\<lparr>cfg_conf = [teA a]\<rparr>"
    and s="\<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(clarsimp)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ ab # w"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (ab # w)\<rparr>"
    and s="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ ab # w"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>")
  apply(rename_tac x i e_d a e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(subgoal_tac "liftA (w@butlast (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))) = liftA (butlast (take (length (restrict_newignore S1 (Suc i))) w @ take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i))))")
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(rule_tac
    f="liftA"
    in arg_cong)
   apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) w @ take (length (restrict_newignore S1 (Suc i)) - length w) (ESplitItem_ignore (S1 ! i))"
    and s="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule take_butn2)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    and s="butn (ESplitItem_ignore (S1 ! (Suc i))) (length(restrict_toberemoved S1 ! (Suc i)))"
    in ssubst)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule take_butn2)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule butlast_of_newignore_is_related1)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(rule_tac
    newi="restrict_newignore S1 i"
    in ssuffix_from_suffix_for_ignore)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(rule ESplitItem_ignore_decompose)
           apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(simp (no_asm))
        apply(rule sym)
        apply(rule fillOptL_length)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(rule_tac
    newi="restrict_newignore S1 (Suc i)"
    in ssuffix_from_suffix_for_ignore)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(rule ESplitItem_ignore_decompose)
          apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(simp (no_asm))
       apply(rule sym)
       apply(rule fillOptL_length)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule restrict_toberemoved_direct_computation)
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(rule_tac ?C1.0="liftA (butlast (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))" and ?\<alpha>1.0="[]" and ?\<alpha>2.0="fw!i" and ?d1.0="d" and ?d2.0="e_d1" in cfgLM_trans_der_biextend2_prime)
          apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
          apply(simp add: split_TSstructure_def)
         apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
     apply(simp (no_asm))
     apply(simp add: liftA_commutes_over_concat)
     apply(rule sym)
     apply(force)
    apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(simp add: setB_liftA)
  apply(simp add: setA_liftA)
  apply(rule_tac
    B="set ((take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
    in subset_trans)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule trivButLast)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(rule_tac
    B="set (((ESplitItem_ignore (S1 ! i))))"
    in subset_trans)
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   apply(rule List.set_take_subset)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(subgoal_tac "EValidSplitItem G (S1!i)")
   apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i e_d a e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d ab w)(*strict*)
  apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA c\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  prefer 2
  apply(rule_tac
    t="\<lparr>cfg_conf = teA a # liftA c\<rparr>"
    and s="\<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    t="\<lparr>cfg_conf = liftB (fw ! i)\<rparr>"
    and s="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    e="e_\<pi>2"
    in exI_5)
  apply(rule_tac
    d="ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ e_\<pi>1"
    in exI_4)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    c="va"
    in exI_3)
  apply(rule_tac
    b="e_d2"
    in exI_2)
  apply(clarsimp)
  apply(rule_tac
    c="\<alpha>2"
    in exI_3)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  prefer 2
  apply(rule_tac
    t="last (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))"
    and s="last (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i)))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule take_butn2)
   apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule ESplitItem_ignore_decompose)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(simp (no_asm))
   apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    and s="butn (ESplitItem_ignore (S1 ! (Suc i))) (length(restrict_toberemoved S1 ! (Suc i)))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule take_butn2)
   apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule ESplitItem_ignore_decompose)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(simp (no_asm))
   apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule last_of_newignore_is_preserved2)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule_tac
    newi="restrict_newignore S1 i"
    in ssuffix_from_suffix_for_ignore)
        apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
        apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(rule ESplitItem_ignore_decompose)
          apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(simp (no_asm))
       apply(rule sym)
       apply(rule fillOptL_length)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
        apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(rule_tac
    newi="restrict_newignore S1 (Suc i)"
    in ssuffix_from_suffix_for_ignore)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(rule ESplitItem_ignore_decompose)
         apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(simp (no_asm))
      apply(rule sym)
      apply(rule fillOptL_length)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(simp add: ssuffix_def)
    apply(rule_tac
    x="c @ option_to_list (Some aa)"
    in exI)
    apply(rule conjI)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     prefer 2
     apply(simp add: option_to_list_def)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
     apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa)"
    in restrict_toberemoved_direct_computation)
    apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(thin_tac "cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(thin_tac "ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2")
  apply(rename_tac x i e_d a aa ab e_d1 e_d2 va e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac ?C2.0="[]" and ?C1.0="liftA (option_to_list (Some aa) @ butlast (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))))" and ?w1''="[]" and ?\<alpha>1.0="[]" and ?\<alpha>2.0="fw!i" and ?d1.0="d" and ?d2.0="e_d1" in cfgLM_trans_der_biextend2_prime)
         apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
         apply(simp add: split_TSstructure_def)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   prefer 2
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  prefer 2
  apply(simp add: cfg_configurations_def)
  apply(simp add: setB_liftA)
  apply(simp add: setA_liftA)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "aa \<in> cfg_nonterminals G \<and> set (ESplitItem_ignore (S1 ! Suc i)) \<subseteq> cfg_nonterminals G")
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule conjI)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule_tac
    B="set ((take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i))))"
    in subset_trans)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule trivButLast)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule_tac
    B="set ((ESplitItem_ignore (S1 ! Suc i)))"
    in subset_trans)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule List.set_take_subset)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(subgoal_tac "EValidSplitItem G (S1!Suc i)")
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(simp only: EValidSplitItem_def EValidSplitItem_belongs_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    t="butlast (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))"
    and s="(c@[aa])@butlast (take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! Suc i)))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  prefer 2
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule take_butn2)
  apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule ESplitItem_ignore_decompose)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(simp (no_asm))
  apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    t="take (length (restrict_newignore S1 (Suc i))) (ESplitItem_ignore (S1 ! (Suc i)))"
    and s="butn (ESplitItem_ignore (S1 ! (Suc i))) (length(restrict_toberemoved S1 ! (Suc i)))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule take_butn2)
  apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(rule ESplitItem_ignore_decompose)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(simp (no_asm))
  apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule butlast_of_newignore_is_related2)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule_tac
    newi="restrict_newignore S1 i"
    in ssuffix_from_suffix_for_ignore)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(rule ESplitItem_ignore_decompose)
          apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(simp (no_asm))
       apply(rule sym)
       apply(rule fillOptL_length)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(rule_tac
    newi="restrict_newignore S1 (Suc i)"
    in ssuffix_from_suffix_for_ignore)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(rule_tac
    t="ESplitItem_ignore (S1 ! (Suc i))"
    in ssubst)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(rule ESplitItem_ignore_decompose)
         apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(simp (no_asm))
      apply(rule sym)
      apply(rule fillOptL_length)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(rule ESplitItem_ignore_restrict_toberemoved_suffix)
       apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(simp add: suffix_def)
    apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
    apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ aa# ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule restrict_toberemoved_restrict_toberemoved_suffix)
    apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa)"
    in restrict_toberemoved_direct_computation)
   apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_d1 e_\<pi>1 e_\<pi>2 \<alpha>1 \<alpha>2 d c)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d p_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(thin_tac "PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i) \<noteq> [] \<longrightarrow> (\<exists>e_d1 e_d2 va e_\<pi>1 e_\<pi>2. ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v))) = e_\<pi>1 @ e_\<pi>2 \<and> (\<exists>\<alpha>1 \<alpha>2. foldl (@) [] (drop (Suc i) (take (length v) fw)) = \<alpha>1 @ \<alpha>2 \<and> cfgLM.trans_der G e_d1 \<lparr>cfg_conf = liftA (option_to_list (Some aa) @ butlast (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))\<rparr> e_\<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G e_d2 \<lparr>cfg_conf = [teA (last (fillOptL (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i)) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! Suc i))) (ESplitItem_ignore (S1 ! Suc i))))))]\<rparr> e_\<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ teB b # va\<rparr>))")
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(erule impE)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def PValidSplit_def)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  prefer 2
  apply(simp add: EValidSplit_def EValidSplit_interline_def)
  apply(clarsimp)
  apply(erule_tac
    x="i"
    in allE)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i)) \<or> SSX" for SSX)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  prefer 2
  apply(rule_tac
    b="option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in mutual_strict_prefix_prefix)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  apply(erule disjE)
  (*strict_prefix (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_to (S1 ! i))*)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  apply(thin_tac "ESplitItem_from (S1 ! length v) = Some ab")
  apply(simp add: strict_prefix_def)
  apply(rename_tac x i e_d a aa p_da e_da va)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa p_da e_da va c)(*strict*)
  apply(case_tac c)
  apply(rename_tac x i e_d a aa p_da e_da va c)(*strict*)
  apply(blast)
  apply(rename_tac x i e_d a aa p_da e_da va c ab list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa p_da e_da va ab list)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x i e_d a aa p_da e_da va ab w)(*strict*)
  apply(subgoal_tac "ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i) = (ESplitItem_elim (S1 ! Suc i) @ ab # w) @ ESplitItem_ignore (S1 ! i)")
  apply(rename_tac x i e_d a aa p_da e_da va ab w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i e_d a aa p_da e_da va ab w)(*strict*)
  apply(simp (no_asm_use))
  apply(clarsimp)
  apply(subgoal_tac "aa = ab \<and> ESplitItem_ignore (S1 ! Suc i) = w @ ESplitItem_ignore (S1 ! i)")
  apply(rename_tac x i e_d a aa p_da e_da va ab w)(*strict*)
  prefer 2
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa p_da e_da va ab w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(thin_tac "option_to_list (Some ab) = [ab]")
  apply(subgoal_tac "False")
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(rule_tac
    tbR_i="restrict_toberemoved S1 ! i"
    and tbR_Si="restrict_toberemoved S1 ! Suc i"
    and ig_i="ESplitItem_ignore (S1 ! i)"
    and ig_Si="ESplitItem_ignore (S1 ! Suc i)"
    and new_i="restrict_newignore S1 i"
    and new_Si="restrict_newignore S1 (Suc i)"
    in impossible_empty_newignore)
      apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
     apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
   apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
    apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
    apply(rule ESplitItem_ignore_decompose)
      apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
   apply(simp (no_asm))
   apply(rule fillOptL_length)
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [ab]"
    in restrict_toberemoved_direct_computation)
    apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a p_da e_da va ab w)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  apply(thin_tac "cfgLMMIP G p_da (liftA (fillWithPreContext (PSplitItem_from (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i)) (last_back_state_if_l3_nonterminal (option_to_list (Some a))) (last_back_state_if_l3_nonterminal (take (length (PSplitItem_ignore (restrict G' G (S1 @ S1') (Suc (length v)) ! i))) (ESplitItem_ignore (S1 ! i)))))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc i) (length v)))) (liftB (foldl (@) [] (drop i (take (length v) fw)) @ [b])) (liftA (fillOptL (PSplitItem_to (restrict G' G (S1 @ S1') (Suc (length v)) ! length v)) (last_back_state_if_l3_nonterminal (take (Suc 0) (ESplitItem_to (S1 ! length v)))) @ tl (ESplitItem_to (S1 ! length v)) @ butn (restrict_toberemoved S1 ! length v) (length (restrict_toberemoved S1 ! i))))")
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLMMIy G d (liftA (a # drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) (liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))) []")
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  prefer 2
  apply(rule e_derivation_can_be_embedded_minimally_hlp3)
                   apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
                   apply(force)
                  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
                  apply(force)
                 apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
                 apply(force)
                apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
                apply(force)
               apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
               apply(force)
              apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
              apply(force)
             apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
             apply(force)
            apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
            apply(force)
           apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
           apply(force)
          apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
          apply(force)
         apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
         apply(force)
        apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab p_da e_da va c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: cfgLMMIy_def)
  apply(clarsimp)
  apply(thin_tac "cfgLMMIyX G d (teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))) (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)))")
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA c\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  prefer 2
  apply(rule_tac
    t="\<lparr>cfg_conf = teA a # liftA c\<rparr>"
    and s="\<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="\<lparr>cfg_conf = liftB (fw ! i)\<rparr>"
    and s="\<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>")
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="fillOptL (restrict_newignore S1 i) (last_back_state_if_l3_nonterminal (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))"
    and s="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal)
  apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
  apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "nat_seq (Suc i) (length v) = Suc i#nat_seq (Suc (Suc i)) (length v)")
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  prefer 2
  apply(rule nat_seq_pullout)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(clarsimp)
  apply(thin_tac "nat_seq (Suc i) (length v) = Suc i # nat_seq (Suc (Suc i)) (length v)")
  apply(rule_tac
    t="foldl (@) (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i)) @ ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i) (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="drop i (take (length v) fw)"
    and s=" fw!i#drop (Suc i) (take (length v) fw) "
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule e_derivation_at_tail_exists_hlp1)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="foldl (@) (fw ! i) (drop (Suc i) (take (length v) fw))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule foldl_first)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    b="e_da"
    in exI_2)
  apply(rule_tac
    d="ESplitItem_prods (S1 ! Suc i) @ \<pi>s ! Suc i @ foldl (@) [] (map (\<lambda>x. foldl (@) [] (ESplitItem_elim_prods ((S1 @ S1') ! x)) @ ESplitItem_prods ((S1 @ S1') ! x) @ \<pi>s ! x) (nat_seq (Suc (Suc i)) (length v)))"
    in exI_4)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    b="va"
    in exI_2)
  apply(rule_tac
    b="ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))"
    in exI_2)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    c="foldl (@) [] (drop (Suc i) (take (length v) fw))"
    in exI_3)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  prefer 2
  apply(rule_tac
    t="[teA (last (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))))]"
    and s="liftA (option_to_list (Some aa))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule take_butn2)
  apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(rule ESplitItem_ignore_decompose)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="aa"
    and s="last(c@[aa])"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    tbR_i="restrict_toberemoved S1 ! i"
    and tbR_Si="restrict_toberemoved S1 ! Suc i"
    and ig_i="ESplitItem_ignore (S1 ! i)"
    and ig_Si="ESplitItem_ignore (S1 ! Suc i)"
    and new_i="restrict_newignore S1 i"
    and new_Si="restrict_newignore S1 (Suc i)"
    in last_of_newignore_is_new_from)
       apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(rule ESplitItem_ignore_decompose)
        apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
        apply(force)
       apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(simp (no_asm))
     apply(rule fillOptL_length)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(simp (no_asm))
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [aa]"
    in restrict_toberemoved_direct_computation)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
  apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rule_tac
    t="butlast (take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i)))"
    and s="c"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="take (length (restrict_newignore S1 i)) (ESplitItem_ignore (S1 ! i))"
    and s="butn (ESplitItem_ignore (S1 ! i)) (length(restrict_toberemoved S1 ! i))"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule take_butn2)
  apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule ESplitItem_ignore_decompose)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA c\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="c"
    and s="butlast(c@[aa])"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    tbR_i="restrict_toberemoved S1 ! i"
    and tbR_Si="restrict_toberemoved S1 ! Suc i"
    and ig_i="ESplitItem_ignore (S1 ! i)"
    and ig_Si="ESplitItem_ignore (S1 ! Suc i)"
    and new_i="restrict_newignore S1 i"
    and new_Si="restrict_newignore S1 (Suc i)"
    in butlast_of_newignore_is_new_from)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(rule_tac
    t="ESplitItem_ignore (S1 ! i)"
    in ssubst)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(rule ESplitItem_ignore_decompose)
       apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
       apply(force)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(simp (no_asm))
    apply(rename_tac x i e_d a aa ab e_da va c)(*strict*)
    apply(rule fillOptL_length)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(rule_tac
    t="ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(rule ESplitItem_ignore_decompose)
      apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
      apply(force)
     apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
     apply(force)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac x i e_d a aa ab e_da va c)(*strict*)
   apply(rule fillOptL_length)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    ?w1.0="ESplitItem_to (S1 ! i)"
    and ?w2.0="ESplitItem_elim (S1 ! Suc i) @ [aa]"
    in restrict_toberemoved_direct_computation)
    apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
    apply(force)
   apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
   apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    w="ESplitItem_to (S1 ! i)"
    in append_linj)
  apply(rule_tac
    t="ESplitItem_to (S1 ! i) @ ESplitItem_ignore (S1 ! i)"
    and s="ESplitItem_elim (S1 ! Suc i) @ option_to_list (Some aa) @ ESplitItem_ignore (S1 ! Suc i)"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(rule_tac
    t="ESplitItem_elim (S1 ! Suc i)"
    and s="ESplitItem_to (S1 ! i) @ c"
    in ssubst)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac x i e_d a aa ab e_da va c)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac x i e_d a aa ab e_da va c d)(*strict*)
  apply(force)
  done

lemma e_derivation_can_be_embedded_minimally_hlp2: "
       F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S1) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S1 @ S1')
  \<Longrightarrow> v @ [teB b] = Esplit_signature S1
  \<Longrightarrow> ESplitItem_elem (S1 ! length v) = Some (teB b)
  \<Longrightarrow> PValidSplit G' G (restrict G' G (S1 @ S1') (Suc (length v)))
  \<Longrightarrow> i \<le> length v
  \<Longrightarrow> S1' \<noteq> []
  \<Longrightarrow> length (Esplit_signature S1) = Suc (length v)
  \<Longrightarrow> length S1 = Suc (length v)
  \<Longrightarrow> length (nat_seq 0 (length v)) = Suc (length v)
  \<Longrightarrow> nat_seq 0 (length v) ! length v = length v
  \<Longrightarrow> (S1 @ S1') ! i = S1 ! i
  \<Longrightarrow> (S1 @ S1') ! Suc i = S1 ! Suc i
  \<Longrightarrow> (S1 @ S1') ! length v = S1 ! length v
  \<Longrightarrow> ESplitItem_from (S1 ! i) = Some a
  \<Longrightarrow> nat_seq 0 (length v) ! i = i
  \<Longrightarrow> nat_seq 0 (length v) ! Suc i = Suc i
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = teA a # liftA (drop (length(ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i @ foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = liftB (fw ! i)@ liftA (drop (length(ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))) \<rparr>"
  apply(subgoal_tac "EValidSplitItem G (S1 ! i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
  apply(subgoal_tac "EValidSplitItem G (S1 ! Suc i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(erule_tac
      x="S1!Suc i"
      in ballE)
    apply(force)
   apply(subgoal_tac "S1!Suc i\<in> set S1")
    apply(force)
   apply(rule nth_mem)
   apply (metis Suc_lessI length_greater_0_conv less_Suc_eq_le nth_append_2_prime_prime nth_mem set_append set_append_contra2)
  apply(subgoal_tac "EValidSplit_interlineX (S1 ! i) (S1 ! Suc i)")
   prefer 2
   apply(simp add: EValidSplit_def EValidSplit_interline_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac "i=length v")
    apply(clarsimp)
   apply(subgoal_tac "i<length v")
    prefer 2
    apply(force)
   apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(thin_tac "EValidSplitItem_elim G (S1 ! i)")
  apply(thin_tac "EValidSplitItem_gen G (S1 ! Suc i)")
  apply(simp add: cfgLMTDL_def cfgLM.trans_der_list_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_elim_def EValidSplitItem_gen_def)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftA SSws\<rparr> (foldl (@) [] SSrenPIs) \<lparr>cfg_conf = []\<rparr>" for SSG SSws SSrenPIs)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule elim_map_to_trans_der)
      apply(rename_tac d)(*strict*)
      apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
      apply(force)
     apply(rename_tac d)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "elim_map G (ESplitItem_elim (S1 ! Suc i)) (ESplitItem_elim_prods (S1 ! Suc i)) (map (\<lambda>x. []) (ESplitItem_elim_prods (S1 ! Suc i)))")
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "(\<exists>b. Some (teB b) = ESplitItem_elem (S1 ! i)) \<longrightarrow> (\<forall>ia<length (ESplitItem_prods (S1 ! i)). hd (cfg_conf (the (get_configuration (d ia)))) \<noteq> the (ESplitItem_elem (S1 ! i)))")
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "(\<exists>A. Some (teA A) = ESplitItem_elem (S1 ! i)) \<longrightarrow> left_degen G d \<and> ESplitItem_elim_prods (S1 ! i) = []")
  apply(rename_tac d da)(*strict*)
  apply(subgoal_tac "ESplitItem_elem (S1 ! i) = Some (SSv ! i)" for SSv)
   apply(rename_tac d da)(*strict*)
   prefer 2
   apply(rule Esplit_signature_take_prefix_closureise)
     apply(rename_tac d da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d da)(*strict*)
    apply(force)
   apply(rename_tac d da)(*strict*)
   apply(force)
  apply(rename_tac d da)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac d da)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="liftA(drop (length(ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac d da)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac d da)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplitItem_belongs_def cfg_configurations_def)
    apply(clarsimp)
    apply (simp add: setB_liftA)
    apply(rule_tac
      B="setA (liftA ((ESplitItem_elim (S1 ! Suc i))))"
      in subset_trans)
     apply(rename_tac d da)(*strict*)
     apply(simp add: setA_liftA_set_drop_subset)
    apply(rename_tac d da)(*strict*)
    apply (simp add: setA_liftA)
   apply(rename_tac d da)(*strict*)
   apply(force)
  apply(rename_tac d da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_to (S1 ! i))\<rparr>")
  apply(rename_tac d da)(*strict*)
  apply(clarsimp)
  apply(rename_tac da d)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i))@ (liftA (ESplitItem_elim (S1 ! Suc i)@drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))))\<rparr>")
   apply(rename_tac da d)(*strict*)
   prefer 2
   apply(rule_tac
      t="(liftA (ESplitItem_elim (S1 ! Suc i)@drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i))))"
      and s="liftA (ESplitItem_to (S1 ! i) @drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))"
      in ssubst)
    apply(rename_tac da d)(*strict*)
    apply(rule_tac
      f="liftA"
      in arg_cong)
    apply(subgoal_tac "X" for X)
     apply(rename_tac da d)(*strict*)
     prefer 2
     apply(rule_tac
      ?w1.0="ESplitItem_elim (S1 ! Suc i)"
      and ?w2.0="ESplitItem_to (S1 ! i)"
      in shortest_dropper)
     apply(force)
    apply(rename_tac da d)(*strict*)
    apply(force)
   apply(rename_tac da d)(*strict*)
   apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac da d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_to (S1 ! i)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr>")
  apply(rename_tac da d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac da d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?v1.0="[]"
      and ?v2.0="option_to_list (Some (Esplit_signature S1 ! i))"
      and ?v4.0="liftA (ESplitItem_elim (S1 ! Suc i) @ drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))"
      and ?d1.0="d"
      and ?d2.0="ds!i"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac da d)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac da d)(*strict*)
    apply(force)
   apply(rename_tac da d)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac da d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i)) \<lparr>cfg_conf = option_to_list (Some (Esplit_signature S1 ! i)) @ liftA (ESplitItem_elim (S1 ! Suc i) @ drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>")
  apply(rename_tac da d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (ds ! i) \<lparr>cfg_conf = [Esplit_signature S1 ! i]\<rparr> (\<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i)\<rparr>")
  apply(rename_tac da d)(*strict*)
  apply(clarsimp)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac da d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?v1.0="fw!i"
      and ?v4.0="liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))"
      and ?d1.0="d"
      and ?d2.0="da"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac da d)(*strict*)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(rename_tac da d)(*strict*)
    apply(force)
   apply(rename_tac da d)(*strict*)
   apply(force)
  apply(rename_tac da d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA (option_to_list (Some a)) @ liftA (drop (length (ESplitItem_to (S1 ! i))) (ESplitItem_elim (S1 ! Suc i)))\<rparr> (ESplitItem_prods (S1 ! i) @ \<pi>s ! i) \<lparr>cfg_conf = liftB (fw ! i) @ liftA (ESplitItem_elim (S1 ! Suc i)) @ liftA (drop (length (ESplitItem_elim (S1 ! Suc i))) (ESplitItem_to (S1 ! i)))\<rparr>")
  apply(rename_tac da d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA (ESplitItem_elim (S1 ! Suc i))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S1 ! Suc i))) \<lparr>cfg_conf = []\<rparr>")
  apply(rename_tac da d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(simp add: option_to_list_def)
  done

lemma restrict_toberemovedX_last2: "
  m = length S
  \<Longrightarrow> length S > 0
  \<Longrightarrow> n=length S - Suc 0
  \<Longrightarrow> restrict_toberemovedX S ! m = tl (ESplitItem_to (S!n) @ ESplitItem_ignore (S!n))"
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="m"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="n"
      and s="nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule restrict_toberemovedX_last)
  apply(force)
  done

lemma restrict_newignore_last_empty: "
  EValidSplit G (S @ S')
  \<Longrightarrow> Suc n = length S
  \<Longrightarrow> ESplitItem_to (S ! n) \<noteq> []
  \<Longrightarrow> restrict_newignore S n = []"
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)) (length (restrict_toberemovedX S ! length S)))"
      in ssubst)
   apply(rule drop_and_crop_length)
  apply(clarsimp)
  apply(rule_tac
      t="min (length S) (length S - Suc 0)"
      and s="n"
      in ssubst)
   apply(force)
  apply(subgoal_tac "restrict_toberemoved S ! n=ESplitItem_ignore (S ! n)")
   prefer 2
   apply(subgoal_tac "last (restrict_toberemoved SSS) = ESplitItem_ignore (last SSS)" for SSS)
    prefer 2
    apply(rule_tac
      S="S"
      in restrict_toberemoved_last_is_ignore)
    apply(force)
   apply(rule_tac
      t="S ! n"
      and s="last S"
      in ssubst)
    apply(rule last_nth_prime)
    apply(force)
   apply(rule_tac
      t="restrict_toberemoved S ! n"
      and s="last (restrict_toberemoved S)"
      in ssubst)
    apply(rule last_nth_prime)
    apply(simp add: restrict_toberemoved_def enforceSuffix_def)
    apply(rule_tac
      t="length S - Suc 0"
      and s="n"
      in ssubst)
     apply(force)
    apply(subgoal_tac "length(nat_seq 0 n) = SSX" for SSX)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(force)
   apply(force)
  apply(rule_tac
      t="restrict_toberemovedX S ! length S"
      in ssubst)
   apply(rule restrict_toberemovedX_last2)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac "ESplitItem_to (S ! n)")
   prefer 2
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(case_tac S)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list aa lista)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma nonemtpy_newignore_implies_newto_unchanged: "
  restrict_newignore S2 n \<noteq> []
  \<Longrightarrow> restrict_newto S2 n = ESplitItem_to (S2!n)"
  apply(simp add: restrict_newto_def new_post_sig_def)
  apply(rule take_drop_and_crop_id)
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(subgoal_tac "length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemovedX S2 ! Suc n))) = SSX" for SSX)
   prefer 2
   apply(rule drop_and_crop_length)
  apply(clarsimp)
  apply(thin_tac "length (drop_and_crop (ESplitItem_to (S2 ! n) @ ESplitItem_ignore (S2 ! n)) (length (restrict_toberemovedX S2 ! Suc n))) = length (ESplitItem_to (S2 ! n)) + length (ESplitItem_ignore (S2 ! n)) - length (restrict_toberemovedX S2 ! Suc n)")
  apply(force)
  done

lemma nonemtpy_newignore_implies_newprods_unchanged: "
  valid_cfg G
  \<Longrightarrow> restrict_newignore S2 n \<noteq> []
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> (ESplitItem_prods (S2 ! n)) \<lparr>cfg_conf=(the (ESplitItem_elem (S2 ! n)) # liftA (ESplitItem_to (S2 ! n)))\<rparr>
  \<Longrightarrow> \<forall>i<length (ESplitItem_prods (S2 ! n)).
              \<exists>A. hd (cfg_conf (the (get_configuration (d i)))) = teA A
  \<Longrightarrow> restrict_newprods G' G S2 n = liftB (ESplitItem_prods (S2!n))"
  apply(subgoal_tac "restrict_newto S2 n = ESplitItem_to (S2!n)")
   prefer 2
   apply(rule nonemtpy_newignore_implies_newto_unchanged)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S2 ! n)) - Suc 0)) = SSx" for SSx)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule listEqI)
   apply(simp add: restrict_newprodsX_def restrict_newprods_def restrict_newprods_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: restrict_newprodsX_def restrict_newprods_def restrict_newprods_def)
  done

lemma equal_split_prefix_hlp1_triv_eq: "
  map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p)))
           (restrict_newprodsX G' G (\<pi>) A
             w) = liftA(map (prod_to_edge G') (\<pi>))"
  apply(simp add: restrict_newprodsX_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq 0 (length (\<pi>) - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
   apply (metis liftA_preserves_length length_map)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length (\<pi>) - Suc 0) ! i = SSX" for SSX)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply (metis teA_liftA_nth length_map nth_map)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length (\<pi>) - Suc 0) ! i = SSX" for SSX)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="liftA (map (prod_to_edge G') (\<pi>)) ! i"
      and s="teA (prod_to_edge G' (\<pi> ! i))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply (metis teA_liftA_nth length_map nth_map)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: prod_to_edge_def)
  done

lemma equal_split_prefix_hlp5_construct_relevant_cfgLMMIP_not_abstract_productions: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S@S')
  \<Longrightarrow> length S = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S
  \<Longrightarrow> ESplitItem_from (S ! Suc n)=Some X
  \<Longrightarrow> n < length v
  \<Longrightarrow> length (ESplitItem_ignore (S ! n)) \<le> length (restrict_toberemovedX S ! Suc n)
  \<Longrightarrow> restrict_toberemovedX S ! Suc n = restrict_toberemoved S ! Suc n
  \<Longrightarrow> cfgLMMIP G d (teA X#liftA (take(length(restrict_newignore S (Suc n)))(ESplitItem_ignore (S! Suc n)))) \<pi> (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)
  \<Longrightarrow> \<exists>d. cfgLMMIP G d (liftA (butn (ESplitItem_to (S ! n)) (length (restrict_toberemoved S ! Suc n) - length (ESplitItem_ignore (S ! n))))) ((foldl (@) [] (ESplitItem_elim_prods (S ! Suc n)) @ \<pi>)) (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)"
  apply(subgoal_tac "Suc n<length S")
   prefer 2
   apply(rule_tac
      y="(length v)"
      in le_less_trans)
    apply(force)
   apply(rule_tac
      y="length (v@[teB b])"
      in less_le_trans)
    apply(simp (no_asm))
   apply(force)
  apply(subgoal_tac "EValidSplit_interlineX ((S @ S') ! n) ((S @ S') ! Suc n)")
   prefer 2
   apply(subgoal_tac "EValidSplit_interline (S @ S')")
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(simp add: EValidSplit_interline_def)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "(S@S')!Suc n=S!Suc n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S@S')!n=S! n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      t="butn (ESplitItem_to (S ! n)) (length (restrict_toberemoved S ! Suc n) - length (ESplitItem_ignore (S ! n)))"
      and s="ESplitItem_elim (S ! Suc n)@ X # (take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n)))"
      in ssubst)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      v="drop (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))"
      in append_injr)
   apply(rule_tac
      t="(ESplitItem_elim (S ! Suc n) @ X # take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))) @ drop (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))"
      and s="ESplitItem_elim (S ! Suc n) @ X # ESplitItem_ignore (S ! Suc n)"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="ESplitItem_elim (S ! Suc n) @ X # ESplitItem_ignore (S ! Suc n)"
      and s="ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)"
      in ssubst)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc n) @ [X]"
      and ?w1.0="ESplitItem_to (S ! n)"
      and S="S"
      and i="n"
      in restrict_toberemoved_direct_computation)
      prefer 3
      apply(rule sym)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc n) @ [X]"
      and ?w1.0="ESplitItem_to (S ! n)"
      and S="S"
      and i="n"
      in toberemoved_suffix)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: suffix_def takeB_def butn_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and i="n"
      in ignore_toberemoved_suffix)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and i="Suc n"
      in ignore_toberemoved_suffix)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def takeB_def butn_def)
   apply(clarsimp)
   apply(rename_tac c ca)(*strict*)
   apply(rule_tac
      t="take (length (ESplitItem_to (S ! n)) - length c) (ESplitItem_to (S ! n))"
      and s="ESplitItem_elim (S ! Suc n) @ X # ca"
      in ssubst)
    apply(rename_tac c ca)(*strict*)
    apply(rule_tac
      t="ESplitItem_to (S ! n)"
      and s="ESplitItem_elim (S ! Suc n) @ X # ca @ c"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac c ca)(*strict*)
   apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! Suc n) @ ESplitItem_ignore (S ! Suc n)) (length (restrict_toberemovedX S ! Suc (Suc n))))"
      in ssubst)
    apply(rename_tac c ca)(*strict*)
    apply(rule drop_and_crop_length)
   apply(rename_tac c ca)(*strict*)
   apply(simp (no_asm))
   apply(clarsimp)
   apply(case_tac "Suc (Suc (Suc n)) \<le> length S")
    apply(rename_tac c ca)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca)(*strict*)
     prefer 2
     apply(rule_tac
      S="S"
      and i="Suc (Suc n)"
      in ignore_toberemoved_suffix)
      apply(rename_tac c ca)(*strict*)
      apply(force)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
    apply(clarsimp)
    apply(rename_tac c ca cb)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule_tac
      n="Suc(Suc n)"
      and S="S"
      in restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplit_interlineX ((S @ S') ! Suc n) ((S @ S') ! Suc (Suc n))")
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(subgoal_tac "EValidSplit_interline (S @ S')")
      apply(rename_tac c ca cb)(*strict*)
      prefer 2
      apply(simp add: EValidSplit_def)
     apply(rename_tac c ca cb)(*strict*)
     apply(simp add: EValidSplit_interline_def)
     apply(simp add: EValidSplit_interlineX_def)
    apply(rename_tac c ca cb)(*strict*)
    apply(subgoal_tac "(S@S')!Suc (Suc n)=S!Suc (Suc n)")
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_interlineX_def)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc n)) @ option_to_list (ESplitItem_from (S ! Suc (Suc n)))"
      and ?w1.0="ESplitItem_to (S ! Suc n)"
      and S="S"
      and i="Suc n"
      in toberemoved_suffix)
       apply(rename_tac c ca cb)(*strict*)
       apply(force)
      apply(rename_tac c ca cb)(*strict*)
      apply(force)
     apply(rename_tac c ca cb)(*strict*)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
    apply(clarsimp)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(rule_tac
      t="drop (length ca - length cc) ca"
      and s="[]"
      in ssubst)
     apply(rename_tac c ca cb cc)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb cc)(*strict*)
     prefer 2
     apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc n)) @ option_to_list (ESplitItem_from (S ! Suc (Suc n)))"
      and ?w1.0="ESplitItem_to (S ! Suc n)"
      and S="S"
      and i="Suc n"
      in restrict_toberemoved_direct_computation)
       apply(rename_tac c ca cb cc)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac c ca cb cc)(*strict*)
      apply(force)
     apply(rename_tac c ca cb cc)(*strict*)
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
   apply(rename_tac c ca)(*strict*)
   apply(subgoal_tac "(Suc (Suc n)) = length S")
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and n="Suc n"
      in restrict_toberemovedX_last)
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "restrict_toberemoved S ! (Suc n) = ESplitItem_ignore (S ! (Suc n))")
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(rule_tac
      t="restrict_toberemoved S ! (Suc n)"
      and s="last(restrict_toberemoved S)"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(rule last_nth_prime)
     apply(simp add: restrict_toberemoved_def enforceSuffix_def)
     apply(rule_tac
      t="length (nat_seq 0 (length (Esplit_signature S) - Suc 0))"
      in ssubst)
      apply(rename_tac c ca)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(rule_tac
      t="S ! (Suc n)"
      and s="last S"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(rule last_nth_prime)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(rule restrict_toberemoved_last_is_ignore)
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac "ESplitItem_to (S ! Suc n)")
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rename_tac c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_to (S ! Suc n) \<noteq> []")
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      b="b"
      in ESplitItem_to_not_empty_on_generating_line)
        apply(rename_tac c)(*strict*)
        apply(force)
       apply(rename_tac c)(*strict*)
       apply(force)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(rule_tac
      t="(S @ S') ! Suc n"
      and s="S!Suc n"
      in ssubst)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply (metis Esplit_signature_take_prefix_closureise2 Nat.lessI Suc_length less_SucE not_less_eq nth_append_2_prime_prime nth_first)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA(ESplitItem_elim (S ! Suc n))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S ! Suc n))) \<lparr>cfg_conf=[]\<rparr>")
   apply(case_tac "\<pi>=[]")
    apply(subgoal_tac "False")
     apply(force)
    apply(clarsimp)
    apply(rename_tac da)(*strict*)
    apply(simp add: cfgLMMIP_def)
    apply(clarsimp)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac da e)(*strict*)
    apply(case_tac tn)
     apply(rename_tac da e)(*strict*)
     apply(clarsimp)
     apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
      apply(rename_tac da e)(*strict*)
      apply(clarsimp)
     apply(rename_tac da e a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac da e a list)(*strict*)
    apply(clarsimp)
    apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
     apply(rename_tac da e a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac da e a list aa lista)(*strict*)
    apply(clarsimp)
   apply(erule exE)+
   apply(rename_tac da)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac da)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="da"
      and ?d2.0="d"
      in cfgLMMIP_and_cfgLM_trans_der_append)
        apply(rename_tac da)(*strict*)
        apply(force)
       apply(rename_tac da)(*strict*)
       apply(force)
      apply(rename_tac da)(*strict*)
      apply(force)
     apply(rename_tac da)(*strict*)
     apply(force)
    apply(rename_tac da)(*strict*)
    apply(force)
   apply(rename_tac da)(*strict*)
   apply(erule exE)+
   apply(rename_tac da daa)(*strict*)
   apply(rule_tac
      x="daa"
      in exI)
   apply (simp add:liftA_commutes_over_concat)
  apply(thin_tac "cfgLMMIP G d (teA X # liftA (take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n)))) \<pi> (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)")
  apply(thin_tac "ESplitItem_elim (S ! Suc n) @ option_to_list (Some X) @ ESplitItem_ignore (S ! Suc n) = ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)")
  apply(thin_tac "(S @ S') ! n = S ! n")
  apply(thin_tac "(S @ S') ! Suc n = S ! Suc n")
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S!Suc n"
      in ballE)
   prefer 2
   apply(force)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_elim_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule elim_map_to_trans_der)
      apply(simp add: split_TSstructure_def)
      apply(force)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma equal_split_prefix_hlp5_construct_relevant_cfgLMMIP: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLMTDL G ds (Esplit_signature S) \<pi>s fw
  \<Longrightarrow> EValidSplit G (S@S')
  \<Longrightarrow> length S = length (v@[teB b])
  \<Longrightarrow> v@[teB b] = Esplit_signature S
  \<Longrightarrow> ESplitItem_from (S ! Suc n)=Some X
  \<Longrightarrow> n < length v
  \<Longrightarrow> length (ESplitItem_ignore (S ! n)) \<le> length (restrict_toberemovedX S ! Suc n)
  \<Longrightarrow> restrict_toberemovedX S ! Suc n = restrict_toberemoved S ! Suc n
  \<Longrightarrow> cfgLMMIP G d (teA X#liftA (take(length(restrict_newignore S (Suc n)))(ESplitItem_ignore (S! Suc n)))) \<pi> (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)
  \<Longrightarrow> \<exists>d \<pi>. cfgLMMIP G d (liftA (butn (ESplitItem_to (S ! n)) (length (restrict_toberemoved S ! Suc n) - length (ESplitItem_ignore (S ! n))))) \<pi> (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)"
  apply(subgoal_tac "Suc n<length S")
   prefer 2
   apply(rule_tac
      y="(length v)"
      in le_less_trans)
    apply(force)
   apply(rule_tac
      y="length (v@[teB b])"
      in less_le_trans)
    apply(simp (no_asm))
   apply(force)
  apply(subgoal_tac "EValidSplit_interlineX ((S @ S') ! n) ((S @ S') ! Suc n)")
   prefer 2
   apply(subgoal_tac "EValidSplit_interline (S @ S')")
    prefer 2
    apply(simp add: EValidSplit_def)
   apply(simp add: EValidSplit_interline_def)
  apply(simp add: EValidSplit_interlineX_def)
  apply(subgoal_tac "(S@S')!Suc n=S!Suc n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S@S')!n=S! n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      t="butn (ESplitItem_to (S ! n)) (length (restrict_toberemoved S ! Suc n) - length (ESplitItem_ignore (S ! n)))"
      and s="ESplitItem_elim (S ! Suc n)@ X # (take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n)))"
      in ssubst)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      v="drop (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))"
      in append_injr)
   apply(rule_tac
      t="(ESplitItem_elim (S ! Suc n) @ X # take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))) @ drop (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n))"
      and s="ESplitItem_elim (S ! Suc n) @ X # ESplitItem_ignore (S ! Suc n)"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="ESplitItem_elim (S ! Suc n) @ X # ESplitItem_ignore (S ! Suc n)"
      and s="ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)"
      in ssubst)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc n) @ [X]"
      and ?w1.0="ESplitItem_to (S ! n)"
      and S="S"
      and i="n"
      in restrict_toberemoved_direct_computation)
      prefer 3
      apply(rule sym)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc n) @ [X]"
      and ?w1.0="ESplitItem_to (S ! n)"
      and S="S"
      and i="n"
      in toberemoved_suffix)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: suffix_def takeB_def butn_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and i="n"
      in ignore_toberemoved_suffix)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and i="Suc n"
      in ignore_toberemoved_suffix)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def takeB_def butn_def)
   apply(clarsimp)
   apply(rename_tac c ca)(*strict*)
   apply(rule_tac
      t="take (length (ESplitItem_to (S ! n)) - length c) (ESplitItem_to (S ! n))"
      and s="ESplitItem_elim (S ! Suc n) @ X # ca"
      in ssubst)
    apply(rename_tac c ca)(*strict*)
    apply(rule_tac
      t="ESplitItem_to (S ! n)"
      and s="ESplitItem_elim (S ! Suc n) @ X # ca @ c"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac c ca)(*strict*)
   apply(simp (no_asm) add: restrict_newignore_def new_post_sig_def)
   apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! Suc n) @ ESplitItem_ignore (S ! Suc n)) (length (restrict_toberemovedX S ! Suc (Suc n))))"
      in ssubst)
    apply(rename_tac c ca)(*strict*)
    apply(rule drop_and_crop_length)
   apply(rename_tac c ca)(*strict*)
   apply(simp (no_asm))
   apply(clarsimp)
   apply(case_tac "Suc (Suc (Suc n)) \<le> length S")
    apply(rename_tac c ca)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca)(*strict*)
     prefer 2
     apply(rule_tac
      S="S"
      and i="Suc (Suc n)"
      in ignore_toberemoved_suffix)
      apply(rename_tac c ca)(*strict*)
      apply(force)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
    apply(clarsimp)
    apply(rename_tac c ca cb)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule_tac
      n="Suc(Suc n)"
      and S="S"
      in restrict_toberemovedX_equals_restrict_toberemoved)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "EValidSplit_interlineX ((S @ S') ! Suc n) ((S @ S') ! Suc (Suc n))")
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(subgoal_tac "EValidSplit_interline (S @ S')")
      apply(rename_tac c ca cb)(*strict*)
      prefer 2
      apply(simp add: EValidSplit_def)
     apply(rename_tac c ca cb)(*strict*)
     apply(simp add: EValidSplit_interline_def)
     apply(simp add: EValidSplit_interlineX_def)
    apply(rename_tac c ca cb)(*strict*)
    apply(subgoal_tac "(S@S')!Suc (Suc n)=S!Suc (Suc n)")
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(simp add: EValidSplit_interlineX_def)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb)(*strict*)
     prefer 2
     apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc n)) @ option_to_list (ESplitItem_from (S ! Suc (Suc n)))"
      and ?w1.0="ESplitItem_to (S ! Suc n)"
      and S="S"
      and i="Suc n"
      in toberemoved_suffix)
       apply(rename_tac c ca cb)(*strict*)
       apply(force)
      apply(rename_tac c ca cb)(*strict*)
      apply(force)
     apply(rename_tac c ca cb)(*strict*)
     apply(force)
    apply(rename_tac c ca cb)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
    apply(clarsimp)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(rule_tac
      t="drop (length ca - length cc) ca"
      and s="[]"
      in ssubst)
     apply(rename_tac c ca cb cc)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac c ca cb cc)(*strict*)
     prefer 2
     apply(rule_tac
      ?w2.0="ESplitItem_elim (S ! Suc (Suc n)) @ option_to_list (ESplitItem_from (S ! Suc (Suc n)))"
      and ?w1.0="ESplitItem_to (S ! Suc n)"
      and S="S"
      and i="Suc n"
      in restrict_toberemoved_direct_computation)
       apply(rename_tac c ca cb cc)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac c ca cb cc)(*strict*)
      apply(force)
     apply(rename_tac c ca cb cc)(*strict*)
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def takeB_def butn_def)
   apply(rename_tac c ca)(*strict*)
   apply(subgoal_tac "(Suc (Suc n)) = length S")
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(rule_tac
      S="S"
      and n="Suc n"
      in restrict_toberemovedX_last)
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "restrict_toberemoved S ! (Suc n) = ESplitItem_ignore (S ! (Suc n))")
    apply(rename_tac c ca)(*strict*)
    prefer 2
    apply(rule_tac
      t="restrict_toberemoved S ! (Suc n)"
      and s="last(restrict_toberemoved S)"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(rule last_nth_prime)
     apply(simp add: restrict_toberemoved_def enforceSuffix_def)
     apply(rule_tac
      t="length (nat_seq 0 (length (Esplit_signature S) - Suc 0))"
      in ssubst)
      apply(rename_tac c ca)(*strict*)
      apply(rule nat_seq_length_prime)
     apply(rename_tac c ca)(*strict*)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(rule_tac
      t="S ! (Suc n)"
      and s="last S"
      in ssubst)
     apply(rename_tac c ca)(*strict*)
     apply(rule last_nth_prime)
     apply(force)
    apply(rename_tac c ca)(*strict*)
    apply(rule restrict_toberemoved_last_is_ignore)
    apply(force)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac "ESplitItem_to (S ! Suc n)")
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rename_tac c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ESplitItem_to (S ! Suc n) \<noteq> []")
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      b="b"
      in ESplitItem_to_not_empty_on_generating_line)
        apply(rename_tac c)(*strict*)
        apply(force)
       apply(rename_tac c)(*strict*)
       apply(force)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(rule_tac
      t="(S @ S') ! Suc n"
      and s="S!Suc n"
      in ssubst)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply (metis Esplit_signature_take_prefix_closureise2 Nat.lessI Suc_length less_SucE not_less_eq nth_append_2_prime_prime nth_first)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA(ESplitItem_elim (S ! Suc n))\<rparr> (foldl (@) [] (ESplitItem_elim_prods (S ! Suc n))) \<lparr>cfg_conf=[]\<rparr>")
   apply(case_tac "\<pi>=[]")
    apply(subgoal_tac "False")
     apply(force)
    apply(clarsimp)
    apply(rename_tac da)(*strict*)
    apply(simp add: cfgLMMIP_def)
    apply(clarsimp)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac da e)(*strict*)
    apply(case_tac tn)
     apply(rename_tac da e)(*strict*)
     apply(clarsimp)
     apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
      apply(rename_tac da e)(*strict*)
      apply(clarsimp)
     apply(rename_tac da e a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac da e a list)(*strict*)
    apply(clarsimp)
    apply(case_tac "foldl (@) [] (drop (Suc n) (take (length v) fw))")
     apply(rename_tac da e a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac da e a list aa lista)(*strict*)
    apply(clarsimp)
   apply(erule exE)+
   apply(rename_tac da)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac da)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="da"
      and ?d2.0="d"
      in cfgLMMIP_and_cfgLM_trans_der_append)
        apply(rename_tac da)(*strict*)
        apply(force)
       apply(rename_tac da)(*strict*)
       apply(force)
      apply(rename_tac da)(*strict*)
      apply(force)
     apply(rename_tac da)(*strict*)
     apply(force)
    apply(rename_tac da)(*strict*)
    apply(force)
   apply(rename_tac da)(*strict*)
   apply(erule exE)+
   apply(rename_tac da daa)(*strict*)
   apply(rule_tac
      x="daa"
      in exI)
   apply(rule_tac
      x="(foldl (@) [] (ESplitItem_elim_prods (S ! Suc n)) @ \<pi>)"
      in exI)
   apply (simp add:liftA_commutes_over_concat)
  apply(thin_tac "cfgLMMIP G d (teA X # liftA (take (length (restrict_newignore S (Suc n))) (ESplitItem_ignore (S ! Suc n)))) \<pi> (liftB (foldl (@) [] (drop (Suc n) (take (length v) fw)) @ [b])) (liftA tn)")
  apply(thin_tac "ESplitItem_elim (S ! Suc n) @ option_to_list (Some X) @ ESplitItem_ignore (S ! Suc n) = ESplitItem_to (S ! n) @ ESplitItem_ignore (S ! n)")
  apply(thin_tac "(S @ S') ! n = S ! n")
  apply(thin_tac "(S @ S') ! Suc n = S ! Suc n")
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_ValidItem_def)
  apply(erule_tac
      x="S!Suc n"
      in ballE)
   prefer 2
   apply(force)
  apply(simp add: EValidSplitItem_def)
  apply(clarsimp)
  apply(simp add: EValidSplitItem_elim_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule elim_map_to_trans_der)
      apply(simp add: split_TSstructure_def)
      apply(force)
     prefer 3
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma restrict_newprodsXX_implication: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2
  \<Longrightarrow> ia < length \<pi>1
  \<Longrightarrow> ia < length \<pi>2
  \<Longrightarrow> cropTol3l2_single F1 = cropTol3l2_single F2
  \<Longrightarrow> cfgLM.trans_der G dx1 \<lparr>cfg_conf = [teA F1]\<rparr> \<pi>1 \<lparr>cfg_conf = X # liftA to1\<rparr>
  \<Longrightarrow> ((\<exists>b. Some (teB b) = Some X) \<longrightarrow> (\<forall>ia<length \<pi>1. hd (cfg_conf (the (get_configuration (dx1 ia)))) \<noteq> X))
  \<Longrightarrow> cfgLM.trans_der G dx2 \<lparr>cfg_conf = [teA F2]\<rparr> \<pi>2 \<lparr>cfg_conf = X # liftA to2\<rparr>
  \<Longrightarrow> ((\<exists>b. Some (teB b) = Some X) \<longrightarrow> (\<forall>ia<length \<pi>2. hd (cfg_conf (the (get_configuration (dx2 ia)))) \<noteq> X))
  \<Longrightarrow> ((\<exists>A. Some (teA A) = Some X) \<longrightarrow> (left_degen G dx1))
  \<Longrightarrow> ((\<exists>A. Some (teA A) = Some X) \<longrightarrow> (left_degen G dx2))
  \<Longrightarrow> length nt \<le> length to1
  \<Longrightarrow> length nt \<le> length to2
  \<Longrightarrow> (\<exists>n1\<le>length to1. nt = cropTol3l2 (take n1 to1)) \<or> nt = to1
  \<Longrightarrow> (\<exists>n2\<le>length to2. nt = cropTol3l2 (take n2 to2)) \<or> nt = to2
  \<Longrightarrow> notfinishingL \<pi>1
  \<Longrightarrow> notfinishingL \<pi>2
  \<Longrightarrow> (\<forall>p\<in> set(butlast \<pi>1). \<forall>b A. prod_rhs p\<noteq>[teB b,teA A])
  \<Longrightarrow> (\<forall>p\<in> set(butlast \<pi>2). \<forall>b A. prod_rhs p\<noteq>[teB b,teA A])
  \<Longrightarrow> restrict_newprodsXX G ia \<pi>1 (Some X) nt
  \<Longrightarrow> restrict_newprodsXX G ia \<pi>2 (Some X) nt"
  apply(clarsimp)
  apply(simp add: restrict_newprodsXX_def)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      i="ia"
      and d="dx1"
      in cfgLM.trans_der_position_detail)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e ci)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac e ci)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac e ci)(*strict*)
  apply(erule_tac
      x="dx1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA F1]\<rparr>"
      in allE)
  apply(erule_tac
      x="take ia \<pi>1"
      in allE)
  apply(erule_tac
      x="ci"
      in allE)
  apply(erule_tac
      P="cfgLMTD G dx1 \<lparr>cfg_conf = [teA F1]\<rparr> (take ia \<pi>1) ci"
      in impE)
   apply(rename_tac e ci)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      t="min (length (\<pi>1)) ia"
      and s="ia"
      in ssubst)
    apply(rename_tac e ci)(*strict*)
    apply(force)
   apply(rename_tac e ci)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci ea eb)(*strict*)
   apply(rule_tac
      m="(length (\<pi>1))-ia"
      and v="map Some (drop ia ((\<pi>1)))"
      in get_labels_drop_tail)
    apply(rename_tac e ci ea eb)(*strict*)
    apply(clarsimp)
    apply (metis List.map_append append_take_drop_id)
   apply(rename_tac e ci ea eb)(*strict*)
   apply(force)
  apply(rename_tac e ci)(*strict*)
  apply(erule_tac
      P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F1]\<rparr> = liftB w1 @ liftA w2"
      in impE)
   apply(rename_tac e ci)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[SSX]" for SSX
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac e ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci w1 w2)(*strict*)
  apply(case_tac ci)
  apply(rename_tac e ci w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac e w1 w2)(*strict*)
   prefer 2
   apply(rename_tac e w1 w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w2 a list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac e w2 a list)(*strict*)
    apply(force)
   apply(rename_tac e w2 a list)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac e w2 a list)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac e w2 a list ea eb)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      eij="ea"
      and cij="\<lparr>cfg_conf = X # liftA to1\<rparr>"
      and ci="\<lparr>cfg_conf = teB a # liftB list @ liftA w2\<rparr>"
      and ei="e"
      and d="dx1"
      and i="ia"
      and j="length (\<pi>1)-ia"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac e w2 a list ea eb)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac e w2 a list ea eb)(*strict*)
        apply(force)
       apply(rename_tac e w2 a list ea eb)(*strict*)
       apply(force)
      apply(rename_tac e w2 a list ea eb)(*strict*)
      apply(force)
     apply(rename_tac e w2 a list ea eb)(*strict*)
     apply(force)
    apply(rename_tac e w2 a list ea eb)(*strict*)
    apply(force)
   apply(rename_tac e w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w2 a list w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "maxTermPrefix (teB a # liftB list @ liftA w2) = a#list")
    apply(rename_tac e w2 a list w)(*strict*)
    apply(clarsimp)
    apply(case_tac X)
     apply(rename_tac e w2 a list w aa)(*strict*)
     apply(subgoal_tac "maxTermPrefix (X # liftA to1) = []")
      apply(rename_tac e w2 a list w aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e w2 a list w aa)(*strict*)
     apply (metis list.simps(3) maxTermPrefix_terminal_front)
    apply(rename_tac e w2 a list w b)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "maxTermPrefix (teB b # liftA to1) = [b]")
     apply(rename_tac e w2 a list w b)(*strict*)
     apply(clarsimp)
     apply(rename_tac e w2 b)(*strict*)
     apply(erule_tac
      x="ia"
      in allE)+
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac e w2 a list w b)(*strict*)
    apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
   apply(rename_tac e w2 a list w)(*strict*)
   apply (metis maxTermPrefix_pull_out append_Nil2 maxTermPrefix_liftA maxTermPrefix_shift)
  apply(rename_tac e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac e w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="dx1"
      and i="ia"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac e)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac e w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e a list)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      xs="list"
      in rev_cases)
   apply(rename_tac e a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac e a)(*strict*)
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(subgoal_tac "derives G (drop ia (\<pi>1)) = X # liftA to1")
    apply(rename_tac e a)(*strict*)
    apply(subgoal_tac "length (X # liftA nt) \<le> length(X # liftA to1)")
     apply(rename_tac e a)(*strict*)
     apply(simp add: prefix_def strict_prefix_def)
     apply(clarsimp)
     apply(rename_tac e a c)(*strict*)
     apply(rule_tac
      xs="c"
      in rev_cases)
      apply(rename_tac e a c)(*strict*)
      apply(clarsimp)
     apply(rename_tac e a c ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac e a ys y)(*strict*)
     apply(subgoal_tac "\<not> (length (liftA nt) \<le> length (liftA to1))")
      apply(rename_tac e a ys y)(*strict*)
      apply(force)
     apply(rename_tac e a ys y)(*strict*)
     apply(rule less_not_leq)
     apply(rule_tac
      t="liftA nt"
      and s="liftA to1 @ ys @ [y]"
      in ssubst)
      apply(rename_tac e a ys y)(*strict*)
      apply(force)
     apply(rename_tac e a ys y)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac e a)(*strict*)
    apply(simp (no_asm_use) add: restrict_newto_def)
    apply (metis liftA_preserves_length takeShorter)
   apply(rename_tac e a)(*strict*)
   apply(thin_tac "(0 < ia) = (e = Some (\<pi>1 ! (ia - Suc 0)))")
   apply(thin_tac "(ia = 0) = (e = None)")
   apply(subgoal_tac "X" for X)
    apply(rename_tac e a)(*strict*)
    prefer 2
    apply(rule_tac
      d="dx1"
      and i="ia"
      in derive_entire)
       apply(rename_tac e a)(*strict*)
       apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e a)(*strict*)
  apply(force)
  apply(rename_tac e a)(*strict*)
  apply(force)
  apply(rename_tac e a)(*strict*)
  apply(force)
  apply(rename_tac e a)(*strict*)
  apply(force)
  apply(rename_tac e a list ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e a ys y)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac A1 w1 B1)
  apply(rename_tac e A1 w1 B1)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1)(*strict*)
  prefer 2
  apply(rule_tac
      i="ia"
      and d="dx2"
      in cfgLM.trans_der_position_detail)
  apply(rename_tac e A1 w1 B1)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac e A1 w1 B1 ea ci cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea cfg_confa)(*strict*)
  apply(thin_tac "(ia = 0) = (ea = None)")
  apply(thin_tac "(0 < ia) = (ea = Some (\<pi>2 ! (ia - Suc 0)))")
  apply(rename_tac w)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  prefer 2
  apply(rule_tac
      ?e1.0="e"
      and n="ia"
      and d="dx1"
      in cfgLM.trans_der_skip)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  prefer 2
  apply(rule_tac
      ?e1.0="ea"
      and n="ia"
      and d="dx2"
      in cfgLM.trans_der_skip)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(subgoal_tac "prefix (realizable G (drop ia (\<pi>1))) SSrenPI" for SSrenPI)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  prefer 2
  apply(rule realizable_prefix)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(subgoal_tac "prefix (realizable G (drop ia (\<pi>2))) SSrenPI" for SSrenPI)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  prefer 2
  apply(rule realizable_prefix)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(case_tac w)
  apply(rename_tac e A1 w1 B1 ea w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="dx2"
      and i="ia"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac e A1 w1 B1 ea w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea a list)(*strict*)
  apply(case_tac a)
  apply(rename_tac e A1 w1 B1 ea a list aa)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list b)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac e A1 w1 B1 ea list b)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
      eij="ec"
      and cij="\<lparr>cfg_conf = X # liftA to2\<rparr>"
      and ci="\<lparr>cfg_conf = teB b # list\<rparr>"
      and ei="ea"
      and d="dx2"
      and i="ia"
      and j="length (\<pi>2)-ia"
      in cfgLM.derivation_monotonically_inc)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(rule_tac
      t="ia + (length \<pi>2 - ia)"
      and s="length \<pi>2"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list b w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (teB b # list) = b#maxTermPrefix list")
  apply(rename_tac e A1 w1 B1 ea list b w)(*strict*)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac e A1 w1 B1 ea list b w a)(*strict*)
  apply(subgoal_tac "maxTermPrefix (X # liftA to2) = []")
  apply(rename_tac e A1 w1 B1 ea list b w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list b w a)(*strict*)
  apply (metis list.simps(3) maxTermPrefix_terminal_front)
  apply(rename_tac e A1 w1 B1 ea list b w ba)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (teB ba # liftA to2) = [ba]")
  apply(rename_tac e A1 w1 B1 ea list b w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list ba)(*strict*)
  apply(erule_tac
      x="ia"
      in allE)+
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list b w ba)(*strict*)
  apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
  apply(rename_tac e A1 w1 B1 ea list b w)(*strict*)
  apply (metis maxTermPrefix_pull_out append_Nil2 maxTermPrefix_liftA maxTermPrefix_shift)
  apply(rename_tac e A1 w1 B1 ea a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea list aa)(*strict*)
  apply(rename_tac w A2)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  prefer 2
  apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(erule_tac
      x="dx2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA F2]\<rparr>"
      in allE)
  apply(erule_tac
      x="take ia \<pi>2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = teA A2 # w\<rparr>"
      in allE)
  apply(erule_tac
      P="cfgLMTD G dx2 \<lparr>cfg_conf = [teA F2]\<rparr> (take ia \<pi>2) \<lparr>cfg_conf = teA A2 # w\<rparr>"
      in impE)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule_tac
      t="min (length (\<pi>2)) ia"
      and s="ia"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w A2 eb ec ed ee)(*strict*)
  apply(rule_tac
      m="(length (\<pi>2))-ia"
      and v="map Some (drop ia ((\<pi>2)))"
      in get_labels_drop_tail)
  apply(rename_tac e A1 w1 B1 ea w A2 eb ec ed ee)(*strict*)
  apply(clarsimp)
  apply (metis List.map_append append_take_drop_id)
  apply(rename_tac e A1 w1 B1 ea w A2 eb ec ed ee)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(erule_tac
      P="\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = [teA F2]\<rparr> = liftB w1 @ liftA w2"
      in impE)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="[SSX]" for SSX
      in exI)
  apply(clarsimp)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w A2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w A2 w1a w2)(*strict*)
  apply(case_tac w1a)
  apply(rename_tac e A1 w1 B1 ea w A2 w1a w2)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea w A2 w1a w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w A2 w1a w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w A2 w2)(*strict*)
  apply(case_tac w2)
  apply(rename_tac e A1 w1 B1 ea w A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w A2 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea a list)(*strict*)
  apply(rename_tac A2 w2)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(thin_tac "(e = None) = (ea = None)")
  apply(thin_tac "(e = Some (\<pi>1 ! (ia - Suc 0))) = (ea = Some (\<pi>2 ! (ia - Suc 0)))")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(rule_tac
      ?w1.0="A1#w1@[B1]"
      and ?w2.0="A2#w2"
      and ?d1.0="derivation_drop dx1 ia"
      and ?d2.0="derivation_drop dx2 ia"
      and ?\<pi>1.0="drop ia \<pi>1"
      and ?\<pi>2.0="drop ia \<pi>2"
      in realizable_length_eq)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule notfinishingL_drop)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule notfinishingL_drop)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(rule_tac
      d="dx1"
      and \<alpha>="[]"
      and w="[F1]"
      and \<pi>="take ia \<pi>1"
      and n="ia"
      in only_l3_nonterminals_butlast_preserved)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(simp add: only_l3_nonterminals_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule_tac
      n="ia"
      and d="dx1"
      in cfgLM.trans_der_crop)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  apply(case_tac v1)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2)(*strict*)
  apply(case_tac v2)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 w2 a list)(*strict*)
  apply(rule_tac
      xs="list"
      in rev_cases)
  apply(rename_tac e w1 B1 ea A2 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 w2 a list ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 w2 a ys y)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac e w1 ea A2 w2 a ys y)(*strict*)
  apply(subgoal_tac "w1=ys")
  apply(rename_tac e w1 ea A2 w2 a ys y)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac e w1 ea A2 w2 a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(rule_tac
      d="dx2"
      and \<alpha>="[]"
      and w="[F2]"
      and \<pi>="take ia \<pi>2"
      and n="ia"
      in only_l3_nonterminals_butlast_preserved)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(simp add: only_l3_nonterminals_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule_tac
      n="ia"
      and d="dx2"
      in cfgLM.trans_der_crop)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  apply(case_tac v1)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2)(*strict*)
  apply(case_tac v2)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 v2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 a list)(*strict*)
  apply(subgoal_tac "w2=list")
  apply(rename_tac e A1 w1 B1 ea w2 a list)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea a list)(*strict*)
  apply(rule_tac
      xs="list"
      in rev_cases)
  apply(rename_tac e A1 w1 B1 ea a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea a list ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply (metis drop_map)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule_tac
      xs="drop ia \<pi>1"
      in rev_cases)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(erule_tac
      x="p"
      and A="set (butlast \<pi>1)"
      in ballE)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  prefer 2
  apply(subgoal_tac "p \<in> set (butlast \<pi>1)")
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(thin_tac "p \<notin> set (butlast \<pi>1)")
  apply(rule_tac
      A="set ys"
      in set_mp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(rule_tac
      B="set(butlast(drop ia \<pi>1))"
      in subset_trans)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply (metis drop_butlast set_drop_subset)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(rule_tac
      xs="drop ia \<pi>2"
      in rev_cases)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(erule_tac
      x="p"
      and A="set (butlast \<pi>2)"
      in ballE)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  prefer 2
  apply(subgoal_tac "p \<in> set (butlast \<pi>2)")
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(thin_tac "p \<notin> set (butlast \<pi>2)")
  apply(rule_tac
      A="set ys"
      in set_mp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(rule_tac
      B="set(butlast(drop ia \<pi>2))"
      in subset_trans)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply (metis drop_butlast set_drop_subset)
  apply(rename_tac e A1 w1 B1 ea A2 w2 ys y p b A)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(case_tac "derives G (drop ia \<pi>2)=[]")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(subgoal_tac "realizable G (drop ia \<pi>2) = drop ia \<pi>2")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(case_tac "strict_prefix (realizable G (drop ia \<pi>2)) (drop ia \<pi>2)")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c ca cb)(*strict*)
  apply(erule_tac
      x="cb"
      in allE)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list)(*strict*)
  apply(case_tac "derives G (drop ia \<pi>2)")
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="derivation_drop dx2 ia"
      in existence_of_realizable)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' ca d)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' ca d cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(subgoal_tac "prod_lhs (hd (drop ia \<pi>2)) = A2")
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="derivation_drop dx2 ia"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb ci' l r)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb ci' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb l r)(*strict*)
  apply(case_tac l)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb l r)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb l r ab listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w eb l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista \<pi>' d w eb)(*strict*)
  apply(case_tac "drop ia \<pi>2")
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista \<pi>' d w eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista \<pi>' d w eb ab listb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="\<pi>2!ia"
      and s="ab"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista \<pi>' d w eb ab listb)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista \<pi>' d w eb ab listb)(*strict*)
  apply (metis nth_via_drop)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  prefer 2
  apply(rule_tac
      ca="\<lparr>cfg_conf = w\<rparr>"
      and \<pi>'="\<pi>'"
      and G="G"
      and d="derivation_drop dx2 ia"
      and da="d"
      in realizable_eq_from_existence)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list aa lista \<pi>' d w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(subgoal_tac "w=aa#lista")
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  prefer 2
  apply(simp add: derives_def)
  apply(erule_tac
      P="setA w = {}"
      in disjE)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(subgoal_tac "(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia \<pi>2)))]\<rparr> (realizable G (drop ia \<pi>2)) c) = \<lparr>cfg_conf=w\<rparr>")
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(rule the_equality)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w ca da)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w ca da cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da cfg_confa)(*strict*)
  apply(rename_tac w')
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf=w'\<rparr>=\<lparr>cfg_conf=w\<rparr>")
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(rule cfgLM_trans_der_unique_result)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w da w')(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d)(*strict*)
  apply(erule_tac
      P="setA lista = {} \<and> (case aa of teA a \<Rightarrow> {a} | teB b \<Rightarrow> {}) = {}"
      in disjE)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>l'. liftB l' = lista")
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterB lista"
    in exI)
  apply (rule liftBDeConv2)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa d l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac aa)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa d l' ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa d l' b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca cb)(*strict*)
  apply(subgoal_tac "cb=a#list")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca cb)(*strict*)
  prefer 2
  apply (metis drop_append2)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  prefer 2
  apply(rule_tac
    i="length(realizable G (drop ia \<pi>2))"
    and d="derivation_drop dx2 ia"
    in cfgLM.trans_der_position_detail)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  apply(rule prefix_length)
  apply(rule_tac
    v="a#list"
    in prefixI)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ci cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ci w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  prefer 2
  apply(rule_tac
    ?v1.0="w"
    and ?w1.0="[teA (prod_lhs (hd (drop ia \<pi>2)))]"
    and \<pi>="realizable G (drop ia \<pi>2)"
    and ?w2.0="liftA w2"
    and ?d2.0="d"
    and ?d1.0="derivation_drop dx2 ia"
    in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule_tac
    m="((length (\<pi>2))-ia)-(length (realizable G (drop ia \<pi>2)))"
    and v="map Some (a # list)"
    in get_labels_drop_tail)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="map Some (realizable G (drop ia \<pi>2)) @ Some a # map Some list"
    and s="map Some (drop ia \<pi>2)"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule_tac
    t="drop ia \<pi>2"
    and s="realizable G (drop ia \<pi>2) @ a # list"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(simp (no_asm))
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule_tac
    t="length (realizable G (drop ia \<pi>2)) + (length \<pi>2 - (ia + length (realizable G (drop ia \<pi>2))))"
    and s="length \<pi>2 - ia"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule hlpXX1)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule_tac
    t="length \<pi>2 - ia"
    and s="length(drop ia \<pi>2)"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(rule prefix_length)
  apply(rule_tac
    v="a#list"
    in prefixI)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    eij="ed"
    and cij="\<lparr>cfg_conf = X # liftA to2\<rparr>"
    and ci="\<lparr>cfg_conf = teB b # liftB l' @ liftA w2\<rparr>"
    and ei="eb"
    and d="dx2"
    and i="length (realizable G (drop ia \<pi>2))+ia"
    and j="length (\<pi>2)-(ia+length (realizable G (drop ia \<pi>2)))"
    in cfgLM.derivation_monotonically_inc)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(simp add: derivation_drop_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ee ef eg)(*strict*)
  apply(case_tac eb)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ee ef eg aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(rule_tac
    t="length (realizable G (drop ia \<pi>2)) + ia + (length \<pi>2 - (ia + length (realizable G (drop ia \<pi>2))))"
    and s="length \<pi>2"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(rule hlpXX3)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(subgoal_tac "length (realizable G (drop ia \<pi>2)) < length \<pi>2 -ia")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(rule_tac
    t="length \<pi>2 - ia"
    and s="length(drop ia \<pi>2)"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(rule_tac
    v="a#list"
    in hlpXX2)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb ec ed ee ef eg)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (teB b # liftB l' @ liftA w2) = b#(maxTermPrefix (liftB l' @ liftA w2))")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w aa)(*strict*)
  apply(subgoal_tac "maxTermPrefix (X # liftA to2) = []")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w aa)(*strict*)
  apply (metis list.simps(3) maxTermPrefix_terminal_front)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ba)(*strict*)
  apply(clarsimp)
  apply(erule_tac
    x="ia+(length (realizable G (drop ia \<pi>2)))"
    and P="\<lambda>X. X < length \<pi>2 \<longrightarrow> hd (cfg_conf (the (case_option None (case_derivation_configuration (\<lambda>e. Some)) (dx2 X)))) \<noteq> teB ba"
    in allE)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ba)(*strict*)
  apply(simp add: derivation_drop_def get_configuration_def)
  apply(case_tac eb)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w ba aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(subgoal_tac "length (realizable G (drop ia \<pi>2)) + ia = ia+length (realizable G (drop ia \<pi>2)) ")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(clarsimp)
  apply(erule impE)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(subgoal_tac "length (realizable G (drop ia \<pi>2)) < length \<pi>2 -ia")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(rule_tac
    t="length \<pi>2 - ia"
    and s="length(drop ia \<pi>2)"
    in ssubst)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(rule_tac
    v="a#list"
    in hlpXX2)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teB ba # liftA to2) = [ba]")
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply (metis maxTermPrefix_leading_terminal)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca w ba)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea w2 c a list d l' b ca eb w)(*strict*)
  apply (metis maxTermPrefix_pull_out append_Nil2 maxTermPrefix_liftA maxTermPrefix_shift)
  apply(rename_tac e A1 w1 B1 ea w2 c a list aa lista d)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "realizable G (drop ia \<pi>1) = drop ia \<pi>1")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply (metis drop_length2 length_map prefix_is_equal_by_length)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length \<pi>1 - ia = length \<pi>2 - ia")
  apply(thin_tac "drop ia \<pi>1 \<sqsubseteq> drop ia \<pi>1")
  apply(thin_tac "drop ia \<pi>2 \<sqsubseteq> drop ia \<pi>2")
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(rule_tac
    d="derivation_drop dx1 ia"
    in entire_realizable_derives_in_context)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  prefer 2
  apply(rule_tac
    d="derivation_drop dx2 ia"
    in entire_realizable_derives_in_context)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c)(*strict*)
  apply(case_tac "derives G (drop ia \<pi>2)")
  apply(rename_tac e A1 w1 B1 ea A2 w2 c)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c list)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c list)(*strict*)
  prefer 2
  apply(rule liftA_append)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c l1 l2)(*strict*)
  apply(subgoal_tac "w2=l2")
  apply(rename_tac e A1 w1 B1 ea A2 w2 c l1 l2)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 w2 c l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(thin_tac "liftA l1 @ liftA l2 = liftA (l1 @ l2)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(rule_tac
    d="dx1"
    and \<alpha>="[]"
    and w="[F1]"
    and \<pi>="take ia \<pi>1"
    and n="ia"
    in only_l3_nonterminals_butlast_preserved)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(simp add: only_l3_nonterminals_def)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(rule_tac
    n="ia"
    and d="dx1"
    in cfgLM.trans_der_crop)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(rule_tac
    d="dx2"
    and \<alpha>="[]"
    and w="[F2]"
    and \<pi>="take ia \<pi>2"
    and n="ia"
    in only_l3_nonterminals_butlast_preserved)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(simp add: only_l3_nonterminals_def)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(rule_tac
    n="ia"
    and d="dx2"
    in cfgLM.trans_der_crop)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1 v1a v2 v2a)(*strict*)
  apply(case_tac v1)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1 v1a v2 v2a)(*strict*)
  prefer 2
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1 v1a v2 v2a a list)(*strict*)
  apply(force)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1 v1a v2 v2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1a v2 v2a)(*strict*)
  apply(case_tac v2)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1a v2 v2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A1 w1 B1 ea A2 c l1 l2 v1a v2 v2a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 c l1 l2 v1a v2a a list)(*strict*)
  apply(rule_tac
    xs="list"
    in rev_cases)
  apply(rename_tac e w1 B1 ea A2 c l1 l2 v1a v2a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 c l1 l2 v1a v2a a list ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 B1 ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac e w1 ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  apply(subgoal_tac "w1=ys")
  apply(rename_tac e w1 ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac e w1 ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  apply(case_tac v1a)
  apply(rename_tac e ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  prefer 2
  apply(rename_tac e ea A2 c l1 l2 v1a v2a a ys y aa list)(*strict*)
  apply(force)
  apply(rename_tac e ea A2 c l1 l2 v1a v2a a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea A2 c l1 l2 v2a a ys y)(*strict*)
  apply(case_tac v2a)
  apply(rename_tac e ea A2 c l1 l2 v2a a ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea A2 c l1 l2 v2a a ys y aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 l2 a ys y aa list)(*strict*)
  apply(subgoal_tac "l2=list")
  apply(rename_tac e ea c l1 l2 a ys y aa list)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(force)
  apply(rename_tac e ea c l1 l2 a ys y aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 a ys y aa list)(*strict*)
  apply(case_tac a)
  apply(rename_tac e ea c l1 a ys y aa list q b)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac e ea c l1 a ys y aa list q b)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 a ys y aa list q b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q b)(*strict*)
  apply(simp add: only_l3_nonterminals_def)
  apply(erule_tac
    x="[]"
    and P="\<lambda>w1. \<forall>w2 xA. cons_l2 q b # ys = w1 @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
    in allE)
  apply(clarsimp)
  apply(rename_tac e ea c l1 a ys y aa list q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(subgoal_tac "cropTol3l2_single (cons_l3 q1 b q2) = cropTol3l2_single aa")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="derivation_drop dx1 ia"
    in existence_of_realizable)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="derivation_drop dx1 ia"
    and da="d"
    in realizable_eq_from_existence)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="derivation_drop dx2 ia"
    in existence_of_realizable)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 \<pi>' ca d)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="derivation_drop dx2 ia"
    and da="da"
    in realizable_eq_from_existence)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(rule_tac
    t="cfg_productions G"
    and s="cfg_step_labels G"
    in ssubst)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(rule cfgLM.trans_der_all_step_labels)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca d \<pi>'a cb da)(*strict*)
  apply(rename_tac dy1 \<pi>'a cb dy2)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(subgoal_tac "prod_lhs (hd (drop ia \<pi>1)) = cons_l3 q1 b q2")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx1"
    and i="ia"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 ci' l r)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 ci' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  apply(case_tac l)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  prefer 2
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2)(*strict*)
  apply(case_tac "drop ia \<pi>1")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="\<pi>1 ! ia"
    and s="a"
    in ssubst)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  apply (metis nth_via_drop)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(subgoal_tac "prod_lhs (hd (drop ia \<pi>2)) = aa")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dx2"
    and i="ia"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 ci' l r)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 ci' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  apply(case_tac l)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  prefer 2
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 cb dy2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2)(*strict*)
  apply(case_tac "drop ia \<pi>2")
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="\<pi>2 ! ia"
    and s="a"
    in ssubst)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2 a lista)(*strict*)
  apply (metis nth_via_drop)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2 ca dy1 \<pi>'a cb dy2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2 cfg_confa)(*strict*)
  apply(case_tac cb)
  apply(rename_tac e ea c l1 ys y list q1 b q2 ca dy1 cb dy2 cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 cfg_confa cfg_confaa)(*strict*)
  apply(rename_tac x1 x2)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  apply(subgoal_tac "x2=X # liftA l1")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  prefer 2
  apply(simp add: derives_def)
  apply(subgoal_tac "(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia \<pi>2)))]\<rparr> (drop ia \<pi>2) c) = \<lparr>cfg_conf=x2\<rparr>")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  apply(rule_tac the_equality)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  apply(rule_tac
    x="dy2"
    in exI)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 ca d)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 ca d cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d cfg_confa)(*strict*)
  apply(rename_tac ww)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf=x2\<rparr>=\<lparr>cfg_conf=ww\<rparr>")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(rule cfgLM_trans_der_unique_result)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  apply(subgoal_tac "x1=derives G (drop ia \<pi>1)")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  prefer 2
  apply(simp add: derives_def)
  apply(subgoal_tac "(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cons_l3   q1 b q2)]\<rparr> (drop ia \<pi>1) c) = \<lparr>cfg_conf=x1\<rparr>")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  apply(rule the_equality)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  apply(rule_tac
    x="dy1"
    in exI)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 ca d)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 ca d cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d cfg_confa)(*strict*)
  apply(rename_tac ww)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf=x1\<rparr>=\<lparr>cfg_conf=ww\<rparr>")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(rule cfgLM_trans_der_unique_result)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1 d ww)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 x1)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2)(*strict*)
  apply(case_tac "derives G (drop ia \<pi>1)")
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2)(*strict*)
  apply(case_tac X)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 a)(*strict*)
  prefer 2
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 ba)(*strict*)
  apply(clarsimp)
  apply(case_tac ys)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 ba a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 a)(*strict*)
  apply(clarsimp)
  apply(rename_tac X)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  prefer 2
  apply(rule_tac
    ?w2.0="[]"
    and ?w1.0="X#l1"
    and ?d1.0="dy2"
    and ?d2.0="dy1"
    in compatible_productions_l3_does_not_end_faster)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply (metis drop_map)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(case_tac "prod_lhs (hd (drop ia \<pi>2))")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X q ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 X)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 lista)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 lista)(*strict*)
  prefer 2
  apply(rule liftA_append)
  apply(force)
  apply(rename_tac e ea c l1 ys y list q1 b q2 dy1 dy2 lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(subgoal_tac "l1a@ys@[y]=to1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  prefer 2
  apply(rule liftA_inj)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(thin_tac "liftA l1a @ liftA ys @ [teA y] = liftA to1")
  apply(clarsimp)
  apply(thin_tac "liftA l1a @ liftA l2 = liftA (l1a @ l2)")
  apply(case_tac "l2=[]")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(thin_tac "liftA l2 \<noteq> []")
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  prefer 2
  apply(rule_tac
    ?d1.0="dy2"
    and ?d2.0="dy1"
    in compatible_productions_l3_grows_faster_than_unknown_ext)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply (metis drop_map)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2a)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(case_tac "prod_lhs (hd (drop ia \<pi>2))")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2a q ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y list q1 b q2 dy1 dy2 l1a l2a q ba)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(clarsimp)
  apply(rename_tac e ea ys y list q2 dy1 dy2 l1a l2a q ba)(*strict*)
  apply(rule_tac
    xs="list"
    in rev_cases)
  apply(rename_tac e ea ys y list q2 dy1 dy2 l1a l2a q ba)(*strict*)
  prefer 2
  apply(rename_tac e ea ys y list q2 dy1 dy2 l1a l2a q ba ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y q2 dy1 dy2 l1a l2a q ba ysa ya)(*strict*)
  apply(thin_tac "only_l3_nonterminals (cons_l3 q ba q2 # ys)")
  apply(simp add: only_l3_nonterminals_def)
  apply(erule_tac
    x="[]"
    in allE)
  apply(clarsimp)
  apply(rename_tac e ea ys y list q2 dy1 dy2 l1a l2a q ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(subgoal_tac "\<exists>c. c \<noteq> [] \<and> l1 @ c = l1a @ l2")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 c)(*strict*)
  apply(rule_tac
    x="liftA c"
    in exI)
  apply(rule conjI)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 c)(*strict*)
  apply (metis liftAMap map_is_Nil_conv)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 c)(*strict*)
  apply (metis List.map_append liftAMap)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(erule_tac
    P="\<exists>n1\<le>Suc (length l1a + length ys). l1a @ l2 = cropTol3l2 (take n1 l1a @ take (n1 - length l1a) ys @ take (n1 - (length l1a + length ys)) [y])"
    in disjE)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  prefer 2
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(erule disjE)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  prefer 2
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(case_tac "n2 - length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="take n2 l1"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ysa ya)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  apply(rule_tac
    xs="take n2 l1"
    in rev_cases)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a n2 ya ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  apply (metis append_assoc not_Cons_self mutual_prefix_implies_equality2 mutual_prefix_implies_equality prefix_append prefix_transitive takePrecise take_max_no_append take_prefix)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n2=Suc nat+length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(rule_tac
    xs="take (Suc nat) list"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(subgoal_tac "butlast (l1 @ ysa @ [ya]) = l1@ysa")
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(erule disjE)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  prefer 2
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(subgoal_tac "length ((take n1 l1a @ take (n1 - length l1a) ys @ take (n1 - (length l1a + length ys)) [y])) \<le> length l1a")
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(thin_tac "length (cropTol3l2 (take n1 l1a @ take (n1 - length l1a) ys @ take (n1 - (length l1a + length ys)) [y])) \<le> length l1a")
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n1 = length l1a \<and> l2 = []")
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  prefer 2
  apply(simp add: cropTol3l2_def)
  apply(case_tac "n1 = 0 \<or> l1a = []")
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(rule_tac
    t="length (take n1 l1a @ take (n1 - length l1a) ys @ take (n1 - (length l1a + length ys)) [y])"
    and s="length (cropTol3l2 (take n1 l1a @ take (n1 - length l1a) ys @ take (n1 - (length l1a + length ys)) [y]))"
    in subst)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(rule cropTol3l2_length)
  apply(rename_tac e ea ys y q1 b q2 dy1 dy2 l1a l2 n1)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(case_tac "n1 - (length l1a + length ys)")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(clarsimp)
  apply(case_tac "n1 - length l1a")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n1 = length l1a \<and> l2 = []")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  prefer 2
  apply(rule cropTol3l2_rest_is_junk)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n1=Suc nat+length l1a")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2 nat)(*strict*)
  apply(rule_tac
    xs="take (Suc nat) ys"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="l2"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2 nat ysa ya ysb yb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya ysb yb)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya ysb)(*strict*)
  apply(subgoal_tac "butlast (l1a @ ysa @ [ya]) = l1a@ysa")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya ysb)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya ysb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(thin_tac "butlast (l1a @ ysa @ [ya]) = l1a @ ysa")
  apply(case_tac "(n2 = 0 \<or> l1 = []) \<and> (n2 \<le> length l1 \<or> list = [])")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply (metis Nat.add_0_right Nil_is_append_conv append_Nil diff_0_eq_0 le_0_eq list.simps(2) list.size(3) take_0)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(case_tac "n2 - length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="take n2 l1"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya ysb yb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya yb)(*strict*)
  apply (metis append_assoc drop_length_append not_Cons_self mutual_prefix_implies_equality2 prefix_append prefix_transitive takePrecise take_all take_all_length take_max_no_append take_prefix)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n2=Suc nata+length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata)(*strict*)
  apply(rule_tac
    xs="take (Suc nata) list"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast (l1 @ ysb @ [yb]) = l1 @ ysb")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="ysb@[cropTol3l2_single ya]"
    in exI)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(case_tac "n2-length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n2=Suc nata+length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata)(*strict*)
  apply(rule_tac
    xs="take (Suc nata) list"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast (l1 @ ysb @ [yb]) = l1 @ ysb")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya nata ysb yb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="ysb@[cropTol3l2_single ya]"
    in exI)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n1=Suc nat+length l1a+length ys")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n1 n2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2)(*strict*)
  apply(subgoal_tac "l2=ys@[cropTol3l2_single y]")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2)(*strict*)
  prefer 2
  apply(simp add: cropTol3l2_def)
  apply(subgoal_tac "butlast (l1a @ ys @ [y])=l1a@ys")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2)(*strict*)
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a l2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(case_tac "n2-length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="take n2 l1"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ysa ya)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "cropTol3l2 (ysa @ [ya]) = ysa@[cropTol3l2_single ya]")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ysa ya)(*strict*)
  prefer 2
  apply(simp add: cropTol3l2_def)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ysa ya)(*strict*)
  apply(clarsimp)
  apply(thin_tac "l1a @ ys @ [cropTol3l2_single y] = cropTol3l2 (l1a @ ys @ [y])")
  apply(simp add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  apply(subgoal_tac "butlast (l1a @ ys @ [y]) = SSX" for SSX)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 ya)(*strict*)
  apply(clarsimp)
  apply (metis append_assoc not_Cons_self mutual_prefix_implies_equality2 mutual_prefix_implies_equality prefix_append prefix_transitive takePrecise take_max_no_append take_prefix)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n2=Suc nat+length l1")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a n2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(thin_tac "l1a @ ys @ [cropTol3l2_single y] = cropTol3l2 (l1a @ ys @ [y])")
  apply(simp add: cropTol3l2_def)
  apply(subgoal_tac "butlast (l1a @ ys @ [y]) = SSX" for SSX)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(clarsimp)
  apply(thin_tac "butlast (l1a @ ys @ [y]) = l1a @ ys")
  apply(case_tac "l1 = [] \<and> list = []")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    xs="take (Suc nat) list"
    in rev_cases)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast (l1 @ ysa @ [ya]) = l1 @ ysa")
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  prefer 2
  apply(rule butlast_direct)
  apply(force)
  apply(rename_tac e ea l1 ys y list q1 b q2 dy1 dy2 l1a nat ysa ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="ysa@[cropTol3l2_single y]"
    in exI)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (derivation_drop dx1 ia) \<lparr>cfg_conf = teA (cons_l3   q1 b q2) # liftA ys @ [teA y]\<rparr> (drop ia \<pi>1) \<lparr>cfg_conf = X # liftA to1\<rparr>")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (derivation_drop dx2 ia) \<lparr>cfg_conf = teA aa # liftA list\<rparr> (drop ia \<pi>2) \<lparr>cfg_conf = X # liftA l1 @ liftA list\<rparr>")
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(thin_tac "realizable G (drop ia \<pi>2) = drop ia \<pi>2")
  apply(thin_tac "derives G (drop ia \<pi>1) @ liftA ys @ [teA y] = X # liftA to1")
  apply(thin_tac "realizable G (drop ia \<pi>1) = drop ia \<pi>1")
  apply(thin_tac "derives G (drop ia \<pi>1) @ c = X # liftA nt")
  apply(thin_tac "derives G (drop ia \<pi>2) = X # liftA l1")
  apply(thin_tac "c \<noteq> []")
  apply(rule_tac
    ?w1.0="ys@[y]"
    and i="ia"
    and ?t2.0="l1@list"
    and ?d1.0="dx1"
    and ?d2.0="dx2"
    in compatible_derivation_from_lxlx_remain_compatible_for_generations)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply (metis length_map)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  apply(erule_tac
    x="iaa"
    in allE)+
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  prefer 2
  apply(rule_tac
    i="iaa"
    and d="dx1"
    in cfgLM.trans_der_position_detail)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  apply(simp add: split_TSstructure_def)
  apply(force)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  apply(force)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa eb ci)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
     apply(erule_tac
    x="iaa"
    in allE)+
     apply(clarsimp)
     apply(subgoal_tac "X" for X)
      apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
      prefer 2
      apply(rule_tac
    i="iaa"
    and d="dx2"
    in cfgLM.trans_der_position_detail)
        apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
       apply(force)
      apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
      apply(force)
     apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea l1 ys y aa list q1 b q2 ba iaa eb ci)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
   apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  apply(rename_tac e ea c l1 ys y aa list q1 b q2)(*strict*)
  apply(force)
  done

lemma newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix: "
  (\<exists>n1\<le>length (ESplitItem_to (S1 ! i)). (restrict_newto S1 i) = cropTol3l2(take n1 (ESplitItem_to (S1 ! i)))) \<or> (restrict_newto S1 i) = (ESplitItem_to (S1 ! i))"
  apply(simp add: restrict_newto_def new_post_sig_def drop_and_crop_def butn_def)
  apply(clarsimp)
  apply(rule_tac
      xs="take (length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_ignore (S1 ! i))"
      in rev_cases)
   apply(clarsimp)
   apply(thin_tac "take (length (ESplitItem_to (S1 ! i))) (cropTol3l2 (take (length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_to (S1 ! i)))) \<noteq> ESplitItem_to (S1 ! i)")
   apply(erule disjE)
    apply(clarsimp)
    apply(rule_tac
      x="length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)"
      in exI)
    apply(rule conjI)
     apply(force)
    apply(simp add: cropTol3l2_def)
   apply(clarsimp)
   apply(rule_tac
      x="length (ESplitItem_to (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)"
      in exI)
   apply(clarsimp)
   apply(simp add: cropTol3l2_def)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(subgoal_tac "butlast (take (length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_to (S1 ! i)) @ ys @ [y]) = SSX" for SSX)
   apply(rename_tac ys y)(*strict*)
   prefer 2
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(thin_tac "butlast (take (length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_to (S1 ! i)) @ ys @ [y]) = take (length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i)) (ESplitItem_to (S1 ! i)) @ ys")
  apply(rename_tac ys y)(*strict*)
  apply(case_tac "min (length (ESplitItem_to (S1 ! i))) (length (ESplitItem_to (S1 ! i)) + length (ESplitItem_ignore (S1 ! i)) - length (restrict_toberemovedX S1 ! Suc i))=length (ESplitItem_to (S1 ! i))")
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  done

lemma restrict_newignore_prefix_of_ESplitItem_ignore_butlast: "
  prefix (butlast(restrict_newignore S x)) (butlast(ESplitItem_ignore (S ! x)))"
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
      t="drop (length (ESplitItem_to (S ! x))) (drop_and_crop (ESplitItem_to (S ! x) @ ESplitItem_ignore (S ! x)) (length (restrict_toberemovedX S ! Suc x)))"
      in ssubst)
   apply(rule cropTol3l2_drop_butn_drop_and_crop)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
      xs="take (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x))"
      in rev_cases)
   apply(rule_tac
      t="take (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x))"
      and s="[]"
      in ssubst)
    apply(force)
   apply(thin_tac "take (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x)) = []")
   apply(simp add: cropTol3l2_def)
   apply(simp add: prefix_def)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_def)
  apply(rule_tac
      t="ESplitItem_ignore (S ! x)"
      in subst)
   apply(rename_tac ys y)(*strict*)
   apply(rule_tac
      n="length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)"
      in append_take_drop_id)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      t="take (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x))"
      and s="ys@[y]"
      in ssubst)
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(thin_tac "take (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x)) = ys @ [y]")
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      xs="drop (length (ESplitItem_ignore (S ! x)) - length (restrict_toberemovedX S ! Suc x)) (ESplitItem_ignore (S ! x))"
      in rev_cases)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac ys)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="butlast SSX" for SSX
      in ssubst)
   apply(rename_tac ys y ysa ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ys y ysa ya)(*strict*)
  apply(simp add: prefix_def)
  done

lemma restrict_newignore_shorter_than_ESplitItem_ignore: "
  length (restrict_newignore S i) \<le> length (ESplitItem_ignore (S!i))"
  apply(simp add: restrict_newignore_def new_post_sig_def)
  apply(rule_tac
      t="length (drop_and_crop (ESplitItem_to (S ! i) @ ESplitItem_ignore (S ! i)) (length (restrict_toberemovedX S ! Suc i)))"
      in ssubst)
   apply(rule drop_and_crop_length)
  apply(clarsimp)
  done

lemma restrict_newprods_preserves_length: "
  n<length S1
  \<Longrightarrow> length (restrict_newprods G' G (S1 @ S2) n) = length (ESplitItem_prods (S1 ! n))"
  apply(simp add: restrict_newprods_def)
  apply(subgoal_tac "(S1 @ S2)!n = SSX" for SSX)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule conjI)
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
  apply(clarsimp)
  apply (metis liftB_reflects_length)
  done

lemma nonabstracted_productions_are_unmodified: "
  PSplitItem_prods (restrict G' G (S@\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>@\<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>#S1) (Suc(length S)) ! n) ! m = teB b
  \<Longrightarrow> n < Suc(length S)
  \<Longrightarrow> Suc m < length (ESplitItem_prods ((S@[\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>@\<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>])!n))
  \<Longrightarrow> length S = n \<longrightarrow> \<not> length \<pi> \<le> m
  \<Longrightarrow> ESplitItem_prods ((S@\<lparr>ESplitItem_elim = el', ESplitItem_from = fr', ESplitItem_ignore = ig', ESplitItem_elim_prods = el\<pi>', ESplitItem_prods = \<pi>, ESplitItem_elem = elem', ESplitItem_to = to'\<rparr>#S2)!n)!m = b"
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "length(nat_seq 0 (length S)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "nat_seq 0 (length S) ! n = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (nat_seq 0 (length \<pi> - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq 0 (length \<pi> + length \<pi>' - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(case_tac "n=length S")
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length \<pi> + length \<pi>' - Suc 0) ! m = SSX" for SSX)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(force)
    apply(force)
   apply(simp add: restrict_newprods_def)
   apply(case_tac "restrict_newignore (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>@\<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) (length S) = []")
    apply(clarsimp)
    apply(simp add: restrict_newprodsX_def)
    apply(case_tac "\<pi>@\<pi>'=[]")
     apply(clarsimp)
    apply(subgoal_tac "(if False then [] else map (\<lambda>i. if restrict_newprodsXX G i (\<pi> @ \<pi>') elem (restrict_newto (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) (length S)) then teB ((\<pi> @ \<pi>') ! i) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' ((\<pi> @ \<pi>') ! i))) (nat_seq 0 (length (\<pi> @ \<pi>') - Suc 0))) ! m = teB b")
     prefer 2
     apply(rule_tac
      t="False"
      and s="\<pi> = [] \<and> \<pi>' = []"
      in ssubst)
      apply(force)
     apply(force)
    apply(thin_tac "(if \<pi> = [] \<and> \<pi>' = [] then [] else map (\<lambda>i. if restrict_newprodsXX G i (\<pi> @ \<pi>') elem (restrict_newto (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) (length S)) then teB ((\<pi> @ \<pi>') ! i) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' ((\<pi> @ \<pi>') ! i))) (nat_seq 0 (length (\<pi> @ \<pi>') - Suc 0))) ! m = teB b")
    apply(clarsimp)
    apply(subgoal_tac "map (\<lambda>i. if restrict_newprodsXX G i (\<pi> @ \<pi>') elem (restrict_newto (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) (length S)) then teB ((\<pi> @ \<pi>') ! i) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' ((\<pi> @ \<pi>') ! i))) (nat_seq 0 (length \<pi> + length \<pi>' - Suc 0)) ! m = SSX" for SSX)
     prefer 2
     apply(rule nth_map)
     apply(force)
    apply(clarsimp)
    apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length \<pi> + length \<pi>' - Suc 0) ! m) (\<pi> @ \<pi>') elem (restrict_newto (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) (length S))")
     prefer 2
     apply(clarsimp)
    apply(clarsimp)
    apply(rule sym)
    apply(rule nth_append_1)
    apply(force)
   apply(clarsimp)
   apply(rule_tac
      t="\<pi>!m"
      and s="(\<pi>@\<pi>')!m"
      in subst)
    apply(rule nth_append_1)
    apply(force)
   apply(rule liftB_nth2)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "(S @ \<lparr>ESplitItem_elim = el', ESplitItem_from = fr', ESplitItem_ignore = ig', ESplitItem_elim_prods = el\<pi>', ESplitItem_prods = \<pi>, ESplitItem_elem = elem', ESplitItem_to = to'\<rparr> # S2) ! n=S!n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S @ \<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = elem, ESplitItem_to = to\<rparr> # S1) ! n=S!n")
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(clarsimp)
  apply(simp add: restrict_newprods_def)
  apply(subgoal_tac " (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi>, ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) ! n = SSX" for SSX)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(subgoal_tac "(S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) ! n = SSX" for SSX)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(case_tac "restrict_newignore (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) n = []")
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
   apply(case_tac "ESplitItem_prods ((S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) ! n) = []")
    apply(clarsimp)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S ! n)) - Suc 0)) = SSX" for SSX)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(clarsimp)
   apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length (ESplitItem_prods (S ! n)) - Suc 0) ! m) (ESplitItem_prods (S ! n)) (ESplitItem_elem (S ! n)) (restrict_newto (S @ [\<lparr>ESplitItem_elim = el, ESplitItem_from = fr, ESplitItem_ignore = ig, ESplitItem_elim_prods = el\<pi>, ESplitItem_prods = \<pi> @ \<pi>', ESplitItem_elem = elem, ESplitItem_to = to\<rparr>]) n)")
    prefer 2
    apply(clarsimp)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 (length (ESplitItem_prods (S ! n)) - Suc 0) ! m = SSX" for SSX)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "m<length(ESplitItem_prods (S ! n))")
   apply (metis liftB_nth DT_two_elements.inject(2))
  apply(clarsimp)
  done

lemma nonabstracted_productions_are_unmodified2: "
  PSplitItem_prods
  (restrict G' G
  (S1 @ S1') ((length S1)+k) !
          n) !
        m =
        teB ba
  \<Longrightarrow> n<length S1
  \<Longrightarrow> m < length (ESplitItem_prods (S1!n))
  \<Longrightarrow> ESplitItem_prods (S1 ! n) ! m = ba"
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "length(nat_seq 0 (length S1 + min (length S1') k - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "nat_seq 0 (length S1 + min (length S1') k - Suc 0) ! n = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "(S1 @ take k S1') ! n = SSX" for SSX)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(simp add: restrict_newprods_def)
  apply(case_tac "restrict_newignore (S1 @ take k S1') n")
   apply(clarsimp)
   apply(simp add: restrict_newprodsX_def)
   apply(case_tac "ESplitItem_prods (S1 ! n) = []")
    apply(clarsimp)
   apply(clarsimp)
   apply(subgoal_tac "(nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0))! m = SSX" for SSX)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0)) = SSX" for SSX)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(subgoal_tac "map (\<lambda>i. if restrict_newprodsXX G i (ESplitItem_prods (S1 ! n)) (ESplitItem_elem (S1 ! n)) (restrict_newto (S1 @ take k S1') n) then teB (ESplitItem_prods (S1 ! n) ! i) else teA (THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (ESplitItem_prods (S1 ! n) ! i))) (nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0)) ! m = SSX" for SSX)
    prefer 2
    apply(rule nth_map)
    apply(force)
   apply(clarsimp)
   apply(case_tac "restrict_newprodsXX G m (ESplitItem_prods (S1 ! n)) (ESplitItem_elem (S1 ! n)) (restrict_newto (S1 @ take k S1') n)")
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply (metis liftB_nth DT_two_elements.inject(2))
  done

lemma nonabstracted_productions_are_unmodified3: "
  PSplitItem_prods (restrict G' G (S1 @ S1') (n+k+Suc 0) ! n) ! m = teB ba
  \<Longrightarrow> n<length S1
  \<Longrightarrow> m < length (ESplitItem_prods (S1!n))
  \<Longrightarrow> ESplitItem_prods (S1 ! n) ! m = ba"
  apply(simp add: restrict_def restrict_map_def restrict_len_def)
  apply(subgoal_tac "length(nat_seq 0 (min (length S1) (Suc (n + k)) + min (length S1') (Suc (n + k) - length S1) - Suc 0)) = SSX" for SSX)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "n<Suc (min (length S1) (Suc (n + k)) + min (length S1') (Suc (n + k) - length S1) - Suc 0)")
   prefer 2
   apply(case_tac "length S1 \<le> Suc(n+k)")
    apply(rule_tac
      t="min (length S1) (Suc(n + k))"
      and s="length S1"
      in ssubst)
     apply(rule Orderings.min_absorb1)
     apply(force)
    apply(case_tac "min (length S1') (Suc (n + k) - length S1)")
     apply(clarsimp)
  apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      t="min (length S1) (Suc(n + k))"
      in ssubst)
  apply(rule Orderings.min_absorb2)
  apply(force)
  apply(force)
  apply(subgoal_tac "nat_seq 0 (min (length S1) (Suc (n + k)) + min (length S1') (Suc (n + k) - length S1) - Suc 0) ! n = SSX" for SSX)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(subgoal_tac "PSplitItem_prods ((\<lambda>i. \<lparr>PSplitItem_elim = ESplitItem_elim ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i)) # restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i)), PSplitItem_ignore = restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_elim_prods = ESplitItem_elim_prods ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i), PSplitItem_prods = restrict_newprods G' G (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_elem = restrict_newelem (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_to = restrict_newto (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i\<rparr>) n) ! m = teB ba")
  prefer 2
  apply(rule_tac
      t="PSplitItem_prods \<lparr>PSplitItem_elim = ESplitItem_elim ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! n), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! n)) # restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n)), PSplitItem_ignore = restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n, PSplitItem_elim_prods = ESplitItem_elim_prods ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! n), PSplitItem_prods = restrict_newprods G' G (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n, PSplitItem_elem = restrict_newelem (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n, PSplitItem_to = restrict_newto (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n\<rparr> ! m"
      and s="PSplitItem_prods(map (\<lambda>i. \<lparr>PSplitItem_elim = ESplitItem_elim ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i), PSplitItem_from = hd (cropTol3l2 (the (ESplitItem_from ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i)) # restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i)), PSplitItem_ignore = restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_elim_prods = ESplitItem_elim_prods ((take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! i), PSplitItem_prods = restrict_newprods G' G (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_elem = restrict_newelem (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i, PSplitItem_to = restrict_newto (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') i\<rparr>) (nat_seq 0 (min (length S1) (Suc (n + k)) + min (length S1') (Suc (n + k) - length S1) - Suc 0)) ! n)!m"
      in ssubst)
  apply(rule_tac
      t="(map SSf SSw)!SSn" for SSf SSw SSn
      in ssubst)
  apply(rule nth_map)
  apply(clarsimp)
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(simp add: restrict_newprods_def)
  apply(subgoal_tac "(take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') ! n = SSX" for SSX)
  prefer 2
  apply(rule nth_append_1)
  apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length(nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0)) = SSX" for SSX)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(case_tac "restrict_newignore (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n = []")
  apply(clarsimp)
  apply(simp add: restrict_newprodsX_def)
  apply(case_tac "ESplitItem_prods (S1 ! n) = []")
  apply(clarsimp)
  apply(clarsimp)
  apply(case_tac "restrict_newprodsXX G (nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0) ! m) (ESplitItem_prods (S1 ! n)) (ESplitItem_elem (S1 ! n)) (restrict_newto (take (Suc (n + k)) S1 @ take (Suc (n + k) - length S1) S1') n)")
  prefer 2
  apply(force)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq 0 (length (ESplitItem_prods (S1 ! n)) - Suc 0) ! m = SSX" for SSX)
  prefer 2
  apply(rule nat_seq_nth_compute)
  apply(force)
  apply(case_tac "length (ESplitItem_prods (S1 ! n))")
  apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  apply(clarsimp)
  apply(clarsimp)
  apply (metis liftB_nth DT_two_elements.inject(2))
  done

hide_fact concat_cfgLM_trans_der_cfgLMMIy
hide_fact e_derivation_can_be_embedded_minimally_hlp2
hide_fact e_derivation_can_be_embedded_minimally_hlp3
hide_fact elim_map_to_trans_der_cfgLMMIy
hide_fact enforceSuffixS_Min_Min
hide_fact equal_split_prefix_hlp5_construct_relevant_cfgLMMIP_not_abstract_productions
hide_fact ESplitItem_ignore_decompose
hide_fact fillOptL_length
hide_fact fillOptL_with_take
hide_fact ignore_parts_in_relation
hide_fact PValidSplit_construct_derivation1
hide_fact restrict_preserves_ValidSplit
hide_fact restrict_PValidSplit_belongs
hide_fact restrict_PValidSplit_belongs_prods_setA
hide_fact restrict_PValidSplit_belongs_prods_setB
hide_fact restrict_PValidSplit_elim
hide_fact restrict_PValidSplit_final
hide_fact restrict_PValidSplit_gen
hide_fact restrict_PValidSplit_initial
hide_fact restrict_PValidSplit_interline
hide_fact restrict_PValidSplit_notEmpty
hide_fact restrict_PValidSplit_to_empty
hide_fact restrict_PValidSplit_ValidItem
hide_fact restrict_toberemoved_at_last
hide_fact restrict_toberemoved_direct_computation
hide_fact restrict_toberemoved_equal
hide_fact restrict_toberemoved_last_is_ignore
hide_fact restrict_toberemoved_preserves_length
hide_fact restrict_toberemoved_restrict_toberemoved_suffix
hide_fact restrict_toberemoved_restrict_toberemoved_suffix_X
hide_fact restrict_toberemoved_restrict_toberemoved_suffix_X2
hide_fact restrict_toberemoved_smaller
hide_fact restrict_toberemoved_smaller_than_ignore
hide_fact restrict_toberemoved_suffix_X
hide_fact restrict_toberemovedX_last
hide_fact restrict_toberemovedX_last2
hide_fact toberemoved_suffix_X
  (* important e_derivation_can_be_embedded_minimally *)
  (* important equal_split_prefix_hlp1_elim_eq_updated *)
  (* important equal_split_prefix_hlp1_triv_eq *)
  (* important equal_split_prefix_hlp2 *)
  (* important equal_split_prefix_hlp3 *)
  (* important equal_split_prefix_hlp5_construct_relevant_cfgLMMIP *)
  (* important ESplitItem_ignore_restrict_toberemoved_suffix *)
  (* important fillOpt_hd_and_last_back_state *)
  (* important ignore_toberemoved_suffix *)
  (* important length_of_restrict *)
  (* important length_restrict_toberemoved *)
  (* important newto_and_old_to_either_unmodified_or_cropTol3l2_of_prefix *)
  (* important nonabstracted_productions_are_unmodified *)
  (* important nonabstracted_productions_are_unmodified2 *)
  (* important nonabstracted_productions_are_unmodified3 *)
  (* important nonemtpy_newignore_implies_newprods_unchanged *)
  (* important nonemtpy_newignore_implies_newto_unchanged *)
  (* important restrict_newignore_last_empty *)
  (* important restrict_newignore_prefix_of_ESplitItem_ignore_butlast *)
  (* important restrict_newignore_shorter_than_ESplitItem_ignore *)
  (* important restrict_newprods_preserves_length *)
  (* important restrict_newprodsXX_implication *)
  (* important restrict_toberemoved_suffix *)
  (* important restrict_toberemovedX_equals_restrict_toberemoved *)
  (* important toberemoved_suffix *)

end
