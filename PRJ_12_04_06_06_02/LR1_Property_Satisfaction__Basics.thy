section {*LR1\_Property\_Satisfaction\_\_Basics*}
theory
  LR1_Property_Satisfaction__Basics

imports
  PRJ_12_04_06_06_02__ENTRY

begin

definition cfgLMTDL :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option) list) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list list \<Rightarrow> ('b list list) \<Rightarrow> bool" where
  "cfgLMTDL G ds w \<pi>s fw = (cfgLM.trans_der_list G ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) w) \<pi>s (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw))"

definition cfgLMMPX :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option)) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> bool" where
  "cfgLMMPX G d w \<pi> \<alpha> c = (
(\<forall>\<pi>'. strict_prefix \<pi>' \<pi> \<longrightarrow> (\<not>(\<exists>d c.
  cfgLM.trans_der G d \<lparr>cfg_conf = w\<rparr> \<pi>' \<lparr>cfg_conf = \<alpha>@c\<rparr>)
  )))"

definition cfgLMMIyX :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option)) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> bool" where
  "cfgLMMIyX G d w \<pi> = ((\<pi>\<noteq>[] \<longrightarrow> (\<not> applicable G \<pi> (butlast w))))"

definition cfgLMMIy :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option)) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> bool" where
  "cfgLMMIy G d w \<pi> c1 c2 = (
  cfgLM.trans_der G d \<lparr>cfg_conf = w\<rparr> \<pi> \<lparr>cfg_conf = c1@c2\<rparr>
  \<and> (cfgLMMIyX G d w \<pi>))"

definition cfgLMMIP :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option)) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> (('a, 'b) DT_two_elements list) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> bool" where
  "cfgLMMIP G d w \<pi> \<alpha> c = (
  cfgLM.trans_der G d \<lparr>cfg_conf = w\<rparr> \<pi> \<lparr>cfg_conf = \<alpha>@c\<rparr>
  \<and> (cfgLMMIyX G d w \<pi> \<and> cfgLMMPX G d w \<pi> \<alpha> c))"

lemma cfgLMMIP_drop_leading_liftB: "
  valid_cfg G
  \<Longrightarrow> cfgLMMIP G d (liftB \<alpha> @ w1) \<pi> (liftB (\<alpha> @ \<beta>)) (liftA v)
  \<Longrightarrow> \<exists>aa. cfgLMMIP G aa w1 \<pi> (liftB \<beta>) (liftA v)"
  apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha> @ w1\<rparr> \<in> cfg_configurations G")
    prefer 2
    apply(unfold cfgLM.trans_der_def cfgLMMIP_def)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac e)(*strict*)
    apply(erule conjE)+
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
     apply(rename_tac e)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(simp add: cfg_configurations_def setBConcat setA_liftB setB_liftB)
  apply(fold cfgLM.trans_der_def cfgLMMIP_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<alpha>="\<alpha>"
      in cfgLM_trans_der_drop_leading_terminals)
    apply(force)
   apply(simp add: cfgLMMIP_def)
   apply(simp add: liftB_commutes_over_concat)
   apply(force)
  apply(rule_tac
      x="derivation_map (derivation_take d (length \<pi>)) (\<lambda>c. \<lparr>cfg_conf = drop (length \<alpha>) (cfg_conf c)\<rparr>)"
      in exI)
  apply(simp add: cfgLMMIP_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cfgLMMIyX_def)
   apply(clarsimp)
   apply(subgoal_tac "w1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(erule disjE)
    apply(clarsimp)
    apply(subgoal_tac "\<pi>=[]")
     apply(force)
    apply(rule applicable_with_empty_source)
    apply(force)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(subgoal_tac "butlast (liftB \<alpha> @ w' @ [a']) = liftB \<alpha> @ w'")
    apply(rename_tac w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "applicable G \<pi> (liftB \<alpha>@w')")
    apply(rename_tac w' a')(*strict*)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(rule applicable_append_liftB)
     apply(rename_tac w' a')(*strict*)
     apply(force)
    apply(rename_tac w' a')(*strict*)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(simp add: cfg_configurations_def setBConcat setB_liftB)
  apply(simp add: cfgLMMPX_def)
  apply(clarsimp)
  apply(rename_tac \<pi>' da c)(*strict*)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>' da c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="\<alpha>"
      and ?w2.0="[]"
      and ?d1.0="da"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac \<pi>' da c)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da c)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da c)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' da c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' da c daa)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

definition cfgLMMP :: "('a,'b) cfg \<Rightarrow> ((nat \<Rightarrow> (('a, 'b) cfg_step_label,('a, 'b) cfg_configuration) derivation_configuration option)) \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> bool" where
  "cfgLMMP G d w \<pi> \<alpha> c = (
  cfgLM.trans_der G d \<lparr>cfg_conf = w\<rparr> \<pi> \<lparr>cfg_conf = \<alpha>@c\<rparr>
  \<and> (cfgLMMPX G d w \<pi> \<alpha> c))"


lemma take_butlast_liftA: "
  take (length (liftA w) - Suc 0) (butlast (liftA w)) = liftA (butlast w)"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(clarsimp)
  apply (simp add: List.butlast_append liftA_commutes_over_concat liftA_preserves_length)
  done

lemma crop_cfgLMMP_to_cfgLMMIP: "
  valid_cfg G
  \<Longrightarrow> cfgLMMP G d (liftB \<beta>@liftA w) \<pi> (liftB \<alpha>) (liftA c)
  \<Longrightarrow> \<pi> \<noteq> []
  \<Longrightarrow> \<exists>w' c' d. prefix w' w \<and> prefix c' c \<and> cfgLMMIP G d (liftB \<beta>@liftA w') \<pi> (liftB \<alpha>) (liftA c')"
  apply(case_tac "applicable G \<pi> (liftB \<beta>@liftA (butlast w))")
   prefer 2
   apply(clarsimp)
   apply(rule_tac
      x="w"
      in exI)
   apply(simp add: prefix_def)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLMMPX_def cfgLMMP_def cfgLMMIP_def cfgLMMIyX_def)
   apply(rule conjI)
    apply(rule_tac
      x="d"
      in exI)
    apply(force)
   apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    prefer 2
    apply(rule case_list)
   apply(erule disjE)
    apply(clarsimp)
    apply(thin_tac "\<not> applicable G \<pi> (liftB \<beta>)")
    apply(thin_tac "\<forall>\<pi>'. strict_prefix \<pi>' \<pi> \<longrightarrow> (\<forall>d c. \<not> cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<beta>\<rparr> \<pi>' \<lparr>cfg_conf = liftB \<alpha> @ c\<rparr>)")
    apply (metis applicable_liftB applicable_def)
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply (metis liftA_append_tail butlast_snoc_2)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      P="\<lambda>n. applicable G \<pi> (liftB \<beta>@take n (butlast (liftA w)))"
      and n="length (butlast (liftA w))"
      in ex_least_nat_le_prime)
    apply(rule_tac
      t="(liftB \<beta> @ take (length (butlast (liftA w))) (butlast (liftA w)))"
      and s="(liftB \<beta> @ liftA (butlast w))"
      in ssubst)
     apply(clarsimp)
     apply (rule take_butlast_liftA)
    apply(force)
   apply(erule exE)+
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      P="\<lambda>w1 w2. prefix w1 w2"
      and ERROR="\<lambda>w n. \<not> (applicable G \<pi> (liftB \<beta> @ butn (liftA w) (Suc n))) \<and> applicable G \<pi> (liftB \<beta> @ butn (liftA w) n) \<and> \<lparr>cfg_conf=liftA w\<rparr>\<in> cfg_configurations G"
      and x="w"
      and n="length (liftA w) - k"
      in error_free_compatible_solution_exists2)
       apply(rename_tac k)(*strict*)
       apply(rule_tac
      t="butn (liftA w) (length (liftA w) - k)"
      in ssubst)
        apply(rename_tac k)(*strict*)
        apply(rule butn_take_butlast)
        apply(force)
       apply(rename_tac k)(*strict*)
       apply(rule conjI)
        apply(rename_tac k)(*strict*)
        prefer 2
        apply(rule conjI)
         apply(rename_tac k)(*strict*)
         apply(force)
        apply(rename_tac k)(*strict*)
        apply(clarsimp)
        apply(simp add: cfgLMMP_def cfgLM.trans_der_def)
        apply(subgoal_tac "\<lparr>cfg_conf=(liftB \<beta> @ liftA w)\<rparr> \<in> cfg_configurations G")
         apply(rename_tac k)(*strict*)
         apply(simp add: cfg_configurations_def)
         apply(simp add: setAConcat)
         apply(simp add: setBConcat)
        apply(rename_tac k)(*strict*)
        apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
         apply(rename_tac k)(*strict*)
         apply(force)
        apply(rename_tac k)(*strict*)
        apply(force)
       apply(rename_tac k)(*strict*)
       apply(case_tac k)
        apply(rename_tac k)(*strict*)
        apply(clarsimp)
        apply (metis applicable_liftB applicable_def)
       apply(rename_tac k nat)(*strict*)
       apply(clarsimp)
       apply(rename_tac nat)(*strict*)
       apply(erule_tac
      x="nat"
      in allE)
       apply(clarsimp)
       apply(subgoal_tac "applicable G \<pi> (liftB \<beta> @ take nat (butlast (liftA w)))")
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(rule_tac
      t="liftB \<beta> @ take nat (butlast (liftA w))"
      and s="liftB \<beta> @ butn (liftA w) (Suc (length (liftA w) - Suc nat))"
      in ssubst)
        apply(rename_tac nat)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "X" for X)
        apply(rename_tac nat)(*strict*)
        prefer 2
        apply(rule_tac
      k="nat"
      and w="liftA w"
      in butn_take_butlast)
        apply (simp add: One_nat_def liftA_preserves_length Suc_leD length_butlast)
       apply(rename_tac nat)(*strict*)
       apply(rule_tac
      t="take nat (butlast (liftA w))"
      and s="butn (liftA w) (length (liftA w) - nat)"
      in subst)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(rule_tac
      t="length (liftA w) - nat"
      and s="Suc (length (liftA w) - Suc nat)"
      in ssubst)
        apply(rename_tac nat)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(subgoal_tac "length (liftA w) - nat = Suc (length (liftA w) - Suc nat)")
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac k x)(*strict*)
      apply(simp add: prefix_def)
     apply(rename_tac k a b ca)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac k x n)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="butlast x"
      in exI)
    apply(rule conjI)
     apply(rename_tac k x n)(*strict*)
     apply(simp add: prefix_def)
     apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac k x n)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac k x n)(*strict*)
     apply(erule disjE)
      apply(rename_tac k x n)(*strict*)
      apply(clarsimp)
     apply(rename_tac k x n)(*strict*)
     apply(clarsimp)
    apply(rename_tac k x n)(*strict*)
    apply(case_tac n)
     apply(rename_tac k x n)(*strict*)
     apply(clarsimp)
    apply(rename_tac k x n nat)(*strict*)
    apply(rule_tac
      x="nat "
      in exI)
    apply(clarsimp)
    apply(rename_tac k x nat)(*strict*)
    apply(rule_tac
      t="butn (liftA(butlast x)) nat"
      and s="butn (liftA x) (Suc nat)"
      in ssubst)
     apply(rename_tac k x nat)(*strict*)
     apply (metis liftA_preserves_length butn_butlast butn_def take_liftA)
    apply(rename_tac k x nat)(*strict*)
    apply(clarsimp)
    apply(case_tac k)
     apply(rename_tac k x nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac x nat)(*strict*)
     apply (metis applicable_liftB applicable_def)
    apply(rename_tac k x nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac x nat nata)(*strict*)
    apply(subgoal_tac "butn (butlast (liftA x)) (Suc nat) = butn (liftA x) (Suc (Suc nat))")
     apply(rename_tac x nat nata)(*strict*)
     apply(rule conjI)
      apply(rename_tac x nat nata)(*strict*)
      apply(rule_tac
      t="liftB \<beta> @ butn (liftA (butlast x)) (Suc nat)"
      and s="liftB \<beta> @ butn (liftA x) (Suc (Suc nat))"
      in ssubst)
       apply(rename_tac x nat nata)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x nat nata)(*strict*)
      apply(clarsimp)
      apply (simp add: liftA_preserves_length butn_butlast butn_def take_liftA)
      apply (smt diff_Suc_less length_greater_0_conv take_Nil take_butlast)
     apply(rename_tac x nat nata)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(rule conjI)
      apply(rename_tac x nat nata)(*strict*)
      apply(simp add: setA_liftA)
      apply(rule subset_trans)
       apply(rule trivButLast)
      apply(force)
     apply(rename_tac x nat nata)(*strict*)
     apply(simp add: setB_liftA)
    apply(rename_tac x nat nata)(*strict*)
    apply(rule butn_butlast)
   apply(rename_tac k x y n)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac k y n ca)(*strict*)
   apply(case_tac k)
    apply(rename_tac k y n ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac y n ca)(*strict*)
    apply (metis applicable_liftB applicable_def)
   apply(rename_tac k y n ca nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac y n ca nat)(*strict*)
   apply(case_tac "ca=[]")
    apply(rename_tac y n ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac y n nat)(*strict*)
    apply(case_tac "n=0")
     apply(rename_tac y n nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac y n nat)(*strict*)
    apply(clarsimp)
    apply(case_tac n)
     apply(rename_tac y n nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac y n nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac y nat nata)(*strict*)
    apply(rule_tac
      G="G"
      and ?\<pi>1.0="\<pi>"
      and ?\<pi>2.0="[]"
      and ?w1.0="liftB \<beta> @ butn (liftA y) (Suc nata)"
      and \<alpha>="[]"
      and ?w2.0="drop (length(butn (liftA y) (Suc nata))) (butn (liftA y) (Suc 0))"
      in applicable_contra)
       apply(rename_tac y nat nata)(*strict*)
       apply(force)
      apply(rename_tac y nat nata)(*strict*)
      apply(rule_tac
      t="((liftB \<beta> @ butn (liftA y) (Suc nata)) @ drop (length (butn (liftA y) (Suc nata))) (butn (liftA y) (Suc 0)))"
      and s="liftB \<beta> @ (butn (liftA y) (Suc 0))"
      in ssubst)
       apply(rename_tac y nat nata)(*strict*)
       apply(simp add: butn_def)
       apply(rule_tac
      t="min (length (liftA y)) (length (liftA y) - Suc nata)"
      and s="length (liftA y) - Suc nata"
      in ssubst)
        apply(rename_tac y nat nata)(*strict*)
        apply (simp add: List.length_take liftA_preserves_length diff_le_self take_length)
       apply(rename_tac y nat nata)(*strict*)
       apply(subgoal_tac "y=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
        apply(rename_tac y nat nata)(*strict*)
        prefer 2
        apply(rule case_list)
       apply(rename_tac y nat nata)(*strict*)
       apply(erule disjE)
        apply(rename_tac y nat nata)(*strict*)
        apply(clarsimp)
       apply(rename_tac y nat nata)(*strict*)
       apply(clarsimp)
       apply(rename_tac nat nata w' a')(*strict*)
       apply (simp only: liftA_commutes_over_concat)
       apply(clarsimp)
       apply(rule append_take_drop_id)
      apply(blast)
     apply(rename_tac y nat nata)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(rule conjI)
      apply(rename_tac y nat nata)(*strict*)
      apply(rule_tac
      B="setA (liftA y)"
      in subset_trans)
       apply(rename_tac y nat nata)(*strict*)
       apply(rule_tac
      B="setA (butn (liftA y) (Suc 0))"
      in subset_trans)
        apply(rename_tac y nat nata)(*strict*)
        apply(rule setADropIndexSubset2)
       apply(rename_tac y nat nata)(*strict*)
       apply (smt butn_def setATake setA_liftA_set)
      apply(rename_tac y nat nata)(*strict*)
      apply(force)
     apply(rename_tac y nat nata)(*strict*)
     apply(rule_tac
      B="setB (liftA y)"
      in subset_trans)
      apply(rename_tac y nat nata)(*strict*)
      apply(rule_tac
      B="setB (butn (liftA y) (Suc 0))"
      in subset_trans)
       apply(rename_tac y nat nata)(*strict*)
       apply(rule setBDropIndexSubset2)
      apply(rename_tac y nat nata)(*strict*)
      apply (metis liftA_preserves_length setBTakeIndexSubset2 butn_def)
     apply(rename_tac y nat nata)(*strict*)
     apply(force)
    apply(rename_tac y nat nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac y n ca nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ca=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac y n ca nat)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac y n ca nat)(*strict*)
   apply(erule disjE)
    apply(rename_tac y n ca nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac y n ca nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac y n nat w' a')(*strict*)
   apply(subgoal_tac "butn (liftA (y @ w' @ [a'])) 0 = liftA (y @ w' @ [a'])")
    apply(rename_tac y n nat w' a')(*strict*)
    prefer 2
    apply(simp add: butn_def)
   apply(rename_tac y n nat w' a')(*strict*)
   apply(subgoal_tac "butn (liftA (y @ w' @ [a'])) (Suc 0) = liftA (y @ w')")
    apply(rename_tac y n nat w' a')(*strict*)
    prefer 2
    apply(rule_tac t="liftA (y @ w' @ [a'])" and s="liftA (y @ w') @ liftA [a']" in ssubst)
     apply (simp add: liftA_commutes_over_concat)
    apply (smt butn_prefix_closureise length_Cons liftA_preserves_length list.size(3))
   apply(rename_tac y n nat w' a')(*strict*)
   apply(subgoal_tac "\<not> applicable G \<pi> (liftB \<beta> @ (liftA (y @ w')))")
    apply(rename_tac y n nat w' a')(*strict*)
    prefer 2
    apply(rule_tac
      t="liftB \<beta> @ (liftA (y @ w'))"
      and s="liftB \<beta> @ butn (liftA (y @ w' @ [a'])) (Suc 0)"
      in subst)
     apply(rename_tac y n nat w' a')(*strict*)
     apply(force)
    apply(rename_tac y n nat w' a')(*strict*)
    apply(force)
   apply(rename_tac y n nat w' a')(*strict*)
   apply(thin_tac "\<not> applicable G \<pi> (liftB \<beta> @ butn (liftA (y @ w' @ [a'])) (Suc 0))")
   apply(thin_tac "butn (liftA (y @ w' @ [a'])) (Suc 0) = liftA (y @ w')")
   apply(subgoal_tac "applicable G \<pi> (liftB \<beta> @ (liftA (y @ w' @ [a'])))")
    apply(rename_tac y n nat w' a')(*strict*)
    prefer 2
    apply(rule_tac
      t="liftB \<beta> @ liftA (y @ w' @ [a'])"
      and s="liftB \<beta> @ butn (liftA (y @ w' @ [a'])) 0"
      in subst)
     apply(rename_tac y n nat w' a')(*strict*)
     apply(force)
    apply(rename_tac y n nat w' a')(*strict*)
    apply(force)
   apply(rename_tac y n nat w' a')(*strict*)
   apply(thin_tac "applicable G \<pi> (liftB \<beta> @ butn (liftA (y @ w' @ [a'])) 0)")
   apply(thin_tac "butn (liftA (y @ w' @ [a'])) 0 = liftA (y @ w' @ [a'])")
   apply(thin_tac "applicable G \<pi> (liftB \<beta> @ liftA (butlast w))")
   apply(thin_tac "\<forall>i<Suc nat. \<not> applicable G \<pi> (liftB \<beta> @ take i (butlast (liftA w)))")
   apply(thin_tac "applicable G \<pi> (liftB \<beta> @ take (Suc nat) (butlast (liftA w)))")
   apply(rule_tac
      G="G"
      and ?\<pi>1.0="\<pi>"
      and ?\<pi>2.0="[]"
      and ?w1.0="liftB \<beta>@butn (liftA y) n"
      and \<alpha>="[]"
      and ?w2.0="liftA (takeB n y @ w')"
      in applicable_contra)
      apply(rename_tac y n nat w' a')(*strict*)
      apply(force)
     apply(rename_tac y n nat w' a')(*strict*)
     apply(rule_tac
      t="((liftB \<beta> @ butn (liftA y) n) @ liftA (takeB n y @ w'))"
      and s="liftB \<beta> @ liftA (y @ w')"
      in ssubst)
      apply(rename_tac y n nat w' a')(*strict*)
      apply(simp add: butn_def takeB_def)
      apply (simp only: liftA_commutes_over_concat)
      apply (metis liftA_commutes_over_concat liftA_preserves_length append_take_drop_id concat_asso length_drop take_liftA)
     apply(rename_tac y n nat w' a')(*strict*)
     apply(force)
    apply(rename_tac y n nat w' a')(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp add: setB_liftA)
    apply(simp add: setA_liftA)
    apply(simp add: takeB_def)
    apply (metis butn_length set_drop_subset subset_trans)
   apply(rename_tac y n nat w' a')(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x' n')(*strict*)
  apply(thin_tac "\<forall>x'' n''. x'' \<sqsubseteq> x' \<and> \<not> applicable G \<pi> (liftB \<beta> @ butn (liftA x'') (Suc n'')) \<and> applicable G \<pi> (liftB \<beta> @ butn (liftA x'') n'') \<and> \<lparr>cfg_conf = liftA x''\<rparr> \<in> cfg_configurations G \<longrightarrow> x'' = x' \<and> n' = n''")
  apply(rename_tac x' n')(*strict*)
  apply(rule_tac
      x="butn x' n'"
      in exI)
  apply(rule conjI)
   apply(rename_tac x' n')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x' n' ca)(*strict*)
   apply(rule_tac
      x="takeB n' x'@ca"
      in exI)
   apply(simp (no_asm) only: butn_def takeB_def)
   apply (metis append_assoc append_take_drop_id butn_def takeB_def)
  apply(rename_tac x' n')(*strict*)
  apply(thin_tac "applicable G \<pi> (liftB \<beta> @ liftA (butlast w))")
  apply(subgoal_tac "\<exists>d c. cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<beta> @ butn (liftA x') n'\<rparr> \<pi> c")
   apply(rename_tac x' n')(*strict*)
   prefer 2
   apply(simp add: applicable_def)
  apply(rename_tac x' n')(*strict*)
  apply(clarsimp)
  apply(rename_tac x' n' da ca)(*strict*)
  apply(simp add: cfgLMMP_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x' n' da ca caa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
  apply(clarify)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="\<pi>"
      and G="G"
      and ?w1.0="liftB \<beta>@butn (liftA x') n'"
      and ?w2.0="takeB n' (liftA x') @ liftA caa"
      and ?d1.0="d"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
   apply(rule_tac
      t="(liftB \<beta> @ butn (liftA x') n') @ takeB n' (liftA x') @ liftA caa"
      and s="liftB \<beta> @ liftA (x' @ caa)"
      in ssubst)
    apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
    apply(simp (no_asm) only: butn_def takeB_def)
    apply(clarsimp)
    apply(rename_tac x' n' da ca cfg_conf)(*strict*)
    apply (simp only: liftA_commutes_over_concat)
    apply(force)
   apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac x' n' da ca caa cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x' n' da ca caa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x' n' da ca w)(*strict*)
  apply(subgoal_tac "strict_prefix w (liftB \<alpha>) \<or> SSX" for SSX)
   apply(rename_tac x' n' da ca w)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac x' n' da ca w)(*strict*)
  apply(erule disjE)
   apply(rename_tac x' n' da ca w)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac x' n' da ca w cb)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x' n' da ca w cb)(*strict*)
    prefer 2
    apply(rule liftB_append)
    apply(force)
   apply(rename_tac x' n' da ca w cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
   apply (simp only: liftB_commutes_over_concat)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac x' n' da ca l1 l2)(*strict*)
    apply(force)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(case_tac l2)
    apply(rename_tac x' n' da ca l1 l2)(*strict*)
    apply(clarsimp)
   apply(rename_tac x' n' da ca l1 l2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x' n' da ca l1 a list)(*strict*)
   apply(simp add: takeB_def)
   apply(case_tac "drop (length (liftA x') - n') (liftA x')")
    apply(rename_tac x' n' da ca l1 a list)(*strict*)
    apply(subgoal_tac "liftA ca = teB a # liftB list @ liftA c")
     apply(rename_tac x' n' da ca l1 a list)(*strict*)
     apply(case_tac ca)
      apply(rename_tac x' n' da ca l1 a list)(*strict*)
      apply(force)
     apply(rename_tac x' n' da ca l1 a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac x' n' da ca l1 a list)(*strict*)
    apply(rule_tac
      t="liftA ca"
      and s="drop (length (liftA x') - n') (liftA x')@liftA ca"
      in ssubst)
     apply(rename_tac x' n' da ca l1 a list)(*strict*)
     apply(force)
    apply(rename_tac x' n' da ca l1 a list)(*strict*)
    apply(force)
   apply(rename_tac x' n' da ca l1 a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac x' n' da ca l1 a list lista)(*strict*)
   apply (metis maxTermPrefix_pull_out liftA_distributes_over_drop liftA_preserves_length list.simps(3) maxTermPrefix_drop_liftA maxTermPrefix_term_string maxTermPrefix_vs_maximalPrefixB maximalPrefixB_liftA)
  apply(rename_tac x' n' da ca w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x' n' da ca cb)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x' n' da ca cb)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(force)
  apply(rename_tac x' n' da ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x' n' da ca l1 l2)(*strict*)
  apply(thin_tac "liftA l1 @ liftA l2 = liftA (l1 @ l2)")
  apply(rule_tac
      x="l1"
      in exI)
  apply(rule conjI)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(rule_tac
      x="l2"
      in exI)
   apply(force)
  apply(rename_tac x' n' da ca l1 l2)(*strict*)
  apply(simp (no_asm) add: cfgLMMIP_def)
  apply(rule_tac
      x="da"
      in exI)
  apply(rule conjI)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(rule_tac
      t="liftA (butn x' n')"
      and s="butn (liftA x') n'"
      in ssubst)
    apply(rename_tac x' n' da ca l1 l2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(rule liftA_butn)
  apply(rename_tac x' n' da ca l1 l2)(*strict*)
  apply(rule conjI)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(simp (no_asm) add: cfgLMMIyX_def)
   apply(rule impI)
   apply(rule_tac
      t="butlast (liftB \<beta> @ liftA (butn x' n'))"
      and s="liftB \<beta> @ butn (liftA x') (Suc n')"
      in ssubst)
    apply(rename_tac x' n' da ca l1 l2)(*strict*)
    apply(clarsimp)
    apply (metis List.butlast_append liftA.simps(1) liftA_butn liftA_vs_filterA filterA.simps(1) append_Nil2 butlast.simps(1) butn_butlast butn_butlast2 butn_zero)
   apply(rename_tac x' n' da ca l1 l2)(*strict*)
   apply(force)
  apply(rename_tac x' n' da ca l1 l2)(*strict*)
  apply(simp add: cfgLMMPX_def)
  apply(clarsimp)
  apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="takeB n' (liftA x') @ liftA ca"
      and ?d1.0="daa"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
     apply(force)
    apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
    apply(thin_tac "takeB n' (liftA x') @ liftA ca = liftA l2")
    apply(subgoal_tac "\<lparr>cfg_conf = liftB \<beta> @ liftA (x' @ ca)\<rparr> \<in> cfg_configurations G")
     apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp (no_asm_use) add: cfgLM.trans_der_def)
     apply(simp add: setB_liftA)
     apply(simp add: setA_liftA)
     apply(simp add: setAConcat)
     apply(simp add: setBConcat)
     apply(simp add: setB_liftA)
     apply(simp add: setA_liftA)
     apply(simp add: takeB_def)
     apply(rule conjI)
      apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
      apply (metis setA_liftA liftA_distributes_over_drop liftA_preserves_length set_drop_subset subset_trans)
     apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
     apply(rule_tac
      t="setB (drop (length (liftA x') - n') (liftA x'))"
      and s="{}"
      in ssubst)
      apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
     apply (metis List.set_simps(1) liftA_distributes_over_drop liftA_preserves_length setB_liftA)
    apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
     apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
    apply(force)
   apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
   apply(force)
  apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c db)(*strict*)
  apply(erule_tac
      x="db"
      in allE)
  apply(erule_tac
      x="c@liftA l2"
      in allE)
  apply(subgoal_tac "liftB \<beta> @ liftA (x' @ ca)=liftB \<beta> @ liftA (butn x' n') @ liftA l2")
   apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c db)(*strict*)
   apply(force)
  apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c db)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="liftA l2"
      and s="takeB n' (liftA x') @ liftA ca"
      in ssubst)
   apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c db)(*strict*)
   apply(force)
  apply(rename_tac x' n' da ca l1 l2 \<pi>' daa c db)(*strict*)
  apply(thin_tac "takeB n' (liftA x') @ liftA ca = liftA l2")
  apply (simp only: liftA_commutes_over_concat)
  apply(clarsimp)
  apply(simp (no_asm) only: butn_def takeB_def)
  apply (metis liftA_commutes_over_concat liftA_distributes_over_drop liftA_preserves_length append_take_drop_id)
  done

definition left_degen :: "
  ('a, 'b) cfg
  \<Rightarrow> (nat
  \<Rightarrow> (('a, 'b) cfg_step_label, ('a, 'b) cfg_configuration) derivation_configuration option)
  \<Rightarrow> bool"
  where
    "left_degen G d \<equiv>
   (sat_refined G d (\<lambda>c1 e c2. (\<exists>w. cfg_conf c1 = [teA (prod_lhs e)] @ w)
  \<and> (\<exists>A w. prod_rhs e = [teA A] @ w) ))"

lemma left_degen_context_persists_prime: "
  valid_cfg G
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e0 \<lparr>cfg_conf = teA A # w1\<rparr>)
  \<Longrightarrow> d (n+m) = Some (pair e c)
  \<Longrightarrow> \<exists>B w2. c=\<lparr>cfg_conf = teA B # w2\<rparr> \<and> suffix w2 w1"
  apply(induct m arbitrary: d A w1 \<pi> B w2 e c)
   apply(rename_tac d A w1 e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A w1)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac m d A w1 e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac m d A w1 e c)(*strict*)
  apply(erule_tac
      x="d"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="w1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+m) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac m d A w1 e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(n+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac m d A w1 e c)(*strict*)
     apply(force)
    apply(rename_tac m d A w1 e c)(*strict*)
    apply(force)
   apply(rename_tac m d A w1 e c)(*strict*)
   apply(force)
  apply(rename_tac m d A w1 e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac m d A w1 c e1 e2 c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m d A w1 c e1 e2 c1 l r)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac m d A w1 c e1 e2 l r B w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac m d A w1 c e1 e2 l r B w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m d A w1 e1 e2 l r B w2)(*strict*)
  apply(case_tac e2)
  apply(rename_tac m d A w1 e1 e2 l r B w2 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A v)
  apply(rename_tac m d Aa w1 e1 e2 l r B w2 A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac m d Aa w1 e1 l r B w2 A v)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac m d Aa w1 e1 l r B w2 A v)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac m d Aa w1 e1 l r B w2 A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac m d Aa w1 e1 r B w2 A v l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac l')
   apply(rename_tac m d Aa w1 e1 r B w2 A v l')(*strict*)
   prefer 2
   apply(rename_tac m d Aa w1 e1 r B w2 A v l' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac m d Aa w1 e1 r B w2 A v l')(*strict*)
  apply(clarsimp)
  apply(rename_tac m d Aa w1 e1 r A v)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac m d Aa w1 e1 A v c)(*strict*)
  apply(simp add: left_degen_def)
  apply(simp add: sat_refined_def)
  apply(erule_tac
      x="n+m"
      in allE)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_slice_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> c'
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> j\<le>length \<pi>
  \<Longrightarrow> \<exists>d'. cfgLM.trans_der G d' ci (take (j-i) (drop i \<pi>)) cj \<and> (left_degen G d \<longrightarrow> left_degen G d')"
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d i) ci (drop i \<pi>) c'")
   prefer 2
   apply(rule cfgLM.trans_der_skip)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "cfgLM.trans_der SSG (derivation_take SSd SSn) ci (take (j-i) (drop i \<pi>)) cj" for SSG SSd SSn)
   prefer 2
   apply(rule cfgLM.trans_der_crop_via_take)
       prefer 5
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: derivation_drop_def get_configuration_def)
   apply(force)
  apply(rule_tac
      x="(derivation_take (derivation_drop d i) (j - i))"
      in exI)
  apply(rule conjI)
   apply(force)
  apply(clarsimp)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac ia)(*strict*)
  apply(case_tac "derivation_take (derivation_drop d i) (j - i) (Suc ia)")
   apply(rename_tac ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_take (derivation_drop d i) (j - i)) ia = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac ia a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc ia"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac ia a)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac ia a)(*strict*)
    apply(force)
   apply(rename_tac ia a)(*strict*)
   apply(force)
  apply(rename_tac ia a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ia e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac ia e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia e1 e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac ia e1 e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia e1 e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac ia e1 e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac ia e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia e1 e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac ia e1 e2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia e1 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac ia e1 r l' A w)(*strict*)
  apply(subgoal_tac "Suc ia\<le>j-i")
   apply(rename_tac ia e1 r l' A w)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def derivation_drop_def)
   apply(case_tac "Suc ia \<le> j - i")
    apply(rename_tac ia e1 r l' A w)(*strict*)
    apply(clarsimp)
   apply(rename_tac ia e1 r l' A w)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia e1 r l' A w)(*strict*)
  apply(erule_tac
      x="i+ia"
      in allE)
  apply(subgoal_tac "d (Suc (i + ia)) = derivation_take (derivation_drop d i) (j - i) (Suc ia)")
   apply(rename_tac ia e1 r l' A w)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def derivation_drop_def)
   apply(rule_tac
      t="i+ia"
      and s="ia+i"
      in ssubst)
    apply(rename_tac ia e1 r l' A w)(*strict*)
    apply(force)
   apply(rename_tac ia e1 r l' A w)(*strict*)
   apply(force)
  apply(rename_tac ia e1 r l' A w)(*strict*)
  apply(subgoal_tac "get_configuration (d ((i + ia))) = get_configuration (derivation_take (derivation_drop d i) (j - i) ia)")
   apply(rename_tac ia e1 r l' A w)(*strict*)
   prefer 2
   apply(thin_tac "derivation_take (derivation_drop d i) (j - i) ia = Some (pair e1 \<lparr>cfg_conf = liftB l' @ teA A # r\<rparr>)")
   apply(rename_tac ia e1 r l' A w)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def)
   apply(rename_tac ia r l' A w)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rule_tac
      t="i+ia"
      and s="ia+i"
      in ssubst)
    apply(rename_tac ia r l' A w)(*strict*)
    apply(force)
   apply(rename_tac ia r l' A w)(*strict*)
   apply(force)
  apply(rename_tac ia e1 r l' A w)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "d(i+ia)")
   apply(rename_tac ia e1 r l' A w)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia e1 r l' A w a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac ia e1 r l' A w a option b)(*strict*)
  apply(clarsimp)
  done

lemma left_degen_drop_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=teA A#C\<rparr> \<pi> \<lparr>cfg_conf=teA B#w@C\<rparr>
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> \<pi> \<lparr>cfg_conf=teA B#w\<rparr> \<and> left_degen G d"
  apply(subgoal_tac "\<lparr>cfg_conf=teA B#w@C\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(induct "\<pi>" arbitrary: B w C rule: rev_induct)
   apply(rename_tac B w C)(*strict*)
   apply(subgoal_tac "A=B \<and> w=[]")
    apply(rename_tac B w C)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
   apply(rename_tac B w C)(*strict*)
   apply(clarsimp)
   apply(rename_tac C)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA A]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac C)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac C)(*strict*)
     apply(force)
    apply(rename_tac C)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac C)(*strict*)
   apply(simp add: left_degen_def sat_refined_def)
   apply(clarsimp)
   apply(rename_tac C i)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac x xs B w C)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs B w C)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc (length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs B w C)(*strict*)
     apply(force)
    apply(rename_tac x xs B w C)(*strict*)
    apply(force)
   apply(rename_tac x xs B w C)(*strict*)
   apply(force)
  apply(rename_tac x xs B w C)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B w C e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs B w C e1 e2 c1 c2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs B w C e1 e2 c1 c2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs B w C e1 e2 c1 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B w C e1 e2 c1 c2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac x xs B w C e1 e2 c1 c2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B w C e1 c1 c2 r l' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac D w)
  apply(rename_tac x xs B wa C e1 c1 c2 r l' D w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs B wa C e1 c1 c2 r l' D w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 c2 r l' D w)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs B wa C e1 c2 r l' D w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
  apply(subgoal_tac "\<exists>B w2. \<lparr>cfg_conf = liftB l' @ teA D # r\<rparr>=\<lparr>cfg_conf = teA B # w2\<rparr> \<and> suffix w2 C")
   apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in left_degen_context_persists_prime)
       apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
       apply(force)
      apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
      apply(force)
     apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
     apply(simp only: cfgLM.trans_der_def)
     apply(force)
    apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
    apply(simp only: cfgLM.trans_der_def)
    apply(force)
   apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
   apply(simp only: cfgLM.trans_der_def)
   apply(force)
  apply(rename_tac x xs B wa C e1 r l' D w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w Ba w2)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
  apply(subgoal_tac "\<exists>B w2. \<lparr>cfg_conf = liftB l' @ w @ r\<rparr>=\<lparr>cfg_conf = teA B # w2\<rparr> \<and> suffix w2 (c@C)")
   apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="length xs"
      and m="Suc 0"
      in left_degen_context_persists_prime)
       apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
       apply(force)
      apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
      apply(force)
     apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
     apply(simp only: cfgLM.trans_der_def)
     apply(force)
    apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
    apply(force)
   apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
   apply(force)
  apply(rename_tac x xs B wa C e1 r l' D w Ba c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w Ba c Bb w2)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w Ba c Bb ca)(*strict*)
  apply(case_tac l')
   apply(rename_tac x xs B wa C e1 r l' D w Ba c Bb ca)(*strict*)
   prefer 2
   apply(rename_tac x xs B wa C e1 r l' D w Ba c Bb ca a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs B wa C e1 r l' D w Ba c Bb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
  apply(erule_tac
      x="Ba"
      in meta_allE)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(erule_tac
      x="C"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
   apply(simp only: cfgLM.trans_der_def)
   apply(rule_tac
      x="e1"
      in exI)
   apply(clarsimp)
   apply(rename_tac x xs B C e1 Ba c ca)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs B C e1 Ba c ca)(*strict*)
    apply(force)
   apply(rename_tac x xs B C e1 Ba c ca)(*strict*)
   apply(force)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
    apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
    apply(simp only: cfgLM.trans_der_def)
    apply(force)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
   apply(simp only: cfgLM.trans_der_def)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(subgoal_tac "x=\<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr>")
   apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
   apply(subgoal_tac "get_labels d (Suc(length xs)) = get_labels d (length xs) @ [Some SSe]" for SSe)
    apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
    prefer 2
    apply(rule cfgLM.get_labels_drop_last)
       apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
       apply(force)
      apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
      apply(force)
     apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
     apply(force)
    apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
    apply(force)
   apply(rename_tac x xs B C e1 Ba c ca da e)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (der2 SSc SSe SSc') SSc [SSe] SSc'" for SSG SSc SSe SSc')
   apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
   prefer 2
   apply(rule_tac
      e="\<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr>"
      and c="\<lparr>cfg_conf = teA Ba # c\<rparr>"
      and c'="\<lparr>cfg_conf = teA Bb # ca @ c\<rparr>"
      in cfgLM.trans_der_der2)
     apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
     apply(force)
    apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = teA Ba # c @ C\<rparr> \<in> cfg_configurations G")
     apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
    apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
     apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
     apply(simp only: cfgLM.trans_der_def)
     apply(force)
    apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
    apply(simp only: cfgLM.trans_der_def)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (derivation_append SSd1 (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = liftB SSv1 @ cfg_conf v @ SSv4\<rparr>)) (length SSrenPI10)) \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB [] @ SSv3 @ []\<rparr>" for SSG SSd1 SSd2 SSv1 SSv4 SSw1 SSrenPI10 SSrenPI20 SSv3)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="da"
      and ?d2.0="(der2 \<lparr>cfg_conf = teA Ba # c\<rparr> \<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr> \<lparr>cfg_conf = teA Bb # ca @ c\<rparr>)"
      in cfgLM_trans_der_concat_extend)
     apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
     apply(force)
    apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
    apply(force)
   apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
   apply(force)
  apply(rename_tac x xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = teA B # wa @ C\<rparr> = \<lparr>cfg_conf = teA Bb # ca @ c @ C\<rparr>")
   apply(rename_tac xs B wa C e1 Ba c Bb ca da)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac xs B wa C e1 Ba c Bb ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da)(*strict*)
  apply(rule_tac
      x="(derivation_append da (derivation_map (der2 \<lparr>cfg_conf = teA Ba # c\<rparr> \<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr> \<lparr>cfg_conf = teA Bb # ca @ c\<rparr>) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v\<rparr>)) (length xs))"
      in exI)
  apply(rename_tac xs C e1 Ba c Bb ca da)(*strict*)
  apply(rule conjI)
   apply(rename_tac xs C e1 Ba c Bb ca da)(*strict*)
   apply(force)
  apply(rename_tac xs C e1 Ba c Bb ca da)(*strict*)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i)(*strict*)
  apply(case_tac "derivation_append da (derivation_map (der2 \<lparr>cfg_conf = teA Ba # c\<rparr> \<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr> \<lparr>cfg_conf = teA Bb # ca @ c\<rparr>) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v\<rparr>)) (length xs) (Suc i)")
   apply(rename_tac xs C e1 Ba c Bb ca da i)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append da (derivation_map (der2 \<lparr>cfg_conf = teA Ba # c\<rparr> \<lparr>prod_lhs = Ba, prod_rhs = teA Bb # ca\<rparr> \<lparr>cfg_conf = teA Bb # ca @ c\<rparr>) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v\<rparr>)) (length xs)) i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
    apply(force)
   apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
   apply(force)
  apply(rename_tac xs C e1 Ba c Bb ca da i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 c1 c2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 c1 c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a e2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac B wX)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
  apply(case_tac "i\<le>length xs")
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. case_option True (case_derivation_configuration (\<lambda>e' c'. case_option False (case_derivation_configuration (\<lambda>e c. case e' of None \<Rightarrow> False | Some e' \<Rightarrow> (\<exists>w. cfg_conf c = teA (prod_lhs e') # w) \<and> (\<exists>A w. prod_rhs e' = teA A # w))) (da i))) (da (Suc i))"
      in allE)
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def der2_def)
   apply(case_tac "Suc i \<le> length xs")
    apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
    apply(clarsimp)
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "i=length xs")
    apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs C e1 c Bb ca da e1a r l' B)(*strict*)
   apply(case_tac l')
    apply(rename_tac xs C e1 c Bb ca da e1a r l' B)(*strict*)
    prefer 2
    apply(rename_tac xs C e1 c Bb ca da e1a r l' B a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac xs C e1 c Bb ca da e1a r l' B)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def der2_def)
  apply(case_tac "i - length xs = Suc 0")
   apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i e1a r l' B wX)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs C e1 Ba c Bb ca da i r l' B wX)(*strict*)
  apply(subgoal_tac "i=Suc(length xs)")
   apply(rename_tac xs C e1 Ba c Bb ca da i r l' B wX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xs C e1 Ba c Bb ca da i r l' B wX)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_concat_extend_with_left_degen: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=liftA w1\<rparr> \<pi>1 \<lparr>cfg_conf=liftA v2@v4\<rparr>
  \<Longrightarrow> left_degen G d1
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=liftA v2\<rparr> \<pi>2 \<lparr>cfg_conf=v3\<rparr>
  \<Longrightarrow> left_degen G d2
  \<Longrightarrow> cfgLM.trans_der G (derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@v4\<rparr>)) (length \<pi>1)) \<lparr>cfg_conf=liftA w1\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=v3@v4\<rparr> \<and> left_degen G ((derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@v4\<rparr>)) (length \<pi>1)))"
  apply(rule context_conjI)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      ?v1.0="[]"
      in cfgLM_trans_der_concat_extend)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ v4\<rparr>)) (length \<pi>1) (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ v4\<rparr>)) (length \<pi>1) i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i a e ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc i"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i a e ea eb)(*strict*)
     apply(force)
    apply(rename_tac i a e ea eb)(*strict*)
    apply(force)
   apply(rename_tac i a e ea eb)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(case_tac "Suc i\<le>length \<pi>1")
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. case_option True (case_derivation_configuration (\<lambda>e' c'. case_option False (case_derivation_configuration (\<lambda>e c. case e' of None \<Rightarrow> False | Some e' \<Rightarrow> (\<exists>w. cfg_conf c = teA (prod_lhs e') # w) \<and> (\<exists>A w. prod_rhs e' = teA A # w))) (d1 i))) (d1 (Suc i))"
      in allE)
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "length \<pi>1 \<le> i")
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>c. length \<pi>1 + c = i")
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      x="i-length \<pi>1"
      in exI)
   apply(force)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1 c2 c)(*strict*)
  apply(erule_tac
      x="c"
      and P="\<lambda>c. case_option True (case_derivation_configuration (\<lambda>e' c'. case_option False (case_derivation_configuration (\<lambda>e c. case e' of None \<Rightarrow> False | Some e' \<Rightarrow> (\<exists>w. cfg_conf c = teA (prod_lhs e') # w) \<and> (\<exists>A w. prod_rhs e' = teA A # w))) (d2 c))) (d2 (Suc c))"
      in allE)
  apply(rename_tac e1 e2 c1 c2 c)(*strict*)
  apply(case_tac "c")
   apply(rename_tac e1 e2 c1 c2 c)(*strict*)
   prefer 2
   apply(rename_tac e1 e2 c1 c2 c nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 nat)(*strict*)
   apply(case_tac "d2 (Suc (Suc nat))")
    apply(rename_tac e1 e2 c1 c2 nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac e1 e2 c1 c2 nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 nat b)(*strict*)
   apply(case_tac "d2 ((Suc nat))")
    apply(rename_tac e1 e2 c1 nat b)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 nat b a)(*strict*)
   apply(case_tac a)
   apply(rename_tac e1 e2 c1 nat b a option ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c1 c2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c1=\<lparr>cfg_conf = liftA v2 @ v4\<rparr>")
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def derivation_map_def cfgLM.trans_der_def)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2)(*strict*)
  apply(case_tac "d2 (Suc 0)")
   apply(rename_tac e1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_map_def cfgLM.trans_der_def)
  apply(rename_tac e1 e2 c2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac e1 e2 c2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2 option b)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac e1 e2 c2 option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c2 option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac e1 e2 c2 option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2 option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac e1 e2 c2 option b optiona ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c2 option b optiona ba a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2 b optiona ba a w A wa)(*strict*)
  apply(case_tac ba)
  apply(rename_tac e1 e2 c2 b optiona ba a w A wa cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2 b optiona a w A wa)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac e1 e2 c2 b optiona a w A wa)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def derivation_map_def cfgLM.trans_der_def)
  apply(rename_tac e1 e2 c2 b optiona a w A wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2 b optiona w A wa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac e1 e2 c2 b optiona w A wa prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c2 b optiona w A wa prod_lhsa)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e1 c2 b optiona w A wa prod_lhsa l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac e1 c2 b optiona w A wa prod_lhsa l r)(*strict*)
   prefer 2
   apply(rename_tac e1 c2 b optiona w A wa prod_lhsa l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c2 b optiona w A wa prod_lhsa r a list)(*strict*)
   apply(case_tac c2)
   apply(rename_tac e1 c2 b optiona w A wa prod_lhsa r a list cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 b optiona w A wa prod_lhsa r a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac e1 b optiona w A wa prod_lhsa r a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 b optiona w A wa prod_lhsa r a list ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba)(*strict*)
   apply(case_tac v2)
    apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba)(*strict*)
    apply(clarsimp)
    apply(case_tac v4)
     apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def derivation_map_def cfgLM.trans_der_def)
    apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def cfgLM.trans_der_def)
   apply(rename_tac e1 b optiona w A wa prod_lhsa r list ba a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 c2 b optiona w A wa prod_lhsa l r)(*strict*)
  apply(clarsimp)
  done

lemma der1_left_degen: "
  left_degen G (der1 c)"
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: der1_def)
  done

lemma cfgLM_trans_der_concat_extend_prime_with_left_degen: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=liftA w1\<rparr> \<pi>1 \<lparr>cfg_conf=liftA v2@v4\<rparr>
  \<Longrightarrow> left_degen G d1
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=liftA v2\<rparr> \<pi>2 \<lparr>cfg_conf=v3\<rparr>
  \<Longrightarrow> left_degen G d2
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA w1\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=v3@v4\<rparr> \<and> left_degen G d"
  apply(rule_tac
      x="(derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@v4\<rparr>)) (length \<pi>1))"
      in exI)
  apply(rule cfgLM_trans_der_concat_extend_with_left_degen)
      apply(force)+
  done

lemma der2_left_degen: "
  (\<exists>w. cfg_conf c = teA (prod_lhs p) # w)
  \<Longrightarrow> (\<exists>A w. prod_rhs p = teA A # w)
  \<Longrightarrow> left_degen G (der2 c p c')"
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac w A wa i)(*strict*)
  apply(simp add: der2_def)
  done

lemma derivation_drop_preserves_left_degen: "
  valid_cfg G
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> left_degen G (derivation_drop d n)"
  apply(simp add: left_degen_def sat_refined_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(erule_tac
      x="i+n"
      in allE)
  apply(case_tac "d (Suc (i+n))")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac option b a optiona ba)(*strict*)
  apply(clarsimp)
  done

lemma left_degen_context_persists: "
  valid_cfg G
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = teA A # w1\<rparr> \<pi> \<lparr>cfg_conf = teA B # w2\<rparr>
  \<Longrightarrow> suffix w2 w1"
  apply(induct "length \<pi>" arbitrary: d A w1 \<pi> B w2)
   apply(rename_tac \<pi> d A w1 B w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A w1 B w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: suffix_def)
   apply(clarsimp)
  apply(rename_tac x \<pi> d A w1 B w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<pi>=[] \<or> (\<exists>w' a'. \<pi>=w'@[a'])")
   apply(rename_tac x \<pi> d A w1 B w2)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x \<pi> d A w1 B w2)(*strict*)
  apply(erule disjE)
   apply(rename_tac x \<pi> d A w1 B w2)(*strict*)
   apply(force)
  apply(rename_tac x \<pi> d A w1 B w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A w1 B w2 w' a')(*strict*)
  apply(rename_tac \<pi> \<pi>X)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X)(*strict*)
  apply(erule_tac
      x="\<pi>"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="d"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="w1"
      in meta_allE)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length(\<pi>)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
     apply(force)
    apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
    apply(force)
   apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
   apply(force)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e1 e2 c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e1 e2 c1 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e1 e2 c1 l r prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e1 e2 c1 l r prod_lhsa prod_rhsa cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A w1 B w2 \<pi> \<pi>X e1 l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A v)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 l r A v)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 l r A v)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 l r A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac l')
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v l')(*strict*)
   prefer 2
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v l' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v l')(*strict*)
  apply(clarsimp)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="r"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) (length \<pi>)) = SSn + 1 - Suc 0" for SSn)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc(length \<pi>))) = SSn + 1 - Suc 0" for SSn)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
   apply(clarsimp)
   apply(rule listEqI)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
    apply(clarsimp)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (length(\<pi>)) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
     apply(force)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(force)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc(length(\<pi>))) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
     apply(force)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(force)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Some(\<pi>!i)"
      and s="(map Some \<pi> @ [Some \<pi>X])!i"
      in ssubst)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(rule_tac
      t="(map Some \<pi> @ [Some \<pi>X]) ! i"
      and s="(map Some \<pi>) ! i"
      in ssubst)
     apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(force)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(rule_tac
      t="map Some \<pi> @ [Some \<pi>X]"
      and s="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (length \<pi>)))"
      in ssubst)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(force)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (length \<pi>))) ! i"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (Suc (length \<pi>))) ! i)"
      in ssubst)
    apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v i)(*strict*)
   apply(force)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 r A v)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 A v c)(*strict*)
  apply(case_tac v)
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 A v c)(*strict*)
   prefer 2
   apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 A v c a list)(*strict*)
   apply(force)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 A v c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d Aa w1 B w2 \<pi> \<pi>X e1 A c)(*strict*)
  apply(simp add: left_degen_def)
  apply(simp add: sat_refined_def)
  apply(erule_tac
      x="length \<pi>"
      in allE)
  apply(clarsimp)
  done

definition appL :: "
  'a list
  \<Rightarrow> ('a
  \<Rightarrow> 'a)
  \<Rightarrow> 'a list"
  where
    "appL w f \<equiv>
   (if w = []
  then w
  else (butlast w @ [f (last w)]))"

definition enforceSuffixS :: "
  'a list list
  \<Rightarrow> nat
  \<Rightarrow> nat set"
  where
    "enforceSuffixS w k \<equiv>
  {n. \<exists>i. k + i < length w
  \<and> n = length (w ! (k + i)) }"

definition enforceSuffix :: "
   'a list list
  \<Rightarrow> 'a list list"
  where
    "enforceSuffix w \<equiv>
   (let minLen = \<lambda>k. Min (enforceSuffixS w k) in (map (\<lambda>n. takeB (minLen n) (w ! n)) (nat_seq 0 (length w - Suc 0))))"

lemma enforceSuffixS_finite: "
  finite (enforceSuffixS w i)"
  apply(induct w arbitrary: i rule: rev_induct)
   apply(rename_tac i)(*strict*)
   apply(simp add: enforceSuffixS_def)
  apply(rename_tac x xs i)(*strict*)
  apply(simp add: enforceSuffixS_def)
  apply(erule_tac
      x="i"
      in meta_allE)
  apply(rule_tac
      B="{n. (\<exists>ia. i + ia < length xs \<and> n = length (xs ! (i + ia)))}\<union>{length x}"
      in finite_subset)
   apply(rename_tac x xs i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs i ia)(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(case_tac "i+ia<length xs")
   apply(rename_tac x xs i ia)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(xs @ [x]) ! (i + ia)"
      and s="xs ! (i + ia)"
      in ssubst)
    apply(rename_tac x xs i ia)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac x xs i ia)(*strict*)
   apply(force)
  apply(rename_tac x xs i ia)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i+ia=length xs")
   apply(rename_tac x xs i ia)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs i ia)(*strict*)
  apply(clarsimp)
  done

lemma enforceSuffixS_smaller: "
  i\<le>k
    \<Longrightarrow> k < length S
    \<Longrightarrow> Min (enforceSuffixS (map ESplitItem_ignore S) i) \<le> length (ESplitItem_ignore (S ! k))"
  apply(rule Lattices_Big.linorder_class.Min_le)
   apply(rule enforceSuffixS_finite)
  apply(simp add: enforceSuffixS_def)
  apply(rule_tac
      x="k-i"
      in exI)
  apply(clarsimp)
  done

lemma enforceSuffixS_shift: "
    length w=n
    \<Longrightarrow> enforceSuffixS (w @ v) n = enforceSuffixS v 0"
  apply(simp add: enforceSuffixS_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  done

lemma Min_enforceSuffixS_single: "
    Min (enforceSuffixS [w] 0) = length w"
  apply(simp add: enforceSuffixS_def)
  done

definition CON :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "CON L R X = L@X@R"

lemma cfgLMMIy_cfgLMMIP_concatenation: "
  valid_cfg G
  \<Longrightarrow> R1=[] \<or> R2=[]
  \<Longrightarrow> \<alpha>2\<noteq>[]
  \<Longrightarrow> cfgLMMIy G d1 (liftA w1) \<pi>1 (liftB \<alpha>1@liftA w1') []
  \<Longrightarrow> \<pi>1 \<noteq> []
  \<Longrightarrow> \<pi>2 \<noteq> []
  \<Longrightarrow> cfgLMMIP G d2 (liftA w2) \<pi>2 (liftB \<alpha>2) (liftA w2')
  \<Longrightarrow> CON [] (liftA R1) (liftA w1) = (liftA w3)
  \<Longrightarrow> CON [] (liftA R1) (liftB \<alpha>1@liftA w1') = CON (liftB \<alpha>1) (liftA R2) (liftA w2)
  \<Longrightarrow> CON (liftB \<alpha>1) (liftA R2) ((liftB \<alpha>2)@(liftA w2')) = (liftB(\<alpha>1@\<alpha>2))@(liftA w3')
  \<Longrightarrow> set(R1@R2) \<subseteq> cfg_nonterminals G
  \<Longrightarrow> \<exists>d3. cfgLMMIP G d3 (liftA w3) (\<pi>1@\<pi>2) (liftB(\<alpha>1@\<alpha>2)) (liftA w3')"
  apply(simp add: CON_def)
  apply(clarsimp)
  apply(simp add: liftB_commutes_over_concat)
  apply(subgoal_tac "w3=w1@R1")
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: liftA_commutes_over_concat)
   apply(rule sym)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "liftA w1 @ liftA R1 = liftA (w1 @ R1)")
  apply(subgoal_tac "w1'@R1=w2@R2")
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: liftA_commutes_over_concat)
  apply(thin_tac "liftA w1' @ liftA R1 = liftA w2 @ liftA R2")
  apply(subgoal_tac "w3'=w2'@R2")
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: liftA_commutes_over_concat)
   apply(rule sym)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "liftA w2' @ liftA R2 = liftA (w2' @ R2)")
  apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSd SSw1 SSrenPI10 SSv SSw1' SSw2)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="liftA R1"
      and ?d1.0="d1"
      in cfgLM_trans_der_context)
     apply(force)
    prefer 2
    apply(clarsimp)
    apply(simp add: cfg_configurations_def)
    apply(rule conjI)
     apply (metis setA_liftA)
    apply (simp add: setB_liftA)
   apply(simp add: cfgLMMIy_def)
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>1 @ liftA w1'\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply(unfold cfgLM.trans_der_def cfgLMMIy_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac e ea)(*strict*)
   apply(erule conjE)+
   apply(fold cfgLM.trans_der_def cfgLMMIy_def)
   apply(rule_tac
      d="d1"
      in cfgLM.belongs_configurations)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(simp add: cfgLMMIP_def)
  apply(subgoal_tac "cfgLM.trans_der SSG SSd \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSd SSw1 SSrenPI10 SSv SSw1' SSw2)
   prefer 2
   apply(rule_tac
      G="G"
      and v="\<alpha>1"
      and ?w2.0="liftA R2"
      and ?d1.0="d2"
      in cfgLM_trans_der_context)
     apply(force)
    prefer 2
    apply(clarsimp)
    apply(simp add: cfg_configurations_def)
    apply(simp add: setAConcat)
    apply(simp add: setBConcat)
    apply(rule conjI)
     apply (metis setA_liftA)
    apply (simp add: setB_liftA)
   apply(force)
  apply(simp add: cfgLMMIP_def)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   prefer 2
   apply(rule_tac
      G="G"
      and ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)"
      and ?d2.0="derivation_map d2 (\<lambda>x. \<lparr>cfg_conf = liftB \<alpha>1 @ cfg_conf x @ liftA R2\<rparr>)"
      in cfgLM_trans_der_concat_extend_prime)
     apply(force)
    apply(force)
   apply(rule_tac
      t="liftB \<alpha>1 @ liftA w1' @ liftA R1"
      and s="liftB \<alpha>1 @ liftA w2 @ liftA R2"
      in ssubst)
    apply(clarsimp)
    apply(rule_tac
      t="liftA w1' @ liftA R1"
      and s="liftA(w1'@R1)"
      in ssubst)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rule_tac
      t="liftA w2 @ liftA R2"
      and s="liftA(w2@R2)"
      in ssubst)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(simp add: liftA_commutes_over_concat)
  apply(rename_tac d)(*strict*)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgLMMIyX_def cfgLMMIy_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      G="G"
      and ?\<pi>1.0="\<pi>1"
      and ?\<pi>2.0="\<pi>2"
      and ?w1.0="butlast (liftA w1)"
      and \<alpha>="[]"
      and ?w2.0="[]"
      in applicable_contra)
       apply(rename_tac d)(*strict*)
       apply(force)
      apply(rename_tac d)(*strict*)
      apply(force)
     apply(rename_tac d)(*strict*)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "R1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac d)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac d)(*strict*)
   apply(erule disjE)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      G="G"
      and ?\<pi>1.0="\<pi>1"
      and ?\<pi>2.0="\<pi>2"
      and ?w1.0="butlast (liftA w1)"
      and \<alpha>="[]"
      and ?w2.0="[]"
      in applicable_contra)
       apply(rename_tac d)(*strict*)
       apply(force)
      apply(rename_tac d)(*strict*)
      apply(force)
     apply(rename_tac d)(*strict*)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w' a')(*strict*)
   apply(simp add: liftA_commutes_over_concat)
   apply(subgoal_tac "butlast (liftA w1' @ liftA w' @ [teA a'])=SSX" for SSX)
    apply(rename_tac d w' a')(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac d w' a')(*strict*)
   apply(rule_tac
      G="G"
      and ?\<pi>2.0="\<pi>2"
      and ?\<pi>1.0="\<pi>1"
      and ?w2.0="liftB \<alpha>1 @ liftA w1'"
      and ?w3.0="liftA w'"
      and ?w1.0="liftA w1"
      in applicable_contra2)
      apply(rename_tac d w' a')(*strict*)
      apply(force)
     apply(rename_tac d w' a')(*strict*)
     prefer 2
     apply(rule_tac
      t="liftA w1 @ liftA w'"
      and s="butlast (liftA w1 @ liftA w' @ [teA a'])"
      in subst)
      apply(rename_tac d w' a')(*strict*)
      apply(rule butlast_direct)
      apply(force)
     apply(rename_tac d w' a')(*strict*)
     apply(force)
    apply(rename_tac d w' a')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d w' a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<not> applicable G \<pi>2 (liftA w1' @ liftA w')")
    apply(rename_tac d w' a')(*strict*)
    prefer 2
    apply(rule_tac
      t="liftA w1' @ liftA w'"
      and s="butlast (liftA w1' @ liftA w' @ [teA a'])"
      in subst)
     apply(rename_tac d w' a')(*strict*)
     apply(force)
    apply(rename_tac d w' a')(*strict*)
    apply(force)
   apply(rename_tac d w' a')(*strict*)
   apply(thin_tac "\<not> applicable G \<pi>2 (butlast (liftA w1' @ liftA w' @ [teA a']))")
   apply(rule_tac
      ?w2.0="[]"
      and ?w1.0="liftA w1' @ liftA w'"
      and G="G"
      and ?\<pi>1.0="\<pi>2"
      and ?\<pi>2.0="[]"
      and \<alpha>="\<alpha>1"
      in applicable_contra)
      apply(rename_tac d w' a')(*strict*)
      apply(force)
     apply(rename_tac d w' a')(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d w' a')(*strict*)
    apply(force)
   apply(rename_tac d w' a')(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(simp add: setAConcat)
   apply(simp add: setBConcat)
  apply(rename_tac d)(*strict*)
  apply(simp add: cfgLMMPX_def)
  apply(clarsimp)
  apply(rename_tac d \<pi>' da c)(*strict*)
  apply(case_tac "prefix \<pi>' \<pi>1")
   apply(rename_tac d \<pi>' da c)(*strict*)
   apply(simp add: prefix_def)
   apply(thin_tac "strict_prefix \<pi>' (\<pi>1 @ \<pi>2)")
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(thin_tac "cfgLMMIy G d1 (liftA w1) (\<pi>' @ ca) (liftB \<alpha>1 @ liftA w1') []")
   apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> (\<pi>' @ ca @ \<pi>2) \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ liftA w2' @ liftA R2\<rparr>")
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(thin_tac "cfgLMMIyX G d2 (liftA w2) \<pi>2")
   apply(thin_tac "\<forall>\<pi>'. strict_prefix \<pi>' \<pi>2 \<longrightarrow> (\<forall>d c. \<not> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w2\<rparr> \<pi>' \<lparr>cfg_conf = liftB \<alpha>2 @ c\<rparr>)")
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = liftA w2\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha>2 @ liftA w2'\<rparr>")
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(thin_tac "cfgLM.trans_der G (derivation_map d2 (\<lambda>x. \<lparr>cfg_conf = liftB \<alpha>1 @ cfg_conf x @ liftA R2\<rparr>)) \<lparr>cfg_conf = liftB \<alpha>1 @ liftA w2 @ liftA R2\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ liftA w2' @ liftA R2\<rparr>")
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(simp add: liftA_commutes_over_concat)
   apply(rename_tac \<pi>' da c ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. (derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)) (length \<pi>') = Some (pair e c)")
    apply(rename_tac \<pi>' da c ca)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>' da c ca e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length(\<pi>'@ca)"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac \<pi>' da c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' da c ca e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da c ca e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' da c ca e cb)(*strict*)
   apply(case_tac cb)
   apply(rename_tac \<pi>' da c ca e cb cfg_confa)(*strict*)
   apply(rename_tac w)
   apply(rename_tac \<pi>' da c ca e cb w)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' da c ca e w)(*strict*)
   apply(subgoal_tac "cfgLM.trans_der G (derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)) \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> \<pi>' \<lparr>cfg_conf = w\<rparr>")
    apply(rename_tac \<pi>' da c ca e w)(*strict*)
    prefer 2
    apply(rule_tac
      n="length(\<pi>')"
      in cfgLM.trans_der_crop)
        apply(rename_tac \<pi>' da c ca e w)(*strict*)
        apply(simp add: )
       apply(rename_tac \<pi>' da c ca e w)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' da c ca e w)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' da c ca e w)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da c ca e w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da c ca e w)(*strict*)
   apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
    apply(rename_tac \<pi>' da c ca e w)(*strict*)
    prefer 2
    apply(rule_tac
      ?w2.0="[]"
      and ?v1.0="SSX"
      and ?w1.0="liftA w1 @ liftA R1"
      and ?d2.0="derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)"
      and ?d1.0="da" for SSX
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
      apply(rename_tac \<pi>' da c ca e w)(*strict*)
      apply(simp add: )
     apply(rename_tac \<pi>' da c ca e w)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da c ca e w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da c ca e w)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' da c ca e)(*strict*)
   apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> \<pi>' \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ c\<rparr>")
   apply(rename_tac \<pi>' da c ca e)(*strict*)
   apply(thin_tac "cfgLM.trans_der G (derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)) \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> \<pi>' \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ c\<rparr>")
   apply(rename_tac \<pi>' da c ca e)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ c\<rparr> @ w = cfg_get_history \<lparr>cfg_conf = liftB \<alpha>1 @ liftA w1' @ liftA R1\<rparr>")
    apply(rename_tac \<pi>' da c ca e)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>' da c ca e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)"
      and i="length \<pi>'"
      and j="length ca"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac \<pi>' da c ca e ea)(*strict*)
         apply(simp add: )
        apply(rename_tac \<pi>' da c ca e ea)(*strict*)
        apply(force)
       apply(rename_tac \<pi>' da c ca e ea)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' da c ca e ea)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' da c ca e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da c ca e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da c ca e)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' c ca e w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "\<alpha>1@\<alpha>2@maxTermPrefix c @ w = \<alpha>1")
    apply(rename_tac \<pi>' c ca e w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' c ca e w)(*strict*)
   apply(rule_tac
      t="\<alpha>1@\<alpha>2@maxTermPrefix c @ w"
      and s="maxTermPrefix (liftB \<alpha>1 @ liftB \<alpha>2 @ c) @ w"
      in ssubst)
    apply(rename_tac \<pi>' c ca e w)(*strict*)
    apply (metis concat_asso maxTermPrefix_shift)
   apply(rename_tac \<pi>' c ca e w)(*strict*)
   apply (metis CON_def liftA_commutes_over_concat maxTermPrefix_shift maximalTermPrefix_split)
  apply(rename_tac d \<pi>' da c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d \<pi>' da c)(*strict*)
   prefer 2
   apply(rule strict_prefix_prefix_alt)
    apply(rename_tac d \<pi>' da c)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c)(*strict*)
   apply(force)
  apply(rename_tac d \<pi>' da c)(*strict*)
  apply(thin_tac "\<not> \<pi>' \<sqsubseteq> \<pi>1")
  apply(thin_tac "strict_prefix \<pi>' (\<pi>1 @ \<pi>2)")
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac d da c y ca)(*strict*)
  apply(erule_tac
      x="y"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. da (length \<pi>1) = Some (pair e c)")
   apply(rename_tac d da c y ca)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d da c y ca e ea eb ec ed)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@y)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac d da c y ca e ea eb ec ed)(*strict*)
     apply(force)
    apply(rename_tac d da c y ca e ea eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac d da c y ca e ea eb ec ed)(*strict*)
   apply(force)
  apply(rename_tac d da c y ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da c y ca e cb)(*strict*)
  apply(case_tac cb)
  apply(rename_tac d da c y ca e cb cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d da c y ca e cb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da c y ca e w)(*strict*)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> \<pi>1 \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac d da c y ca e w)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac d da c y ca e w)(*strict*)
       apply(simp add: )
      apply(rename_tac d da c y ca e w)(*strict*)
      apply(force)
     apply(rename_tac d da c y ca e w)(*strict*)
     apply(force)
    apply(rename_tac d da c y ca e w)(*strict*)
    apply(force)
   apply(rename_tac d da c y ca e w)(*strict*)
   apply(force)
  apply(rename_tac d da c y ca e w)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac d da c y ca e w)(*strict*)
   prefer 2
   apply(rule_tac
      ?w2.0="[]"
      and ?v1.0="SSX"
      and ?w1.0="liftA w1 @ liftA R1"
      and ?d1.0="derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ liftA R1\<rparr>)"
      and ?d2.0="da" for SSX
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac d da c y ca e w)(*strict*)
     apply(force)
    apply(rename_tac d da c y ca e w)(*strict*)
    apply(force)
   apply(rename_tac d da c y ca e w)(*strict*)
   apply(force)
  apply(rename_tac d da c y ca e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da c y ca e)(*strict*)
  apply(subgoal_tac "\<exists>d c. cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<alpha>1@liftA w2\<rparr> y \<lparr>cfg_conf = liftB \<alpha>1@(liftB \<alpha>2 @ c)\<rparr>")
   apply(rename_tac d da c y ca e)(*strict*)
   apply(erule exE)+
   apply(rename_tac d da c y ca e db cb)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftA w2\<rparr> y \<lparr>cfg_conf = (liftB \<alpha>2 @ cb)\<rparr>")
    apply(rename_tac d da c y ca e db cb)(*strict*)
    prefer 2
    apply(rule_tac
      \<alpha>="\<alpha>1"
      and d="db"
      in cfgLM_drop_terminal_prefix)
     apply(rename_tac d da c y ca e db cb)(*strict*)
     apply(force)
    apply(rename_tac d da c y ca e db cb)(*strict*)
    apply(force)
   apply(rename_tac d da c y ca e db cb)(*strict*)
   apply(force)
  apply(rename_tac d da c y ca e)(*strict*)
  apply(thin_tac "\<forall>d c. \<not> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w2\<rparr> y \<lparr>cfg_conf = liftB \<alpha>2 @ c\<rparr>")
  apply(rename_tac d da c y ca e)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<alpha>1 @ liftA w1' @ liftA R1\<rparr> y \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ c\<rparr>")
   apply(rename_tac d da c y ca e)(*strict*)
   prefer 2
   apply(rule_tac
      n="length \<pi>1"
      and d="da"
      in cfgLM.trans_der_skip_prime)
       apply(rename_tac d da c y ca e)(*strict*)
       apply(force)
      apply(rename_tac d da c y ca e)(*strict*)
      apply(force)
     apply(rename_tac d da c y ca e)(*strict*)
     apply(force)
    apply(rename_tac d da c y ca e)(*strict*)
    apply(force)
   apply(rename_tac d da c y ca e)(*strict*)
   apply(force)
  apply(rename_tac d da c y ca e)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> (\<pi>1 @ y) \<lparr>cfg_conf = liftB \<alpha>1 @ liftB \<alpha>2 @ c\<rparr>")
  apply(rename_tac d da c y ca e)(*strict*)
  apply(thin_tac "da (length \<pi>1) = Some (pair e \<lparr>cfg_conf = liftB \<alpha>1 @ liftA w1' @ liftA R1\<rparr>)")
  apply(rename_tac d da c y ca e)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = liftA w1 @ liftA R1\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>1 @ liftA w1' @ liftA R1\<rparr>")
  apply(rename_tac d da c y ca e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c y ca da)(*strict*)
  apply(thin_tac "cfgLMMIyX G d2 (liftA w2) (y @ ca)")
  apply(erule disjE)
   apply(rename_tac d c y ca da)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac
      x="da"
      in exI)
   apply(simp add: liftA_commutes_over_concat)
   apply(force)
  apply(rename_tac d c y ca da)(*strict*)
  apply(clarsimp)
  apply(simp add: liftA_commutes_over_concat)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d c y ca da)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="da"
      and ?w1.0="liftB \<alpha>1 @ liftA w2"
      and y="liftA R2"
      and \<pi>="y"
      in unseen_nonterminal_tail_can_be_removed)
      apply(rename_tac d c y ca da)(*strict*)
      apply(force)
     apply(rename_tac d c y ca da)(*strict*)
     apply(force)
    apply(rename_tac d c y ca da)(*strict*)
    apply(subgoal_tac "applicable G (y@ca) (liftA w2)")
     apply(rename_tac d c y ca da)(*strict*)
     apply(case_tac "applicable G y (liftB \<alpha>1 @ liftA w2)")
      apply(rename_tac d c y ca da)(*strict*)
      apply(force)
     apply(rename_tac d c y ca da)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac d c y ca da)(*strict*)
      apply(force)
     apply(rename_tac d c y ca da)(*strict*)
     apply(rule_tac
      ?w2.0="[]"
      and \<alpha>="[]"
      and G="G"
      and ?\<pi>2.0="ca"
      and ?\<pi>1.0="y"
      in applicable_contra)
        apply(rename_tac d c y ca da)(*strict*)
        apply(force)
       apply(rename_tac d c y ca da)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac d c y ca da)(*strict*)
      apply(case_tac "applicable G y (liftA w2 @ [])")
       apply(rename_tac d c y ca da)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d c y ca da)(*strict*)
      apply(subgoal_tac "applicable G y (liftB \<alpha>1 @ liftA w2)")
       apply(rename_tac d c y ca da)(*strict*)
       apply(force)
      apply(rename_tac d c y ca da)(*strict*)
      apply(rule applicable_append_liftB)
        apply(rename_tac d c y ca da)(*strict*)
        apply(force)
       apply(rename_tac d c y ca da)(*strict*)
       apply(force)
      apply(rename_tac d c y ca da)(*strict*)
      apply(simp add: cfg_configurations_def)
      apply(clarsimp)
      apply(rename_tac d c y ca da x)(*strict*)
      apply(simp add: setAConcat)
      apply(simp add: setBConcat)
      apply (simp add: setA_liftB)
      apply (simp add: setB_liftB)
      apply(force)
     apply(rename_tac d c y ca da)(*strict*)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac d c y ca da)(*strict*)
    apply(simp add: applicable_def)
    apply(force)
   apply(rename_tac d c y ca da)(*strict*)
   apply(rule liftB_liftA_inter)
  apply(rename_tac d c y ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c y ca da db cb)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac d c y ca da db cb)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="da"
      and ?d2.0="db"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac d c y ca da db cb)(*strict*)
     apply(force)
    apply(rename_tac d c y ca da db cb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d c y ca da db cb)(*strict*)
   apply(force)
  apply(rename_tac d c y ca da db cb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "strict_prefix cb (liftB \<alpha>2) \<or> SSX" for SSX)
   apply(rename_tac d c y ca da db cb)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac d c y ca da db cb)(*strict*)
  apply(erule disjE)
   apply(rename_tac d c y ca da db cb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d y ca da db cc)(*strict*)
   apply(force)
  apply(rename_tac d c y ca da db cb)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac d c y ca da db cb cc)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d c y ca da db cb cc)(*strict*)
   prefer 2
   apply(rule liftB_append)
   apply(force)
  apply(rename_tac d c y ca da db cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c y ca da db l1 l2)(*strict*)
  apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
  apply(simp add: liftB_commutes_over_concat)
  apply(case_tac l2)
   apply(rename_tac d c y ca da db l1 l2)(*strict*)
   prefer 2
   apply(rename_tac d c y ca da db l1 l2 a list)(*strict*)
   apply(case_tac R2)
    apply(rename_tac d c y ca da db l1 l2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d c y ca da db l1 l2 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c y ca da db l1 l2)(*strict*)
  apply(clarsimp)
  done

definition l3seq :: "('a,'b)DT_l2_l3_nonterminals list \<Rightarrow> bool" where
  "l3seq w = (\<forall>w1 x y w2. w=w1@[x,y]@w2 \<longrightarrow> (
  case x of cons_l2 q A \<Rightarrow> False
  | cons_l3 q1 A1 q1' \<Rightarrow> (case y of cons_l2 q A \<Rightarrow> False
  | cons_l3 q2 A2 q2' \<Rightarrow> (q1'=q2))
  ))"

lemma l3seq_change_initial_state: "
  \<forall>q A. cons_l2 q A \<notin> set \<beta>
  \<Longrightarrow> l3seq (cons_l3 q1 A q2 # \<beta>)
  \<Longrightarrow> l3seq (cons_l3 q3 A q2 # \<beta>)"
  apply(simp add: l3seq_def)
  apply(clarsimp)
  apply(rename_tac w1 x y w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac w1 x y w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac y w2)(*strict*)
   apply(case_tac y)
    apply(rename_tac y w2 q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w2 q b)(*strict*)
    apply(force)
   apply(rename_tac y w2 q1a b q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 q1a b q2a)(*strict*)
   apply(force)
  apply(rename_tac w1 x y w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y w2 list)(*strict*)
  apply(case_tac x)
   apply(rename_tac x y w2 list q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac y w2 list q b)(*strict*)
   apply(erule_tac
      x="cons_l3 q1 A q2 # list"
      in allE)
   apply(clarsimp)
  apply(rename_tac x y w2 list q1a b q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w2 list q1a b q2a)(*strict*)
  apply(case_tac y)
   apply(rename_tac y w2 list q1a b q2a q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 list q1a b q2a q ba)(*strict*)
   apply(force)
  apply(rename_tac y w2 list q1a b q2a q1aa ba q2aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w2 list q1a b q2a q1aa ba q2aa)(*strict*)
  apply(erule_tac
      x="cons_l3 q1 A q2 # list"
      in allE)
  apply(clarsimp)
  done

lemma l3seq_drop_initial_state: "
  l3seq (cons_l3 q1 A q2 # \<beta>)
  \<Longrightarrow> l3seq (\<beta>)"
  apply(simp add: l3seq_def)
  apply(clarsimp)
  apply(rename_tac w1 x y w2)(*strict*)
  apply(erule_tac
      x="[cons_l3 q1 A q2]@w1"
      in allE)
  apply(clarsimp)
  done

lemma l3_seq_add_initial_state: "
  l3seq (cons_l3 q0 s1 p1 # \<beta>1)
  \<Longrightarrow> l3seq (cons_l3 q1 s2 qX1 # cons_l3 qX1 s3 p1 # \<beta>1)"
  apply(simp add: l3seq_def)
  apply(clarsimp)
  apply(rename_tac w1 x y w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac w1 x y w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 x y w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y w2 list)(*strict*)
  apply(case_tac list)
   apply(rename_tac x y w2 list)(*strict*)
   apply(clarsimp)
   apply(rename_tac y w2)(*strict*)
   apply(case_tac y)
    apply(rename_tac y w2 q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w2 q b)(*strict*)
    apply(force)
   apply(rename_tac y w2 q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 q1 b q2)(*strict*)
   apply(force)
  apply(rename_tac x y w2 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y w2 lista)(*strict*)
  apply(case_tac x)
   apply(rename_tac x y w2 lista q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac y w2 lista q b)(*strict*)
   apply(erule_tac
      x="cons_l3 q0 s1 p1 # lista"
      in allE)
   apply(force)
  apply(rename_tac x y w2 lista q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w2 lista q1 b q2)(*strict*)
  apply(case_tac y)
   apply(rename_tac y w2 lista q1 b q2 q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 lista q1 b q2 q ba)(*strict*)
   apply(erule_tac
      x="cons_l3 q0 s1 p1 # lista"
      in allE)
   apply(force)
  apply(rename_tac y w2 lista q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w2 lista q1 b q2 q1a ba q2a)(*strict*)
  apply(erule_tac
      x="cons_l3 q0 s1 p1 # lista"
      in allE)
  apply(force)
  done

lemma l3seq_append_decomp2: "
  l3seq (x@y)
  \<Longrightarrow> l3seq y"
  apply(simp add: l3seq_def)
  apply(clarsimp)
  apply(rename_tac w1 xa y w2)(*strict*)
  apply(case_tac xa)
   apply(rename_tac w1 xa y w2 q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 y w2 q b)(*strict*)
   apply(erule_tac
      x="x@w1"
      in allE)
   apply(clarsimp)
  apply(rename_tac w1 xa y w2 q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 y w2 q1 b q2)(*strict*)
  apply(case_tac y)
   apply(rename_tac w1 y w2 q1 b q2 q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 q1 b q2 q ba)(*strict*)
   apply(erule_tac
      x="x@w1"
      in allE)
   apply(clarsimp)
  apply(rename_tac w1 y w2 q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 q1 b q2 q1a ba q2a)(*strict*)
  apply(erule_tac
      x="x@w1"
      in allE)
  apply(clarsimp)
  done

definition isl2 :: "('a,'b)DT_l2_l3_nonterminals \<Rightarrow> bool" where
  "isl2 x =(case x of cons_l2 q A \<Rightarrow> True | _ \<Rightarrow> False)"

definition isl3 :: "('a,'b)DT_l2_l3_nonterminals \<Rightarrow> bool" where
  "isl3 x =(case x of cons_l2 q A \<Rightarrow> False | _ \<Rightarrow> True)"

definition notfinishing :: "(('q,'x)DT_l2_l3_nonterminals,'b)cfg_step_label \<Rightarrow> bool" where
  "notfinishing p = (prod_rhs p = [] \<longrightarrow> isl3 (prod_lhs p))"

lemma notfinishing_use: "
  notfinishing p
  \<Longrightarrow> prod_rhs p=[]
  \<Longrightarrow> isl3 (prod_lhs p)"
  apply(simp add: notfinishing_def)
  done

definition notfinishingL :: "(('q,'x)DT_l2_l3_nonterminals,'b)cfg_step_label list \<Rightarrow> bool" where
  "notfinishingL ps = (\<forall>i<length ps. notfinishing (ps!i))"

lemma notfinishingL_use: "
  notfinishingL \<pi>
  \<Longrightarrow> i<length \<pi>
  \<Longrightarrow> X = (prod_lhs (\<pi>!i))
  \<Longrightarrow> prod_rhs (\<pi>!i)=[]
  \<Longrightarrow> isl3 X"
  apply(simp add: notfinishingL_def)
  apply(rule notfinishing_use)
   apply(force)
  apply(force)
  done

lemma notfinishingL_foldl: "
  notfinishingL (foldl (@) [] w)
  \<Longrightarrow> i<length w
  \<Longrightarrow> notfinishingL (w!i)"
  apply(induct w arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "foldl (@) a w=a@foldl (@) [] w")
   apply(rename_tac a w i)(*strict*)
   prefer 2
   apply(rule foldl_first)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w)(*strict*)
   apply(simp add: notfinishingL_def)
   apply(clarsimp)
   apply(rename_tac a w i)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      t="a!i"
      and s="(a @ foldl (@) [] w) ! i"
      in subst)
    apply(rename_tac a w i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac a w i)(*strict*)
   apply(force)
  apply(rename_tac a w i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a w nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a w nat)(*strict*)
  apply(simp add: notfinishingL_def)
  apply(clarsimp)
  apply(rename_tac a w nat i)(*strict*)
  apply(erule_tac
      x="length a + i"
      in allE)
  apply(clarsimp)
  done

lemma notfinishingL_drop: "
  notfinishingL w
  \<Longrightarrow> notfinishingL (drop n w)"
  apply(simp add: notfinishingL_def)
  done

lemma notfinishingL_drop2: "
  notfinishingL (w@v)
  \<Longrightarrow> notfinishingL v"
  apply(simp add: notfinishingL_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="length w+i"
      in allE)
  apply(clarsimp)
  done

lemma notfinishingL_take: "
  notfinishingL (w@v)
  \<Longrightarrow> notfinishingL w"
  apply(simp add: notfinishingL_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      t="w!i"
      and s="(w@v)!i"
      in subst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma notfinishingL_prefix: "
  notfinishingL v
  \<Longrightarrow> prefix w v
  \<Longrightarrow> notfinishingL w"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule notfinishingL_take)
  apply(force)
  done

definition only_l3_nonterminals :: "
  ('a, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "only_l3_nonterminals w \<equiv>
  \<forall>w1 w2 xA.
    w = w1 @ [xA] @ w2
    \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"

lemma only_l3_nonterminals_to_l3_l2_separation_ALT: "
  only_l3_nonterminals ys
  \<Longrightarrow> l3_l2_separation_ALT (ys @ [cons_l2 q b])"
  apply(simp add: only_l3_nonterminals_def l3_l2_separation_ALT_def)
  apply(case_tac ys)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a list q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list q b)(*strict*)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac a list q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac list q1 b q2 x)(*strict*)
  apply(case_tac x)
   apply(rename_tac list q1 b q2 x q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac list q1 b q2 q ba)(*strict*)
   apply(subgoal_tac "\<exists>k<length list. list!k=cons_l2 q ba")
    apply(rename_tac list q1 b q2 q ba)(*strict*)
    prefer 2
    apply (metis in_set_conv_nth)
   apply(rename_tac list q1 b q2 q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac list q1 b q2 q ba k)(*strict*)
   apply(erule_tac
      x="cons_l3 q1 b q2#take k list"
      in allE)
   apply(erule_tac
      x="drop (Suc k) list"
      in allE)
   apply(erule_tac
      x="list!k"
      in allE)
   apply(erule impE)
    apply(rename_tac list q1 b q2 q ba k)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac list q1 b q2 q ba k)(*strict*)
   apply(clarsimp)
   apply(rename_tac list q ba k)(*strict*)
   apply (metis List.Cons_nth_drop_Suc append_take_drop_id_hlp)
  apply(rename_tac list q1 b q2 x q1a ba q2a)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_append1: "
  only_l3_nonterminals ys
  \<Longrightarrow> only_l3_nonterminals (ys @ [cons_l3 q b qx])"
  apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 xA)(*strict*)
  apply(case_tac xA)
   apply(rename_tac w1 w2 xA qa ba)(*strict*)
   prefer 2
   apply(rename_tac w1 w2 xA q1 ba q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 xA qa ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 qa ba)(*strict*)
  apply(rule_tac
      xs="w2"
      in rev_cases)
   apply(rename_tac w1 w2 qa ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 qa ba ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 q b ys)(*strict*)
  apply(erule_tac
      x="w1"
      in allE)
  apply(rename_tac ys)(*strict*)
  apply(force)
  done

lemma l3_l2_separation_ALT_to_only_l3_nonterminals: "
  l3_l2_separation_ALT ys
  \<Longrightarrow> only_l3_nonterminals (butlast ys)"
  apply(simp add: l3_l2_separation_ALT_def only_l3_nonterminals_def)
  apply(rule_tac
      xs="ys"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w1 w2 xA)(*strict*)
  apply(case_tac xA)
   apply(rename_tac y w1 w2 xA q b)(*strict*)
   prefer 2
   apply(rename_tac y w1 w2 xA q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac y w1 w2 xA q b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w1 w2 q b)(*strict*)
  apply(case_tac "w1 @ cons_l2 q b # w2 @ [y]")
   apply(rename_tac y w1 w2 q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y w1 w2 q b a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs="list"
      in rev_cases)
   apply(rename_tac y w1 w2 q b a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac y w1 w2 q b a list ys ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 q b a ys ya)(*strict*)
  apply(case_tac a)
   apply(rename_tac w1 w2 q b a ys ya qa ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 q b a ys ya q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 q b ys ya q1 ba q2)(*strict*)
  apply(case_tac ya)
   apply(rename_tac w1 w2 q b ys ya q1 ba q2 qa bb)(*strict*)
   prefer 2
   apply(rename_tac w1 w2 q b ys ya q1 ba q2 q1a bb q2a)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 q b ys ya q1 ba q2 qa bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 q b ys q1 ba q2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac w1 w2 q b ys q1 ba q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 q b ys q1 ba q2 a list)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_butlast: "
  only_l3_nonterminals ys
  \<Longrightarrow> only_l3_nonterminals (butlast ys)"
  apply(simp add: only_l3_nonterminals_def)
  apply(rule_tac
      xs="ys"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ysa y)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_nth_l2: "
  only_l3_nonterminals w
  \<Longrightarrow> w!i=cons_l2 q A
  \<Longrightarrow> i<length w
  \<Longrightarrow> Q"
  apply(simp add: only_l3_nonterminals_def)
  apply(erule_tac
      x="take i w"
      in allE)
  apply(erule_tac
      x="drop (Suc i) w"
      in allE)
  apply(erule_tac
      x="w!i"
      in allE)
  apply(erule impE)
   apply (metis List.Cons_nth_drop_Suc append_take_drop_id_hlp)
  apply(force)
  done

lemma only_l3_nonterminals_single: "
  only_l3_nonterminals [cons_l3 x y z]"
  apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 xA)(*strict*)
  apply(case_tac w1)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 xA a list)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_append: "
  only_l3_nonterminals w1
  \<Longrightarrow> only_l3_nonterminals w2
  \<Longrightarrow> w=w1@w2
  \<Longrightarrow> only_l3_nonterminals w"
  apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac w1a w2a xA)(*strict*)
  apply(subgoal_tac "prefix w1 w1a \<or> SSX" for SSX)
   apply(rename_tac w1a w2a xA)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac w1a w2a xA)(*strict*)
  apply(erule disjE)
   apply(rename_tac w1a w2a xA)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac w1a w2a xA)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w1 w2a xA c)(*strict*)
  apply(case_tac c)
   apply(rename_tac w1 w2a xA c)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1a. \<forall>w2 xA. w1 = w1a @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1. \<forall> w2a xAa. xA # w2 = w1 @ xAa # w2a \<longrightarrow> (\<exists>q1 A q2. xAa = cons_l3 q1 A q2)"
      in allE)
   apply(clarsimp)
  apply(rename_tac w1 w2a xA c a list)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_drop: "
  only_l3_nonterminals (w@v)
  \<Longrightarrow> only_l3_nonterminals v"
  apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 xA)(*strict*)
  apply(erule_tac
      x="w@w1"
      in allE)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_l2_at_front: "
  only_l3_nonterminals (cons_l2 q A # w)
  \<Longrightarrow> Q"
  apply(simp add: only_l3_nonterminals_def)
  apply(erule_tac
      x="[]"
      in allE)
  apply(force)
  done

lemma only_l3_nonterminals_take: "
  only_l3_nonterminals (w@v)
  \<Longrightarrow> only_l3_nonterminals w"
  apply(simp add: only_l3_nonterminals_def)
  done

lemma only_l3_nonterminals_replace_front: "
  only_l3_nonterminals (cons_l3 q1 A1 q1' # v1)
  \<Longrightarrow> only_l3_nonterminals (cons_l3 q2 A2 q2' # v1)"
  apply (metis CON_def ConsApp append_Cons only_l3_nonterminals_append only_l3_nonterminals_drop only_l3_nonterminals_single only_l3_nonterminals_take)
  done

lemma only_l3_nonterminals_butlast_butn: "
  only_l3_nonterminals (butlast t)
  \<Longrightarrow> only_l3_nonterminals (butlast (butn t n))"
  apply(simp add: butn_def)
  apply(rule_tac
      xs="t"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys nat)(*strict*)
  apply(rule_tac
      xs="take (length ys - nat) ys"
      in rev_cases)
   apply(rename_tac ys nat)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac ys nat)(*strict*)
    apply(clarsimp)
    apply(simp add: only_l3_nonterminals_def)
   apply(rename_tac ys nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys nat ysa y)(*strict*)
  apply(clarsimp)
  apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac ys nat y w1 w2 xA)(*strict*)
  apply(case_tac xA)
   apply(rename_tac ys nat y w1 w2 xA q b)(*strict*)
   prefer 2
   apply(rename_tac ys nat y w1 w2 xA q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys nat y w1 w2 xA q b)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys nat y w1 w2 q b)(*strict*)
  apply(erule_tac
      x="w1"
      in allE)
  apply(erule_tac
      x="w2@[y]@drop(length ys-nat)ys"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="cons_l2 q b"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "ys = w1 @ cons_l2 q b # w2 @ y # drop (length ys - nat) ys")
   apply(rename_tac ys nat y w1 w2 q b)(*strict*)
   apply(force)
  apply(rename_tac ys nat y w1 w2 q b)(*strict*)
  apply(thin_tac "ys \<noteq> w1 @ cons_l2 q b # w2 @ y # drop (length ys - nat) ys")
  apply(rule_tac
      t="w1 @ cons_l2 q b # w2 @ y # drop (length ys - nat) ys"
      and s="(w1 @ cons_l2 q b # w2 @ [y]) @ drop (length ys - nat) ys"
      in ssubst)
   apply(rename_tac ys nat y w1 w2 q b)(*strict*)
   apply(force)
  apply(rename_tac ys nat y w1 w2 q b)(*strict*)
  apply(rule_tac
      t="w1 @ cons_l2 q b # w2 @ [y]"
      and s="take (length ys - nat) ys"
      in ssubst)
   apply(rename_tac ys nat y w1 w2 q b)(*strict*)
   apply(force)
  apply(rename_tac ys nat y w1 w2 q b)(*strict*)
  apply(thin_tac "take (length ys - nat) ys = w1 @ cons_l2 q b # w2 @ [y]")
  apply (metis append_take_drop_id)
  done

definition only_l3_nonterminals_and_l3_adjacency :: "
  ('a, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "only_l3_nonterminals_and_l3_adjacency w \<equiv>
  \<forall>w1 w2 xA xB.
    w = w1 @ [xA, xB] @ w2
    \<longrightarrow> (\<exists>q1 A q2 B q3.
          xA = cons_l3 q1 A q2
          \<and> xB = cons_l3 q2 B q3)"

definition proper_l3_seq :: "
  ('a, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "proper_l3_seq w \<equiv>
  only_l3_nonterminals w
  \<and> only_l3_nonterminals_and_l3_adjacency w"

lemma proper_l3_seq_drop: "
  proper_l3_seq w
  \<Longrightarrow> proper_l3_seq (drop n w)"
  apply(simp add: proper_l3_seq_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: only_l3_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(erule_tac
      x="take n w@w1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="w2"
      in allE)
   apply(erule_tac
      x="xA"
      in allE)
   apply(erule impE)
    apply(rename_tac w1 w2 xA)(*strict*)
    apply (metis append_take_drop_id)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(force)
  apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 xA xB)(*strict*)
  apply(erule_tac
      x="take n w@w1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule_tac
      x="xA"
      in allE)
  apply(erule_tac
      x="xB"
      in allE)
  apply(erule impE)
   apply(rename_tac w1 w2 xA xB)(*strict*)
   apply (metis append_take_drop_id)
  apply(rename_tac w1 w2 xA xB)(*strict*)
  apply(force)
  done

lemma proper_l3_seq_no_l2: "
  proper_l3_seq w
  \<Longrightarrow> w=w1@[cons_l2 q A]@w2
  \<Longrightarrow> Q"
  apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
  apply(force)
  done

lemma proper_l3_seq_drop_tail: "
  proper_l3_seq (w@v)
  \<Longrightarrow> proper_l3_seq w"
  apply(simp add: proper_l3_seq_def)
  apply(rule conjI)
   apply(simp add: only_l3_nonterminals_def)
  apply(clarsimp)
  apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
  done

lemma proper_l3_seq_l3_adjacent: "
  proper_l3_seq w
  \<Longrightarrow> w=w1@[cons_l3 q1 A q2,cons_l3 q2' B q3]@w2
  \<Longrightarrow> q2=q2'"
  apply(simp add: proper_l3_seq_def only_l3_nonterminals_and_l3_adjacency_def)
  apply(force)
  done

lemma proper_l3_seq_compose2: "
  proper_l3_seq (w1@[cons_l3 q1 A q])
  \<Longrightarrow> proper_l3_seq ([cons_l3 q B q2]@w2)
  \<Longrightarrow> proper_l3_seq (w1@[cons_l3 q1 A q,cons_l3 q B q2]@w2)"
  apply(simp add: proper_l3_seq_def)
  apply(rule context_conjI)
   apply(simp add: only_l3_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac w1a w2a xA)(*strict*)
   apply(case_tac xA)
    apply(rename_tac w1a w2a xA qa b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1a w2a qa b)(*strict*)
    apply(subgoal_tac "prefix w1 w1a \<or> prefix w1a w1")
     apply(rename_tac w1a w2a qa b)(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac w1a w2a qa b)(*strict*)
    apply(erule disjE)
     apply(rename_tac w1a w2a qa b)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac w2a qa b c)(*strict*)
     apply(case_tac c)
      apply(rename_tac w2a qa b c)(*strict*)
      apply(clarsimp)
     apply(rename_tac w2a qa b c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac w2a qa b list)(*strict*)
     apply(case_tac list)
      apply(rename_tac w2a qa b list)(*strict*)
      apply(clarsimp)
     apply(rename_tac w2a qa b list a lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac w2 qa b lista)(*strict*)
     apply(erule_tac
      x="cons_l3 q B q2 # lista"
      and P="\<lambda>w1. \<forall>w2a xA. cons_l3 q B q2 # lista @ cons_l2 qa b # w2 = w1 @ xA # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
     apply(rename_tac w2 qa b lista)(*strict*)
     apply(force)
    apply(rename_tac w1a w2a qa b)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac w1 w2a qa b c)(*strict*)
    apply(case_tac c)
     apply(rename_tac w1 w2a qa b c)(*strict*)
     apply(clarsimp)
    apply(rename_tac w1 w2a qa b c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 qa b list)(*strict*)
    apply(erule_tac
      x="w1"
      and P="\<lambda>w1. \<forall>w2a xA. cons_l3 q B q2 # w2 = w1 @ xA # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
    apply(force)
   apply(rename_tac w1a w2a xA q1a b q2a)(*strict*)
   apply(clarsimp)
  apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
  apply(clarsimp)
  apply(rename_tac w1a w2a xA xB)(*strict*)
  apply(case_tac xA)
   apply(rename_tac w1a w2a xA xB qa b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1a w2a xB qa b)(*strict*)
   apply(simp add: only_l3_nonterminals_def)
   apply(erule_tac
      x="w1a"
      and P="\<lambda>w1. \<forall>w2 xA. w1a @ cons_l2 qa b # xB # w2a = w1 @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(rename_tac w1a w2a xB qa b)(*strict*)
   apply(force)
  apply(rename_tac w1a w2a xA xB q1a b q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1a w2a xB q1a b q2a)(*strict*)
  apply(case_tac xB)
   apply(rename_tac w1a w2a xB q1a b q2a qa ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1a w2a q1a b q2a qa ba)(*strict*)
   apply(simp add: only_l3_nonterminals_def)
   apply(erule_tac
      x="w1a @ [cons_l3 q1a b q2a]"
      and P="\<lambda>w1. \<forall>w2 xA. w1a @ cons_l3 q1a b q2a # cons_l2 qa ba # w2a = w1 @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(rename_tac w1a w2a q1a b q2a qa ba)(*strict*)
   apply(force)
  apply(rename_tac w1a w2a xB q1a b q2a q1aa ba q2aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1a w2a q1a b q2a q1aa ba q2aa)(*strict*)
  apply(subgoal_tac "prefix w1 w1a \<or> prefix w1a w1")
   apply(rename_tac w1a w2a q1a b q2a q1aa ba q2aa)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac w1a w2a q1a b q2a q1aa ba q2aa)(*strict*)
  apply(erule disjE)
   apply(rename_tac w1a w2a q1a b q2a q1aa ba q2aa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac w2a q1a b q2a q1aa ba q2aa c)(*strict*)
   apply(case_tac c)
    apply(rename_tac w2a q1a b q2a q1aa ba q2aa c)(*strict*)
    apply(clarsimp)
   apply(rename_tac w2a q1a b q2a q1aa ba q2aa c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2a q1a b q2a q1aa ba q2aa list)(*strict*)
   apply(case_tac list)
    apply(rename_tac w2a q1a b q2a q1aa ba q2aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w2 q1a ba q2a)(*strict*)
    apply(erule_tac
      x="[]"
      and P="\<lambda>X. \<forall>w2a xA xB. cons_l3 q B q2 # cons_l3 q1a ba q2a # w2 = X @ xA # xB # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2 \<and> (\<exists>B q3. xB = cons_l3 q2 B q3))"
      in allE)
    apply(rename_tac w2 q1a ba q2a)(*strict*)
    apply(force)
   apply(rename_tac w2a q1a b q2a q1aa ba q2aa list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 q1a b q2a q1aa ba q2aa lista)(*strict*)
   apply(erule_tac
      x="cons_l3 q B q2 # lista"
      and P="\<lambda>w1. \<forall>w2a xA xB. cons_l3 q B q2 # lista @ cons_l3 q1a b q2a # cons_l3 q1aa ba q2aa # w2 = w1 @ xA # xB # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2 \<and> (\<exists>B q3. xB = cons_l3 q2 B q3))"
      in allE)
   apply(rename_tac w2 q1a b q2a q1aa ba q2aa lista)(*strict*)
   apply(force)
  apply(rename_tac w1a w2a q1a b q2a q1aa ba q2aa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa c)(*strict*)
  apply(case_tac c)
   apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa list)(*strict*)
  apply(case_tac list)
   apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 q1a b q2a)(*strict*)
   apply(erule_tac
      x="[]"
      and P="\<lambda>X. \<forall>w2a xA xB. cons_l3 q B q2 # w2 = X @ xA # xB # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2 \<and> (\<exists>B q3. xB = cons_l3 q2 B q3))"
      in allE)
   apply(rename_tac w1 q1a b q2a)(*strict*)
   apply(force)
  apply(rename_tac w1 w2a q1a b q2a q1aa ba q2aa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 q1a b q2a q1aa ba q2aa lista)(*strict*)
  apply(erule_tac
      x="cons_l3 q B q2 # lista"
      and P="\<lambda>w1. \<forall>w2a xA xB. cons_l3 q B q2 # w2 = w1 @ xA # xB # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2 \<and> (\<exists>B q3. xB = cons_l3 q2 B q3))"
      in allE)
  apply(rename_tac w1 q1a b q2a q1aa ba q2aa lista)(*strict*)
  apply(force)
  done

lemma proper_l3_seq_drop_front: "
  proper_l3_seq (w@v)
  \<Longrightarrow> proper_l3_seq v"
  apply(simp add: proper_l3_seq_def)
  apply(rule conjI)
   apply(simp add: only_l3_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(case_tac xA)
    apply(rename_tac w1 w2 xA q b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 w2 q b)(*strict*)
    apply(erule_tac
      x="w@w1"
      in allE)
    apply(force)
   apply(rename_tac w1 w2 xA q1 b q2)(*strict*)
   apply(clarsimp)
  apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 xA xB)(*strict*)
  apply(erule_tac
      x="w@w1"
      in allE)
  apply(clarsimp)
  done

lemma proper_l3_seq_take: "
  proper_l3_seq w
  \<Longrightarrow> proper_l3_seq (take n w)"
  apply(rule_tac
      v="drop n w"
      in proper_l3_seq_drop_tail)
  apply (metis append_take_drop_id)
  done

definition last_back_state :: "
  ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option"
  where
    "last_back_state w \<equiv>
  case w of
  [] \<Rightarrow> None
  | a # w' \<Rightarrow> (
    case last w of
      cons_l2 q A \<Rightarrow> Some q
      | cons_l3 q1 A q2 \<Rightarrow> Some q2)"

lemma last_back_state_not_empty: "
  last_back_state w = Some q
  \<Longrightarrow> \<exists>w' x. w=w'@[x] \<and> last_back_state [x]=Some q"
  apply(simp add: last_back_state_def)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac "w'@[a']")
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a' a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "list=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' a' a list)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' a' a list)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w' a' a list qa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' a list q1 b q2)(*strict*)
  apply(clarsimp)
  done

lemma last_back_state_empty: "
  last_back_state w = None
  \<Longrightarrow> w=[]"
  apply(simp add: last_back_state_def)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac "w'@[a']")
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a' a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "list=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' a' a list)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' a' a list)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
    apply(rename_tac a q b)(*strict*)
    apply(clarsimp)
   apply(rename_tac a q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a'a)(*strict*)
  apply(case_tac a'a)
   apply(rename_tac a'a q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a'a q1 b q2)(*strict*)
  apply(clarsimp)
  done

lemma last_back_state_l3: "
  w=w'@[cons_l3 q1 A q2]
  \<Longrightarrow> last_back_state w = Some q2"
  apply(simp add: last_back_state_def)
  apply(clarsimp)
  apply(case_tac "w'@[cons_l3 q1 A q2]")
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "list=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac a list)(*strict*)
  apply(erule disjE)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma proper_l3_seq_inter_1: "
  proper_l3_seq (w @ cons_l3 q1 b q2 # w')
  \<Longrightarrow> last_back_state w = None \<or> last_back_state w = Some q1"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: last_back_state_def)
  apply(rule disjI2)
  apply(simp add: proper_l3_seq_def only_l3_nonterminals_and_l3_adjacency_def)
  apply(clarsimp)
  apply(rename_tac w'a a')(*strict*)
  apply(erule_tac
      x="w'a"
      in allE)
  apply(clarsimp)
  apply(rename_tac w'a q1a A)(*strict*)
  apply(rule last_back_state_l3)
  apply(force)
  done

definition proper_l3_l2_seq :: "
  ('a, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "proper_l3_l2_seq w \<equiv>
  \<exists>w' q A.
    w = w' @ [cons_l2 q A]
    \<and> proper_l3_seq w'
    \<and> (last_back_state w' = None \<or> last_back_state w' = Some q)"

lemma l2_in_proper_l3_l2_seq_at_end: "
  proper_l3_l2_seq (w @ [cons_l2 q1 A1] @ v)
  \<Longrightarrow> v=[]"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' q A)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' q A)(*strict*)
   apply(subgoal_tac "w'=[]")
    apply(rename_tac w' q A)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A)(*strict*)
    apply(case_tac w)
     apply(rename_tac q A)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' q A)(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac w' q A)(*strict*)
  apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSw SSq)
   apply(rename_tac w' q A)(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac w' q A)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A w'a x)(*strict*)
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac q A w'a x)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac q A w'a x)(*strict*)
  apply(erule disjE)
   apply(rename_tac q A w'a x)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A w'a x)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w'a x w')(*strict*)
  apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
  apply(clarsimp)
  apply(erule_tac
      x="w"
      in allE)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule_tac
      x="cons_l2 q1 A1"
      in allE)
  apply(clarsimp)
  done

lemma proper_l3_l2_seq_replace_first: "
  proper_l3_l2_seq (cons_l3 q1 A1 q # w)
  \<Longrightarrow> proper_l3_l2_seq (cons_l3 q2 A2 q # w)"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' qa A)(*strict*)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac w' qa A)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' qa A)(*strict*)
  apply(erule_tac
      P="w = []"
      in disjE)
   apply(rename_tac w' qa A)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' qa A)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a)(*strict*)
  apply(erule disjE)
   apply(rename_tac qa w'a)(*strict*)
   apply(subgoal_tac "cons_l3 q1 A1 q # w'a = []")
    apply(rename_tac qa w'a)(*strict*)
    apply(force)
   apply(rename_tac qa w'a)(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac qa w'a)(*strict*)
  apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSw SSq)
   apply(rename_tac qa w'a)(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac qa w'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a w' x)(*strict*)
  apply(subgoal_tac "w'a=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac qa w'a w' x)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac qa w'a w' x)(*strict*)
  apply(erule disjE)
   apply(rename_tac qa w'a w' x)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa)(*strict*)
   apply(rule conjI)
    apply(rename_tac qa)(*strict*)
    apply(simp add: proper_l3_seq_def)
    apply(rule conjI)
     apply(rename_tac qa)(*strict*)
     apply(simp add: only_l3_nonterminals_def)
     apply(clarsimp)
     apply(rename_tac qa w1 w2 xA)(*strict*)
     apply(case_tac w1)
      apply(rename_tac qa w1 w2 xA)(*strict*)
      apply(clarsimp)
     apply(rename_tac qa w1 w2 xA a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac qa)(*strict*)
    apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
   apply(rename_tac qa)(*strict*)
   apply(rule disjI2)
   apply(simp add: last_back_state_def)
  apply(rename_tac qa w'a w' x)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa x w'b)(*strict*)
  apply(rule conjI)
   apply(rename_tac qa x w'b)(*strict*)
   apply(simp add: proper_l3_seq_def)
   apply(rule conjI)
    apply(rename_tac qa x w'b)(*strict*)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac qa x w'b w1 w2 xA)(*strict*)
    apply(case_tac w1)
     apply(rename_tac qa x w'b w1 w2 xA)(*strict*)
     apply(clarsimp)
    apply(rename_tac qa x w'b w1 w2 xA a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac qa x w'b w2 xA list)(*strict*)
    apply(erule_tac
      x="cons_l3 q1 A1 q # list"
      in allE)
    apply(clarsimp)
   apply(rename_tac qa x w'b)(*strict*)
   apply(clarsimp)
   apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
   apply(clarsimp)
   apply(rename_tac qa x w'b w1 w2 xA xB)(*strict*)
   apply(case_tac w1)
    apply(rename_tac qa x w'b w1 w2 xA xB)(*strict*)
    apply(clarsimp)
    apply(rename_tac qa x w'b w2 xB)(*strict*)
    apply(erule_tac
      x="[]"
      in allE)
    apply(clarsimp)
   apply(rename_tac qa x w'b w1 w2 xA xB a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa x w'b w2 xA xB list)(*strict*)
   apply(erule_tac
      x="cons_l3 q1 A1 q # list"
      in allE)
   apply(clarsimp)
  apply(rename_tac qa x w'b)(*strict*)
  apply(rule disjI2)
  apply(simp add: last_back_state_def)
  done

lemma proper_l3_l2_seq_enlarge: "
  proper_l3_l2_seq (cons_l3 q1 A q2 # w)
  \<Longrightarrow> proper_l3_l2_seq (cons_l3 q0 B q1 # cons_l3 q1 A q2 # w)"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' q Aa)(*strict*)
  apply(rule conjI)
   apply(rename_tac w' q Aa)(*strict*)
   apply(simp add: proper_l3_seq_def)
   apply(rule conjI)
    apply(rename_tac w' q Aa)(*strict*)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac w' q Aa w1 w2 xA)(*strict*)
    apply(case_tac w1)
     apply(rename_tac w' q Aa w1 w2 xA)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' q Aa w1 w2 xA a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' q Aa)(*strict*)
   apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
   apply(clarsimp)
   apply(rename_tac w' q Aa w1 w2 xA xB)(*strict*)
   apply(case_tac w1)
    apply(rename_tac w' q Aa w1 w2 xA xB)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' q Aa w1 w2 xA xB a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q Aa)(*strict*)
  apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac w' q Aa)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' q Aa)(*strict*)
  apply(erule_tac
      P="last_back_state w' = None"
      in disjE)
   apply(rename_tac w' q Aa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "w'=[]")
    apply(rename_tac w' q Aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' q Aa)(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac w' q Aa)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' q Aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q Aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac q Aa w'a a')(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac q Aa w'a a')(*strict*)
   apply(clarsimp)
  apply(rename_tac q Aa w'a a')(*strict*)
  apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSw SSq)
   apply(rename_tac q Aa w'a a')(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac q Aa w'a a')(*strict*)
  apply(clarsimp)
  apply(thin_tac "last_back_state (w'a @ [a']) = Some q")
  apply(case_tac "last_back_state (cons_l3 q0 B q1 # w'a @ [a'])")
   apply(rename_tac q Aa w'a a')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "cons_l3 q0 B q1 # w'a @ [a'] = []")
    apply(rename_tac q Aa w'a a')(*strict*)
    apply(force)
   apply(rename_tac q Aa w'a a')(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac q Aa w'a a' a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w' x. (cons_l3 q0 B q1 # w'a @ [a']) = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
   apply(rename_tac q Aa w'a a' a)(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac q Aa w'a a' a)(*strict*)
  apply(clarsimp)
  done

lemma proper_l3_l2_seq_nol2: "
  proper_l3_l2_seq (w@cons_l2  q A#w'@[a])
  \<Longrightarrow> Q"
  apply(simp add: proper_l3_l2_seq_def proper_l3_seq_def only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac qa)(*strict*)
  apply(erule_tac
      x="w"
      in allE)
  apply(force)
  done

lemma proper_l3_l2_seq_nol3: "
  proper_l3_l2_seq (w@[cons_l3 q A q'])
  \<Longrightarrow> Q"
  apply(simp add: proper_l3_l2_seq_def proper_l3_seq_def only_l3_nonterminals_def)
  done

lemma proper_l3_l2_seq_drop: "
  proper_l3_l2_seq w
  \<Longrightarrow> n<length w
  \<Longrightarrow> proper_l3_l2_seq (drop n w)"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' q)(*strict*)
  apply(rule conjI)
   apply(rename_tac w' q)(*strict*)
   apply(rule proper_l3_seq_drop)
   apply(force)
  apply(rename_tac w' q)(*strict*)
  apply(subgoal_tac "drop n w'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac w' q)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' q)(*strict*)
  apply(erule_tac
      P="last_back_state w' = None"
      in disjE)
   apply(rename_tac w' q)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
    apply(rename_tac w' q)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' q)(*strict*)
   apply(erule_tac
      P="w' = []"
      in disjE)
    apply(rename_tac w' q)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' q)(*strict*)
   apply(clarsimp)
   apply(rename_tac q w'a a')(*strict*)
   apply(subgoal_tac "w'a@[a']=[]")
    apply(rename_tac q w'a a')(*strict*)
    apply(force)
   apply(rename_tac q w'a a')(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac w' q)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w' x. SSw = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSw SSq)
   apply(rename_tac w' q)(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac w' q)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w'a x)(*strict*)
  apply(erule disjE)
   apply(rename_tac q w'a x)(*strict*)
   apply(clarsimp)
   apply(simp add: last_back_state_def)
  apply(rename_tac q w'a x)(*strict*)
  apply(clarsimp)
  apply(rename_tac q w'a x w' a')(*strict*)
  apply(case_tac "n-length w'a")
   apply(rename_tac q w'a x w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac q w'a a')(*strict*)
   apply(case_tac "last_back_state (drop n w'a @ [a'])")
    apply(rename_tac q w'a a')(*strict*)
    apply(subgoal_tac "(drop n w'a @ [a'])=[]")
     apply(rename_tac q w'a a')(*strict*)
     apply(force)
    apply(rename_tac q w'a a')(*strict*)
    apply(rule last_back_state_empty)
    apply(force)
   apply(rename_tac q w'a a' a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>w' x. (drop n w'a @ [a']) = w' @ [x] \<and> last_back_state [x] = Some SSq" for SSq)
    apply(rename_tac q w'a a' a)(*strict*)
    prefer 2
    apply(rule last_back_state_not_empty)
    apply(force)
   apply(rename_tac q w'a a' a)(*strict*)
   apply(clarsimp)
  apply(rename_tac q w'a x w' a' nat)(*strict*)
  apply(clarsimp)
  done

lemma proper_l3_l2_seq_drop_prime: "
  v\<noteq>[]
  \<Longrightarrow> proper_l3_l2_seq (w@v)
  \<Longrightarrow> proper_l3_l2_seq v"
  apply(rule_tac
      t="v"
      and s="drop(length w)(w@v)"
      in ssubst)
   apply(force)
  apply(rule proper_l3_l2_seq_drop)
   apply(force)
  apply(force)
  done

lemma proper_l3_seq_drop_tail_X: "
  proper_l3_l2_seq (w@cons_l3  q A q'#wx)
  \<Longrightarrow> proper_l3_l2_seq (w@[cons_l2 q A])"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' qa Aa)(*strict*)
  apply(rule conjI)
   apply(rename_tac w' qa Aa)(*strict*)
   apply(simp add: proper_l3_seq_def)
   apply(rule conjI)
    apply(rename_tac w' qa Aa)(*strict*)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac w' qa Aa w1 w2 xA)(*strict*)
    apply(subgoal_tac "wx=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac w' qa Aa w1 w2 xA)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac w' qa Aa w1 w2 xA)(*strict*)
    apply(erule_tac
      P="wx = []"
      in disjE)
     apply(rename_tac w' qa Aa w1 w2 xA)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' qa Aa w1 w2 xA)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' qa Aa)(*strict*)
   apply(simp add: only_l3_nonterminals_and_l3_adjacency_def)
   apply(clarsimp)
   apply(rename_tac w' qa Aa w1 w2 xA xB)(*strict*)
   apply(subgoal_tac "wx=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' qa Aa w1 w2 xA xB)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' qa Aa w1 w2 xA xB)(*strict*)
   apply(erule_tac
      P="wx = []"
      in disjE)
    apply(rename_tac w' qa Aa w1 w2 xA xB)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' qa Aa w1 w2 xA xB)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' qa Aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' qa Aa)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' qa Aa)(*strict*)
  apply(erule_tac
      P="w = []"
      in disjE)
   apply(rename_tac w' qa Aa)(*strict*)
   apply(clarsimp)
   apply(simp add: last_back_state_def)
  apply(rename_tac w' qa Aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' qa Aa w'a a')(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   apply(force)
  apply(rename_tac w' qa Aa w'a a')(*strict*)
  apply(erule disjE)
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' qa Aa w'a a')(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   apply(erule disjE)
    apply(rename_tac w' qa Aa w'a a')(*strict*)
    apply(clarsimp)
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   apply(clarsimp)
   apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
   apply(subgoal_tac "w'b@[a'a] = []")
    apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
    apply(force)
   apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac w' qa Aa w'a a')(*strict*)
  apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' qa Aa w'a a')(*strict*)
  apply(erule disjE)
   apply(rename_tac w' qa Aa w'a a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' qa Aa w'a a')(*strict*)
  apply(clarsimp)
  apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
  apply(case_tac "last_back_state (w'a @ [a'])")
   apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "w'a@[a'] = []")
    apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
    apply(force)
   apply(rename_tac qa Aa w'a a' w'b a'a)(*strict*)
   apply(rule last_back_state_empty)
   apply(force)
  apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
   prefer 2
   apply(rule last_back_state_not_empty)
   apply(force)
  apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
   prefer 2
   apply(rule_tac
      q="a"
      in last_back_state_not_empty)
   apply(force)
  apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "wx=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
  apply(erule disjE)
   apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
   apply(clarsimp)
  apply(rename_tac qa Aa w'a a' w'b a'a a)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a a' w'b a'a a w')(*strict*)
  apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac qa w'a a' w'b a'a a w')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac qa w'a a' w'b a'a a w')(*strict*)
  apply(erule disjE)
   apply(rename_tac qa w'a a' w'b a'a a w')(*strict*)
   apply(clarsimp)
   apply(rename_tac qa w'a a' a)(*strict*)
   apply(case_tac a')
    apply(rename_tac qa w'a a' a qaa b)(*strict*)
    apply(simp add: only_l3_nonterminals_def proper_l3_seq_def)
    apply(force)
   apply(rename_tac qa w'a a' a q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa w'a a q1 b q2)(*strict*)
   apply(subgoal_tac "q2=q")
    apply(rename_tac qa w'a a q1 b q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac qa w'a a q1 b)(*strict*)
    apply(simp add: last_back_state_def)
   apply(rename_tac qa w'a a q1 b q2)(*strict*)
   apply(simp add: only_l3_nonterminals_and_l3_adjacency_def proper_l3_seq_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac qa w'a a' w'b a'a a w')(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a a' a'a a w'c)(*strict*)
  apply(case_tac a')
   apply(rename_tac qa w'a a' a'a a w'c qaa b)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa w'a a'a a w'c qaa b)(*strict*)
   apply(simp add: only_l3_nonterminals_def proper_l3_seq_def)
   apply(force)
  apply(rename_tac qa w'a a' a'a a w'c q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a a'a a w'c q1 b q2)(*strict*)
  apply(case_tac a'a)
   apply(rename_tac qa w'a a'a a w'c q1 b q2 qaa ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa w'a a w'c q1 b q2 qaa ba)(*strict*)
   apply(simp add: only_l3_nonterminals_def proper_l3_seq_def)
   apply(clarsimp)
   apply(erule_tac
      x="w'a @ cons_l3 q1 b q2 # cons_l3 q A q' # w'c"
      in allE)
   apply(force)
  apply(rename_tac qa w'a a'a a w'c q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa w'a a w'c q1 b q2 q1a ba q2a)(*strict*)
  apply(subgoal_tac "q2=q")
   apply(rename_tac qa w'a a w'c q1 b q2 q1a ba q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa w'a a w'c q1 b q1a ba q2a)(*strict*)
   apply(simp add: last_back_state_def)
  apply(rename_tac qa w'a a w'c q1 b q2 q1a ba q2a)(*strict*)
  apply(simp add: only_l3_nonterminals_and_l3_adjacency_def proper_l3_seq_def)
  apply(force)
  done

lemma proper_l3_l2_seq_proper_l3_seq_slice: "
  proper_l3_l2_seq (w1@w2@w3@[a])
  \<Longrightarrow> proper_l3_seq w2"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac q)(*strict*)
  apply(subgoal_tac "proper_l3_seq (w1@w2)")
   apply(rename_tac q)(*strict*)
   apply(rule proper_l3_seq_drop_front)
   apply(force)
  apply(rename_tac q)(*strict*)
  apply(rule_tac
      v="w3"
      in proper_l3_seq_drop_tail)
  apply(force)
  done

definition fill :: "
  ('q, 'b) DT_l2_l3_nonterminals
  \<Rightarrow> 'q
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals"
  where
    "fill X q \<equiv>
   (case X of cons_l2 q1 A1
  \<Rightarrow> cons_l3 q1 A1 q
  | cons_l3 q1 A1 q1'
  \<Rightarrow> cons_l3 q1 A1 q1')"

definition fillL :: "
  ('q, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals list"
  where
    "fillL w q \<equiv>
   (appL w (\<lambda>x. fill x q))"

definition concretization :: "
  ('q, 't, 's) epda
  \<Rightarrow> (('q, 't, 's) epda_step_label, (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label) DT_two_elements list
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) cfg_step_label list
  \<Rightarrow> bool"
  where
    "concretization G \<pi>1 \<pi>2 \<equiv>
   (length \<pi>1 = length \<pi>2
  \<and> (\<forall>i < length \<pi>1. (case \<pi>1 ! i of teB b
  \<Rightarrow> b = \<pi>2 ! i
  | teA A
  \<Rightarrow> A \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2 ! i)) ))"

definition fillB :: "
  (('q, 'b) DT_l2_l3_nonterminals, 't) DT_two_elements
  \<Rightarrow> 'q
  \<Rightarrow> (('q, 'b) DT_l2_l3_nonterminals, 't) DT_two_elements"
  where
    "fillB X q \<equiv>
   (case X of teB b
  \<Rightarrow> X
  | teA A
  \<Rightarrow> teA (fill A q))"

definition fillBOpt :: "
  (('q, 'b) DT_l2_l3_nonterminals, 't) DT_two_elements
  \<Rightarrow> 'q option
  \<Rightarrow> (('q, 'b) DT_l2_l3_nonterminals, 't) DT_two_elements"
  where
    "fillBOpt X q \<equiv>
   (case q of None
  \<Rightarrow> X
  | Some q
  \<Rightarrow> fillB X q)"

definition fillOptL :: "
  ('q, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals list"
  where
    "fillOptL w q \<equiv>
   (case q of None
  \<Rightarrow> w
  | Some q
  \<Rightarrow> fillL w q)"

definition fillWithContext :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option
  \<Rightarrow> 'q option
  \<Rightarrow> 'q option
  \<Rightarrow> (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements list"
  where
    "fillWithContext X1 w2 w3 q1 q2 q3 \<equiv>
  [fillBOpt X1 q1] @ (liftA (fillOptL w2 q2)) @ (liftA (fillOptL w3 q3))"

definition ValidFillO :: "
  ('q, 's) DT_l2_l3_nonterminals
  \<Rightarrow> 'q option
  \<Rightarrow> bool"
  where
    "ValidFillO A q \<equiv>
   (case A of cons_l2 q A
  \<Rightarrow> True
  | cons_l3 q1 A q2
  \<Rightarrow> q = None)"

definition ValidFillBO :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements
  \<Rightarrow> 'q option
  \<Rightarrow> bool"
  where
    "ValidFillBO X q \<equiv>
   (case X of teB b
  \<Rightarrow> q = None
  | teA A
  \<Rightarrow> ValidFillO A q)"

definition ValidFillOL :: "
  ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option
  \<Rightarrow> bool"
  where
    "ValidFillOL w q \<equiv>
   (proper_l3_seq w \<longrightarrow> q = None)"

definition event_stack_separation_and_proper_l3_l2_seq :: "
  (('a, 'b) DT_l2_l3_nonterminals, 't) DT_two_elements list
  \<Rightarrow> bool"
  where
    "event_stack_separation_and_proper_l3_l2_seq w \<equiv>
  \<exists>w1 w2.
    w = liftB w1 @ liftA w2
    \<and> proper_l3_l2_seq w2"

definition ValidContext :: "
  (('q, 's) DT_l2_l3_nonterminals, 't) DT_two_elements
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option
  \<Rightarrow> 'q option
  \<Rightarrow> 'q option
  \<Rightarrow> bool"
  where
    "ValidContext X1 w2 w3 w4 q1 q2 q3 \<equiv>
   (\<exists>c. (event_stack_separation_and_proper_l3_l2_seq ((fillWithContext X1 w2 w3 q1 q2 q3) @ (liftA (w4 @ c))))
  \<and> (w4 \<noteq> [] \<longrightarrow> c = [])
  \<and> (ValidFillBO X1 q1)
  \<and> (ValidFillOL w2 q2)
  \<and> (ValidFillOL w3 q3))"

definition fillOpt :: "
  ('q, 'b) DT_l2_l3_nonterminals
  \<Rightarrow> 'q option
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals"
  where
    "fillOpt X q \<equiv>
   (case q of None
  \<Rightarrow> X
  | Some q
  \<Rightarrow> fill X q)"

definition cropTol3l2_single :: "
  ('q, 'b) DT_l2_l3_nonterminals
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals"
  where
    "cropTol3l2_single w \<equiv>
   (case w of cons_l2 q A
  \<Rightarrow> cons_l2 q A
  | cons_l3 q1 A q2
  \<Rightarrow> cons_l2 q1 A)"

definition cropTol3l2 :: "
  ('q, 'b) DT_l2_l3_nonterminals list
  \<Rightarrow> ('q, 'b) DT_l2_l3_nonterminals list"
  where
    "cropTol3l2 w \<equiv>
   (if w = []
  then w
  else butlast w @ [cropTol3l2_single (last w)])"

lemma cropTol3l2_drop_butn: "
    drop (length w) (cropTol3l2 (butn (w@v) n)) = cropTol3l2 (butn v n)"
  apply(simp add: cropTol3l2_def)
  apply(rule conjI)
   apply(simp add: butn_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: butn_def)
  apply(clarsimp)
  apply(subgoal_tac "butn v n=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "butn (w@v) n=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a' w'a a'a)(*strict*)
  apply(subgoal_tac "w'a@[a'a] = w@w'@[a']")
   apply(rename_tac w' a' w'a a'a)(*strict*)
   prefer 2
   apply(simp add: butn_def)
   apply(clarsimp)
   apply(rename_tac w' a'a)(*strict*)
   apply(case_tac "length v - n")
    apply(rename_tac w' a'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a'a nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' w'a a'a)(*strict*)
  apply(clarsimp)
  done

lemma cropTol3l2_makes_shorter: "
      length (cropTol3l2 w) \<le> length w"
  apply(simp add: cropTol3l2_def)
  done

lemma cropTol3l2_of_tail_of_proper_l3_l2_seq_ident: "
  proper_l3_l2_seq (w@v)
  \<Longrightarrow> cropTol3l2 v=v"
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: cropTol3l2_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(simp add: cropTol3l2_single_def)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(simp add: proper_l3_l2_seq_def)
  done

lemma append_last_back_state_for_proper_l3_seq: "
  last_back_state w = Some a
  \<Longrightarrow> proper_l3_seq w
  \<Longrightarrow> fillL (cropTol3l2 w) a = w"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: last_back_state_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q b)(*strict*)
   apply(simp add: proper_l3_seq_def only_l3_nonterminals_def)
   apply(force)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def fillL_def appL_def fill_def)
  apply(subgoal_tac "last_back_state (w' @ [cons_l3 q1 b q2]) = Some SSq'" for SSq')
   apply(rename_tac w' q1 b q2)(*strict*)
   prefer 2
   apply(rule last_back_state_l3)
   apply(force)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(clarsimp)
  done

lemma cropTol3l2_ID: "
  w \<noteq> []
  \<Longrightarrow> F1 = hd (cropTol3l2 (F1 # w))"
  apply(simp add: cropTol3l2_def)
  done

lemma cropTol3l2_single_equal_from_cropTol3l2_equal: "
  hd(cropTol3l2 (a1#w1)) = hd(cropTol3l2 (a2#w2))
  \<Longrightarrow> cropTol3l2_single a1 = cropTol3l2_single a2"
  apply(simp add: cropTol3l2_def)
  apply(rule_tac
      xs="w1"
      in rev_cases)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(case_tac a1)
    apply(rename_tac q b)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      xs="w2"
      in rev_cases)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(case_tac a2)
    apply(rename_tac q b)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y ysa ya)(*strict*)
  apply(clarsimp)
  done

lemma cropTol3l2_length: "
  length (cropTol3l2 w) = length w"
  apply(simp add: cropTol3l2_def)
  done

lemma cropTol3l2_rest_is_junk: "
  n1\<le>length l1a
  \<Longrightarrow> l1a @ l2x = cropTol3l2 (take n1 l1a)
  \<Longrightarrow> n1=length l1a \<and> l2x=[]"
  apply(simp add: cropTol3l2_def)
  apply(case_tac "n1=0 \<or> l1a=[]")
   apply(clarsimp)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      xs="take n1 l1a"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply (metis Suc_length append_eq_conv_conj append_self_conv gr0_conv_Suc hlpXX2 le_SucE le_trans length_shorter_append less_not_refl nat.inject not_Cons_self take_all take_length take_take1)
  done

definition drop_and_crop :: "
  ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> nat
  \<Rightarrow> ('q, 's) DT_l2_l3_nonterminals list"
  where
    "drop_and_crop w n \<equiv>
   (cropTol3l2 (butn w n))"

lemma drop_and_crop_length: "
  length (drop_and_crop w x) = length w - x"
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  apply(clarsimp)
  apply(force)
  done

lemma cropTol3l2_drop_butn_drop_and_crop: "
  drop (length w) (drop_and_crop (w@v) k) = drop_and_crop v k"
  apply(simp add: drop_and_crop_def)
  apply(rule cropTol3l2_drop_butn)
  done

lemma drop_and_crop_makes_shorter: "
  length (drop_and_crop w n) \<le> length w"
  apply(simp add: drop_and_crop_def)
  apply(simp add: cropTol3l2_def butn_def)
  done

lemma fillL_exists: "
  n>0
  \<Longrightarrow> proper_l3_l2_seq w
  \<Longrightarrow> \<exists>q. fillL (drop_and_crop w n) q = butn w n"
  apply(subgoal_tac "\<exists>w1 w2. w= (butn w n)@(takeB n w)")
   prefer 2
   apply(simp add: butn_def takeB_def)
  apply(clarsimp)
  apply(rule_tac
      P="\<lambda>X. \<exists>q. fillL (drop_and_crop X n) q = butn w n"
      and s="butn w n @ takeB n w"
      in ssubst)
   apply(force)
  apply(simp add: drop_and_crop_def)
  apply(rule_tac
      t="butn (butn w n @ takeB n w) n"
      and s="butn w n"
      in ssubst)
   apply(simp add: butn_def takeB_def)
  apply(subgoal_tac "butn w n=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: fillL_def cropTol3l2_def appL_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q b)(*strict*)
   apply(subgoal_tac "takeB n w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' q b)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' q b)(*strict*)
   apply(erule disjE)
    apply(rename_tac w' q b)(*strict*)
    apply(clarsimp)
    apply(simp add: takeB_def)
   apply(rename_tac w' q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q b w'a a')(*strict*)
   apply(rule_tac
      w="w'"
      and w'="w'a"
      in proper_l3_l2_seq_nol2)
   apply(force)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(rule_tac
      x="q2"
      in exI)
  apply(simp add: cropTol3l2_def cropTol3l2_single_def fillL_def fill_def appL_def)
  done

lemma drop_and_crop_prefix2: "
    drop_and_crop w 0 = c @ [cons_l2 q A]
  \<Longrightarrow> isl2 (last w)
    \<Longrightarrow> w=c@[cons_l2 q A]"
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a')(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(case_tac a')
   apply(rename_tac a' qa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2)(*strict*)
  apply(simp add: isl2_def)
  done

lemma drop_and_crop_shiftn_HELPXX: "
  take (length w - n) w = w' @ [a']
  \<Longrightarrow> take (length w - Suc n) w = w'"
  apply (metis Nat.add_0_right One_nat_def add_Suc_shift butlast_conv_take butlast_snoc butlast_take diff_diff_left diff_le_self)
  done

lemma drop_and_crop_shift1: "
  drop_and_crop w (Suc n) = drop_and_crop (butlast w) n"
  apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
  apply(clarsimp)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma drop_and_crop_shiftn: "
  drop_and_crop w n = drop_and_crop (butn w n) 0"
  apply(induct n)
   apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="butn w (Suc n)"
      and s="butlast (butn w n)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(simp add: butn_def)
   apply(subgoal_tac "take (length w - n) w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac n)(*strict*)
   apply(erule disjE)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n w' a')(*strict*)
   apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
   apply (rule drop_and_crop_shiftn_HELPXX)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="drop_and_crop (butlast (butn w n)) 0"
      and s="drop_and_crop (butn w n) (Suc 0)"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule drop_and_crop_shift1)
  apply(rename_tac n)(*strict*)
  apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
  apply(clarsimp)
  apply(case_tac "length w\<le> Suc n")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="min (length w) (length w - n)"
      and s="length w - n"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="min (length w - n - Suc 0) (length w - n)"
      and s="length w - n - Suc 0"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="min (length w) (length w - n)"
      and s="length w - n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="min (length w - n - Suc 0) (length w - n)"
      and s="length w - n - Suc 0"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma drop_and_crop_prefix1: "
  proper_l3_l2_seq w
  \<Longrightarrow> drop_and_crop w n = c @ [cons_l2 q A]
  \<Longrightarrow> 0<n
  \<Longrightarrow> \<exists>q' w'. length w'=n \<and> c@[cons_l3 q A q']@w'= w"
  apply(subgoal_tac "drop_and_crop (butn w n) 0 = c @ [cons_l2 q A]")
   prefer 2
   apply(rule_tac
      t="drop_and_crop (butn w n) 0"
      and s="drop_and_crop w n"
      in subst)
    apply(rule drop_and_crop_shiftn)
   apply(force)
  apply(thin_tac "drop_and_crop w n = c @ [cons_l2 q A]")
  apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
  apply(subgoal_tac "min (length w) (length w - n) = length w - n")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(case_tac "length w \<le> n \<or> w = []")
   apply(clarsimp)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "take (length w - n) w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a' w'a a'a)(*strict*)
  apply(case_tac "Suc (length w'a) - n")
   apply(rename_tac w' a' w'a a'a)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' w'a a'a nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length w'a) = Suc nat+n")
   apply(rename_tac w' a' w'a a'a nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w' a' w'a a'a nat)(*strict*)
  apply(clarsimp)
  apply(thin_tac "min (nat + n) nat = nat")
  apply(subgoal_tac "take nat w'a = w'")
   apply(rename_tac w' a' w'a a'a nat)(*strict*)
   prefer 2
   apply(rule take_restrict)
    apply(rename_tac w' a' w'a a'a nat)(*strict*)
    apply(force)
   apply(rename_tac w' a' w'a a'a nat)(*strict*)
   apply(force)
  apply(rename_tac w' a' w'a a'a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a' w'a a'a nat)(*strict*)
  apply(case_tac a')
   apply(rename_tac a' w'a a'a nat qa b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w'a a'a nat qa b)(*strict*)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac w'a a'a nat)(*strict*)
   apply(simp add: proper_l3_l2_seq_def proper_l3_seq_def only_l3_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac w'a nat qa Aa)(*strict*)
   apply(erule_tac
      x="take nat w'a"
      in allE)
   apply(erule_tac
      x="drop (Suc nat) w'a"
      in allE)
   apply(erule_tac
      x="cons_l2 q A"
      in allE)
   apply(erule impE)
    apply(rename_tac w'a nat qa Aa)(*strict*)
    apply(rule_tac
      t="take nat w'a @ cons_l2 q A # drop (Suc nat) w'a"
      and s="take (Suc nat) w'a @ drop (Suc nat) w'a"
      in ssubst)
     apply(rename_tac w'a nat qa Aa)(*strict*)
     apply(force)
    apply(rename_tac w'a nat qa Aa)(*strict*)
    apply (metis append_take_drop_id)
   apply(rename_tac w'a nat qa Aa)(*strict*)
   apply(force)
  apply(rename_tac a' w'a a'a nat q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w'a a'a nat q1 b q2)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(clarsimp)
  apply(rename_tac w'a a'a nat q2)(*strict*)
  apply(erule_tac
      x="q2"
      in allE)
  apply(erule_tac
      x="drop (Suc nat) w'a@[a'a]"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "take nat w'a @ cons_l3 q A q2 # drop (Suc nat) w'a = w'a")
   apply(rename_tac w'a a'a nat q2)(*strict*)
   apply(force)
  apply(rename_tac w'a a'a nat q2)(*strict*)
  apply(rule_tac
      t="take nat w'a @ cons_l3 q A q2 # drop (Suc nat) w'a"
      and s="take (Suc nat) w'a @ drop (Suc nat) w'a"
      in ssubst)
   apply(rename_tac w'a a'a nat q2)(*strict*)
   apply(force)
  apply(rename_tac w'a a'a nat q2)(*strict*)
  apply (metis append_take_drop_id)
  done

lemma drop_and_crop_preserves_l3_l2_separation: "
  proper_l3_l2_seq (w @ v)
  \<Longrightarrow> n<length v
  \<Longrightarrow> proper_l3_l2_seq (w @ drop_and_crop v n)"
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' q A)(*strict*)
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' q A)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' q A)(*strict*)
  apply(erule_tac
      P="v = []"
      in disjE)
   apply(rename_tac w' q A)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q A)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A w'a)(*strict*)
  apply(subgoal_tac "w @ drop_and_crop (w'a @ [cons_l2 q A]) n=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac q A w'a)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac q A w'a)(*strict*)
  apply(erule_tac
      P="w @ drop_and_crop (w'a @ [cons_l2 q A]) n = []"
      in disjE)
   apply(rename_tac q A w'a)(*strict*)
   apply(clarsimp)
   apply(simp add: drop_and_crop_def)
   apply(simp add: butn_def)
   apply(simp add: cropTol3l2_def)
   apply(case_tac w'a)
    apply(rename_tac q A w'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac q A w'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A w'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A w'a w' a')(*strict*)
  apply(case_tac a')
   apply(rename_tac q A w'a w' a' qa b)(*strict*)
   prefer 2
   apply(rename_tac q A w'a w' a' q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w'a w' q1 b q2)(*strict*)
   apply(simp add: drop_and_crop_def)
   apply(simp add: butn_def)
   apply(simp add: cropTol3l2_def)
   apply(case_tac "w'a=[] \<and> Suc 0\<le>n")
    apply(rename_tac q A w'a w' q1 b q2)(*strict*)
    apply(clarsimp)
   apply(rename_tac q A w'a w' q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w'a q1 b q2)(*strict*)
   apply(simp add: cropTol3l2_single_def)
   apply(case_tac "Suc 0-n")
    apply(rename_tac q A w'a q1 b q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q w'a q1 b q2)(*strict*)
    apply(case_tac "(last (take (Suc (length w'a) - n) w'a))")
     apply(rename_tac q w'a q1 b q2 qa ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac q w'a q1 b q2 q1a ba q2a)(*strict*)
    apply(clarsimp)
   apply(rename_tac q A w'a q1 b q2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A w'a w' a' qa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A w'a w' qa b)(*strict*)
  apply(subgoal_tac "prefix w w' \<or> prefix w' w")
   apply(rename_tac q A w'a w' qa b)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac q A w'a w' qa b)(*strict*)
  apply(erule_tac
      P="w \<sqsubseteq> w'"
      in disjE)
   apply(rename_tac q A w'a w' qa b)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac q A w'a w' qa b c)(*strict*)
   apply(case_tac c)
    apply(rename_tac q A w'a w' qa b c)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a w' qa b)(*strict*)
    apply(case_tac w'a)
     apply(rename_tac q A w'a w' qa b)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A w' qa b)(*strict*)
     apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
    apply(rename_tac q A w'a w' qa b a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w' qa b a list)(*strict*)
    apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
    apply(case_tac "Suc (Suc (length list)) - n")
     apply(rename_tac q A w' qa b a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A w' qa b a list nat)(*strict*)
    apply(clarsimp)
    apply(case_tac nat)
     apply(rename_tac q A w' qa b a list nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac q w' qa b a list)(*strict*)
     apply(case_tac a)
      apply(rename_tac q w' qa b a list qb ba)(*strict*)
      apply(clarsimp)
      apply(rename_tac q w' qa b list)(*strict*)
      apply(rule_tac
      ?w1.0="w'"
      and w="(w' @ cons_l2 qa b # list)"
      in proper_l3_seq_no_l2)
       apply(rename_tac q w' qa b list)(*strict*)
       apply(force)
      apply(rename_tac q w' qa b list)(*strict*)
      apply(force)
     apply(rename_tac q w' qa b a list q1 ba q2)(*strict*)
     apply(clarsimp)
     apply(rename_tac q w' qa b list q2)(*strict*)
     apply(rule conjI)
      apply(rename_tac q w' qa b list q2)(*strict*)
      apply(rule proper_l3_seq_drop_tail)
      apply(force)
     apply(rename_tac q w' qa b list q2)(*strict*)
     apply(subgoal_tac "w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
      apply(rename_tac q w' qa b list q2)(*strict*)
      prefer 2
      apply(rule case_list)
     apply(rename_tac q w' qa b list q2)(*strict*)
     apply(erule_tac
      P="w' = []"
      in disjE)
      apply(rename_tac q w' qa b list q2)(*strict*)
      apply(clarsimp)
      apply(rename_tac q qa b list q2)(*strict*)
      apply(simp add: last_back_state_def)
     apply(rename_tac q w' qa b list q2)(*strict*)
     apply(rule disjI2)
     apply(clarsimp)
     apply(rename_tac q qa b list q2 w'a a')(*strict*)
     apply(case_tac a')
      apply(rename_tac q qa b list q2 w'a a' qb ba)(*strict*)
      apply(clarsimp)
      apply(rename_tac q qa b list q2 w'a qb ba)(*strict*)
      apply(rule_tac
      ?w1.0="w'a"
      and w="(w'a @ cons_l2 qb ba # cons_l3 qa b q2 # list)"
      in proper_l3_seq_no_l2)
       apply(rename_tac q qa b list q2 w'a qb ba)(*strict*)
       apply(force)
      apply(rename_tac q qa b list q2 w'a qb ba)(*strict*)
      apply(force)
     apply(rename_tac q qa b list q2 w'a a' q1 ba q2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa b list q2 w'a q1 ba q2a)(*strict*)
     apply(subgoal_tac "last_back_state (w'a @ [cons_l3 q1 ba q2a]) = Some q2a")
      apply(rename_tac q qa b list q2 w'a q1 ba q2a)(*strict*)
      prefer 2
      apply(rule last_back_state_l3)
      apply(force)
     apply(rename_tac q qa b list q2 w'a q1 ba q2a)(*strict*)
     apply(clarsimp)
     apply(rule proper_l3_seq_l3_adjacent)
      apply(rename_tac q qa b list q2 w'a q1 ba q2a)(*strict*)
      apply(force)
     apply(rename_tac q qa b list q2 w'a q1 ba q2a)(*strict*)
     apply(force)
    apply(rename_tac q A w' qa b a list nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w' qa b a list nata)(*strict*)
    apply(case_tac list)
     apply(rename_tac q A w' qa b a list nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A w' qa b a list nata aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac q A w'a w' qa b c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w'a w' qa b)(*strict*)
   apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
   apply(case_tac w'a)
    apply(rename_tac q A w'a w' qa b)(*strict*)
    apply(clarsimp)
   apply(rename_tac q A w'a w' qa b a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A w'a w' qa b)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac q A w'a qa b c)(*strict*)
  apply(subgoal_tac "proper_l3_l2_seq (drop_and_crop (w'a @ [cons_l2 q A]) n)")
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(clarsimp)
   apply(simp add: proper_l3_l2_seq_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac q A w'a qa b c)(*strict*)
    apply(case_tac c)
     apply(rename_tac q A w'a qa b c)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A w'a qa b)(*strict*)
     apply(rule proper_l3_seq_drop_tail)
     apply(force)
    apply(rename_tac q A w'a qa b c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b a list)(*strict*)
    apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac q A w'a qa b a list)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac q A w'a qa b a list)(*strict*)
    apply(erule_tac
      P="w = []"
      in disjE)
     apply(rename_tac q A w'a qa b a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A w'a qa b a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b a list w' a')(*strict*)
    apply(case_tac a')
     apply(rename_tac q A w'a qa b a list w' a' qb ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A w'a qa b a list w' qb ba)(*strict*)
     apply(rule_tac
      ?w1.0="w'"
      and w="(w' @ cons_l2 qb ba # w'a)"
      in proper_l3_seq_no_l2)
      apply(rename_tac q A w'a qa b a list w' qb ba)(*strict*)
      apply(force)
     apply(rename_tac q A w'a qa b a list w' qb ba)(*strict*)
     apply(force)
    apply(rename_tac q A w'a qa b a list w' a' q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b a list w' q1 ba q2)(*strict*)
    apply(case_tac a)
     apply(rename_tac q A w'a qa b a list w' q1 ba q2 qb bb)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A w'a qa b list w' q1 ba q2 qb bb)(*strict*)
     apply(rule_tac
      ?w1.0="[]"
      and w="(cons_l2 qb bb # list)"
      in proper_l3_seq_no_l2)
      apply(rename_tac q A w'a qa b list w' q1 ba q2 qb bb)(*strict*)
      apply(force)
     apply(rename_tac q A w'a qa b list w' q1 ba q2 qb bb)(*strict*)
     apply(force)
    apply(rename_tac q A w'a qa b a list w' q1 ba q2 q1a bb q2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b list w' q1 ba q2 q1a bb q2a)(*strict*)
    apply(case_tac w'a)
     apply(rename_tac q A w'a qa b list w' q1 ba q2 q1a bb q2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a)(*strict*)
     apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
    apply(rename_tac q A w'a qa b list w' q1 ba q2 q1a bb q2a a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a a lista qb bc)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista qb bc)(*strict*)
     apply(rule_tac
      ?w1.0="w'@[SSX]"
      and w="(w' @ cons_l3 q1 ba q2 # cons_l2 qb bc # lista)" for SSX
      in proper_l3_seq_no_l2)
      apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista qb bc)(*strict*)
      apply(force)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista qb bc)(*strict*)
     apply(force)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a a lista q1b bc q2b)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b)(*strict*)
    apply(subgoal_tac "q1b=q1a")
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b)(*strict*)
     prefer 2
     apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
     apply(case_tac "Suc (Suc (length lista)) - n")
      apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b)(*strict*)
      apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nat)(*strict*)
     apply(clarsimp)
     apply(case_tac nat)
      apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nat nata)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nata)(*strict*)
     apply(case_tac lista)
      apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b nata a listb)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista q1b bc q2b)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista bc q2b)(*strict*)
    apply(subgoal_tac "q2=q1a")
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista bc q2b)(*strict*)
     prefer 2
     apply(rule proper_l3_seq_l3_adjacent)
      apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista bc q2b)(*strict*)
      apply(force)
     apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista bc q2b)(*strict*)
     apply(force)
    apply(rename_tac q A qa b list w' q1 ba q2 q1a bb q2a lista bc q2b)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b list w' q1 ba q1a bb q2a lista bc q2b)(*strict*)
    apply(rule_tac
      t="w' @ cons_l3 q1 ba q1a # cons_l3 q1a bb q2a # list"
      and s="w' @ [cons_l3 q1 ba q1a,cons_l3 q1a bb q2a] @ list"
      in ssubst)
     apply(rename_tac q A qa b list w' q1 ba q1a bb q2a lista bc q2b)(*strict*)
     apply(force)
    apply(rename_tac q A qa b list w' q1 ba q1a bb q2a lista bc q2b)(*strict*)
    apply(rule proper_l3_seq_compose2)
     apply(rename_tac q A qa b list w' q1 ba q1a bb q2a lista bc q2b)(*strict*)
     apply(rule proper_l3_seq_drop_tail)
     apply(force)
    apply(rename_tac q A qa b list w' q1 ba q1a bb q2a lista bc q2b)(*strict*)
    apply(force)
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(erule_tac
      P="last_back_state c = None"
      in disjE)
    apply(rename_tac q A w'a qa b c)(*strict*)
    apply(subgoal_tac "c=[]")
     apply(rename_tac q A w'a qa b c)(*strict*)
     prefer 2
     apply(rule last_back_state_empty)
     apply(force)
    apply(rename_tac q A w'a qa b c)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b)(*strict*)
    apply(case_tac "w'a")
     apply(rename_tac q A w'a qa b)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b)(*strict*)
     apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
    apply(rename_tac q A w'a qa b a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b a list)(*strict*)
    apply(case_tac a)
     apply(rename_tac q A qa b a list qb ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b list qb ba)(*strict*)
     apply(rule_tac
      ?w1.0="w"
      and w="(w @ cons_l2 qb ba # list)"
      in proper_l3_seq_no_l2)
      apply(rename_tac q A qa b list qb ba)(*strict*)
      apply(force)
     apply(rename_tac q A qa b list qb ba)(*strict*)
     apply(force)
    apply(rename_tac q A qa b a list q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A qa b list q1 ba q2)(*strict*)
    apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
    apply(clarsimp)
    apply(case_tac "Suc (Suc (length list)) - n")
     apply(rename_tac q A qa b list q1 ba q2)(*strict*)
     apply(clarsimp)
    apply(rename_tac q A qa b list q1 ba q2 nat)(*strict*)
    apply(clarsimp)
    apply(case_tac nat)
     apply(rename_tac q A qa b list q1 ba q2 nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa b list q2)(*strict*)
     prefer 2
     apply(rename_tac q A qa b list q1 ba q2 nat nata)(*strict*)
     apply(clarsimp)
     apply(rename_tac q A qa b list q1 ba q2 nata)(*strict*)
     apply(case_tac list)
      apply(rename_tac q A qa b list q1 ba q2 nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac q A qa b list q1 ba q2 nata a lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac q qa b list q2)(*strict*)
    apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac q qa b list q2)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac q qa b list q2)(*strict*)
    apply(erule_tac
      P="w = []"
      in disjE)
     apply(rename_tac q qa b list q2)(*strict*)
     apply(clarsimp)
    apply(rename_tac q qa b list q2)(*strict*)
    apply(clarsimp)
    apply(rename_tac q qa b list q2 w' a')(*strict*)
    apply(case_tac a')
     apply(rename_tac q qa b list q2 w' a' qb ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac q qa b list q2 w' qb ba)(*strict*)
     apply(rule_tac
      ?w1.0="w'"
      and w="(w' @ cons_l2 qb ba # cons_l3 qa b q2 # list)"
      in proper_l3_seq_no_l2)
      apply(rename_tac q qa b list q2 w' qb ba)(*strict*)
      apply(force)
     apply(rename_tac q qa b list q2 w' qb ba)(*strict*)
     apply(force)
    apply(rename_tac q qa b list q2 w' a' q1 ba q2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac q qa b list q2 w' q1 ba q2a)(*strict*)
    apply(subgoal_tac "q2a=qa")
     apply(rename_tac q qa b list q2 w' q1 ba q2a)(*strict*)
     prefer 2
     apply(rule proper_l3_seq_l3_adjacent)
      apply(rename_tac q qa b list q2 w' q1 ba q2a)(*strict*)
      apply(force)
     apply(rename_tac q qa b list q2 w' q1 ba q2a)(*strict*)
     apply(force)
    apply(rename_tac q qa b list q2 w' q1 ba q2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac q qa b list q2 w' q1 ba)(*strict*)
    apply(subgoal_tac "last_back_state (w' @ [cons_l3 q1 ba qa]) = Some qa")
     apply(rename_tac q qa b list q2 w' q1 ba)(*strict*)
     apply(force)
    apply(rename_tac q qa b list q2 w' q1 ba)(*strict*)
    apply(rule last_back_state_l3)
    apply(force)
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(subgoal_tac "c=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac q A w'a qa b c)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(erule_tac
      P="c = []"
      in disjE)
    apply(rename_tac q A w'a qa b c)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b)(*strict*)
    apply(simp add: last_back_state_def)
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w'a qa b w' a')(*strict*)
   apply(case_tac a')
    apply(rename_tac q A w'a qa b w' a' qb ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac q A w'a qa b w' qb ba)(*strict*)
    apply(rule_tac
      ?w1.0="w'"
      and w="(w' @ [cons_l2 qb ba])"
      in proper_l3_seq_no_l2)
     apply(rename_tac q A w'a qa b w' qb ba)(*strict*)
     apply(force)
    apply(rename_tac q A w'a qa b w' qb ba)(*strict*)
    apply(force)
   apply(rename_tac q A w'a qa b w' a' q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w'a qa b w' q1 ba q2)(*strict*)
   apply(subgoal_tac "last_back_state (w @ w' @ [cons_l3 q1 ba q2]) = Some q2")
    apply(rename_tac q A w'a qa b w' q1 ba q2)(*strict*)
    prefer 2
    apply(rule last_back_state_l3)
    apply(force)
   apply(rename_tac q A w'a qa b w' q1 ba q2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "last_back_state (w' @ [cons_l3 q1 ba q2]) = Some q2")
    apply(rename_tac q A w'a qa b w' q1 ba q2)(*strict*)
    prefer 2
    apply(rule last_back_state_l3)
    apply(force)
   apply(rename_tac q A w'a qa b w' q1 ba q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A w'a qa b c)(*strict*)
  apply(subgoal_tac "proper_l3_seq w'a")
   apply(rename_tac q A w'a qa b c)(*strict*)
   prefer 2
   apply(rule proper_l3_seq_drop_front)
   apply(force)
  apply(rename_tac q A w'a qa b c)(*strict*)
  apply(subgoal_tac "w'a=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac q A w'a qa b c)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac q A w'a qa b c)(*strict*)
  apply(erule_tac
      P="w'a = []"
      in disjE)
   apply(rename_tac q A w'a qa b c)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A qa b c)(*strict*)
   apply(simp add: drop_and_crop_def cropTol3l2_single_def butn_def cropTol3l2_def)
   apply(clarsimp)
   apply(rename_tac qa b)(*strict*)
   apply(simp add: proper_l3_l2_seq_def)
   apply(rename_tac qa)(*strict*)
   apply(simp add: last_back_state_def)
  apply(rename_tac q A w'a qa b c)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c w' a')(*strict*)
  apply(case_tac a')
   apply(rename_tac q A qa b c w' a' qb ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A qa b c w' qb ba)(*strict*)
   apply(rule_tac
      ?w1.0="w@w'"
      and w="(w @ w' @ [cons_l2 qb ba])"
      in proper_l3_seq_no_l2)
    apply(rename_tac q A qa b c w' qb ba)(*strict*)
    apply(force)
   apply(rename_tac q A qa b c w' qb ba)(*strict*)
   apply(force)
  apply(rename_tac q A qa b c w' a' q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c w' q1 ba q2)(*strict*)
  apply(subgoal_tac "last_back_state (w @ w' @ [cons_l3 q1 ba q2]) = Some q2")
   apply(rename_tac q A qa b c w' q1 ba q2)(*strict*)
   prefer 2
   apply(rule last_back_state_l3)
   apply(force)
  apply(rename_tac q A qa b c w' q1 ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c w' q1 ba)(*strict*)
  apply(thin_tac "proper_l3_seq (w @ w' @ [cons_l3 q1 ba q])")
  apply(thin_tac "last_back_state (w @ w' @ [cons_l3 q1 ba q]) = Some q")
  apply(simp add: proper_l3_l2_seq_def)
  apply(case_tac n)
   apply(rename_tac q A qa b c w' q1 ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "SSw = SSc @ [cons_l2 SSq SSA]" for SSw SSc SSq SSA)
    apply(rename_tac q A qa b c w' q1 ba)(*strict*)
    prefer 2
    apply(rule drop_and_crop_prefix2)
     apply(rename_tac q A qa b c w' q1 ba)(*strict*)
     apply(force)
    apply(rename_tac q A qa b c w' q1 ba)(*strict*)
    apply(clarsimp)
    apply(simp add: isl2_def)
   apply(rename_tac q A qa b c w' q1 ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac qa b w' q1 ba)(*strict*)
   apply(subgoal_tac "last_back_state (w' @ [cons_l3 q1 ba qa]) = Some qa")
    apply(rename_tac qa b w' q1 ba)(*strict*)
    apply(force)
   apply(rename_tac qa b w' q1 ba)(*strict*)
   apply(rule last_back_state_l3)
   apply(force)
  apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
  apply(subgoal_tac "\<exists>q' w'. length w' = SSn \<and> SSc @ [cons_l3 SSq SSA q'] @ w' = SSw" for SSn SSc SSq SSA SSw)
   apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
   prefer 2
   apply(rule drop_and_crop_prefix1)
     apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
   apply(simp add: proper_l3_l2_seq_def)
   apply(rule disjI2)
   apply(rule last_back_state_l3)
   apply(force)
  apply(rename_tac q A qa b c w' q1 ba nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c w' q1 ba nat q' w'a)(*strict*)
  apply(subgoal_tac "w'a=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac q A qa b c w' q1 ba nat q' w'a)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac q A qa b c w' q1 ba nat q' w'a)(*strict*)
  apply(erule disjE)
   apply(rename_tac q A qa b c w' q1 ba nat q' w'a)(*strict*)
   apply(clarsimp)
  apply(rename_tac q A qa b c w' q1 ba nat q' w'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c w' q1 ba q' w'b)(*strict*)
  apply(subgoal_tac "w'b=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac q A qa b c w' q1 ba q' w'b)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac q A qa b c w' q1 ba q' w'b)(*strict*)
  apply(erule disjE)
   apply(rename_tac q A qa b c w' q1 ba q' w'b)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A w' q1 ba)(*strict*)
   apply(rule conjI)
    apply(rename_tac q A w' q1 ba)(*strict*)
    apply(rule proper_l3_seq_drop_tail)
    apply(force)
   apply(rename_tac q A w' q1 ba)(*strict*)
   apply(rule proper_l3_seq_inter_1)
   apply(force)
  apply(rename_tac q A qa b c w' q1 ba q' w'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q A qa b c q1 ba q' w'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac q A qa b c q1 ba q' w'a)(*strict*)
   apply(rule proper_l3_seq_drop_tail)
   apply(force)
  apply(rename_tac q A qa b c q1 ba q' w'a)(*strict*)
  apply(rule proper_l3_seq_inter_1)
  apply(force)
  done

lemma take_unchanged_prefix_of_drop_and_crop: "
  n<length v
  \<Longrightarrow> w=take (length w) (drop_and_crop (w@v) n)"
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  apply(clarsimp)
  apply(subgoal_tac "take (length v - n) v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="butlast (w @ w' @ [a'])"
      and s="SSX" for SSX
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  done

lemma drop_and_crop_preserves_proper_l3_l2_seq2: "
  proper_l3_l2_seq (w @ v)
  \<Longrightarrow> v=[]
    \<Longrightarrow> proper_l3_l2_seq (w @ drop_and_crop v n)"
  apply(clarsimp)
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  done

lemma drop_and_crop_preserves_proper_l3_l2_seq: "
    proper_l3_l2_seq v
    \<Longrightarrow> n<length v
    \<Longrightarrow> proper_l3_l2_seq (drop_and_crop v n)"
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  apply(rule conjI)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: proper_l3_l2_seq_def)
  apply(clarsimp)
  apply(rename_tac w' q A)(*strict*)
  apply(subgoal_tac "take (Suc (length w') - n) w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' q A)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' q A)(*strict*)
  apply(erule_tac
      P="take (Suc (length w') - n) w' = []"
      in disjE)
   apply(rename_tac w' q A)(*strict*)
   apply(clarsimp)
   apply(rename_tac q A)(*strict*)
   apply(erule_tac
      x="q"
      in allE)
   apply(erule_tac
      P="\<forall>Aa. cropTol3l2_single (cons_l2 q A) \<noteq> cons_l2 q Aa"
      in disjE)
    apply(rename_tac q A)(*strict*)
    apply(erule_tac
      x="A"
      in allE)
    apply(simp add: cropTol3l2_single_def)
   apply(rename_tac q A)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q A)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q A w'a a')(*strict*)
  apply(case_tac "Suc 0 \<le> n")
   apply(rename_tac w' q A w'a a')(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac q A w'a a')(*strict*)
   apply(subgoal_tac "butlast (w'a @ [a', cons_l2 q A]) = (w'a @ [a'])")
    apply(rename_tac q A w'a a')(*strict*)
    prefer 2
    apply (metis butLastSimp rotate_simps)
   apply(rename_tac q A w'a a')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="q"
      in allE)
   apply(erule_tac
      P="\<forall>Aa. cropTol3l2_single (cons_l2 q A) \<noteq> cons_l2 q Aa"
      in disjE)
    apply(rename_tac q A w'a a')(*strict*)
    apply(erule_tac
      x="A"
      in allE)
    apply(simp add: cropTol3l2_single_def)
   apply(rename_tac q A w'a a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q A w'a a')(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q w'a a')(*strict*)
  apply(case_tac "Suc (length w') - n")
   apply(rename_tac w' q w'a a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q w'a a' nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length w') = Suc nat+n")
   apply(rename_tac w' q w'a a' nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w' q w'a a' nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "take nat w' = w'a")
   apply(rename_tac w' q w'a a' nat)(*strict*)
   prefer 2
   apply(rule take_restrict)
    apply(rename_tac w' q w'a a' nat)(*strict*)
    apply(force)
   apply(rename_tac w' q w'a a' nat)(*strict*)
   apply(force)
  apply(rename_tac w' q w'a a' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q a' nat)(*strict*)
  apply(erule impE)
   apply(rename_tac w' q a' nat)(*strict*)
   apply(rule_tac
      v="drop nat w'"
      in proper_l3_seq_drop_tail)
   apply(force)
  apply(rename_tac w' q a' nat)(*strict*)
  apply(case_tac a')
   apply(rename_tac w' q a' nat qa b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q nat qa b)(*strict*)
   apply(rule_tac
      ?w2.0="drop (Suc nat) w'"
      and q="qa"
      and A="b"
      and ?w1.0="take nat w'"
      and w="w'"
      in proper_l3_seq_no_l2)
    apply(rename_tac w' q nat qa b)(*strict*)
    apply(force)
   apply(rename_tac w' q nat qa b)(*strict*)
   apply (metis ConsApp append_assoc append_take_drop_id)
  apply(rename_tac w' q a' nat q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q nat q1 b q2)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(rename_tac w' q nat q1 b q2)(*strict*)
  apply(subgoal_tac "take nat w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' q nat q1 b q2)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' q nat q1 b q2)(*strict*)
  apply(erule_tac
      P="take nat w' = []"
      in disjE)
   apply(rename_tac w' q nat q1 b q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q nat q1 b q2 y)(*strict*)
   apply(simp add: last_back_state_def)
  apply(rename_tac w' q nat q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q nat q1 b q2 w'a a' y)(*strict*)
  apply(case_tac nat)
   apply(rename_tac w' q nat q1 b q2 w'a a' y)(*strict*)
   apply(force)
  apply(rename_tac w' q nat q1 b q2 w'a a' y nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q q1 b q2 w'a a' y nata)(*strict*)
  apply(subgoal_tac "take nata w' = w'a")
   apply(rename_tac w' q q1 b q2 w'a a' y nata)(*strict*)
   prefer 2
   apply(rule take_restrict)
    apply(rename_tac w' q q1 b q2 w'a a' y nata)(*strict*)
    apply(force)
   apply(rename_tac w' q q1 b q2 w'a a' y nata)(*strict*)
   apply(force)
  apply(rename_tac w' q q1 b q2 w'a a' y nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q q1 b q2 a' y nata)(*strict*)
  apply(case_tac a')
   apply(rename_tac w' q q1 b q2 a' y nata qa ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q q1 b q2 y nata qa ba)(*strict*)
   apply(rule_tac
      ?w2.0="drop (Suc nata) w'"
      and q="qa"
      and A="ba"
      and ?w1.0="take nata w'"
      and w="w'"
      in proper_l3_seq_no_l2)
    apply(rename_tac w' q q1 b q2 y nata qa ba)(*strict*)
    apply(force)
   apply(rename_tac w' q q1 b q2 y nata qa ba)(*strict*)
   apply (metis ConsApp append_assoc append_take_drop_id)
  apply(rename_tac w' q q1 b q2 a' y nata q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q q1 b q2 y nata q1a ba q2a)(*strict*)
  apply(subgoal_tac "last_back_state (take nata w' @ [cons_l3 q1a ba q2a]) = Some q2a")
   apply(rename_tac w' q q1 b q2 y nata q1a ba q2a)(*strict*)
   prefer 2
   apply(rule last_back_state_l3)
   apply(force)
  apply(rename_tac w' q q1 b q2 y nata q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
  apply(subgoal_tac "y=q1")
   apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
  apply(rule_tac
      ?q1.0="q1a"
      and A="ba"
      and B="b"
      and ?q3.0="q2"
      and ?w1.0="take nata w'"
      and ?w2.0="drop(Suc(Suc nata))w'"
      in proper_l3_seq_l3_adjacent)
   apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
   apply(force)
  apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
  apply(rule_tac
      P="\<lambda>x. x=take nata w' @ [cons_l3 q1a ba y, cons_l3 q1 b q2] @ drop (Suc (Suc nata)) w'"
      and t="w'"
      and s="take (Suc (Suc nata)) w'@drop (Suc (Suc nata)) w'"
      in ssubst)
   apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
   apply (metis append_take_drop_id)
  apply(rename_tac w' q q1 b q2 y nata q1a ba)(*strict*)
  apply(clarsimp)
  done

lemma proper_l3_l2_seq_preserved_by_drop_and_crop: "
  proper_l3_l2_seq (w1 @ w2 @ [cons_l2 q1 A1])
  \<Longrightarrow> drop_and_crop (w2 @ [cons_l2 q1 A1]) n = w3 @ [cons_l2 q2 A2]
  \<Longrightarrow> proper_l3_l2_seq (w1 @ w3 @ [cons_l2 q2 A2])"
  apply(case_tac n)
   apply(clarsimp)
   apply(simp add: drop_and_crop_def butn_def)
   apply(simp add: drop_and_crop_def butn_def cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>q w. w3@[cons_l3 q2 A2 q]@w = w2")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat q w)(*strict*)
   apply(thin_tac "drop_and_crop (w3 @ cons_l3 q2 A2 q # w @ [cons_l2 q1 A1]) (Suc nat) = w3 @ [cons_l2 q2 A2]")
   apply(rule_tac
      t="w1 @ w3 @ [cons_l2 q2 A2]"
      and s="drop_and_crop (w1 @ w3 @ cons_l3 q2 A2 q # w @ [cons_l2 q1 A1]) (Suc(length w))"
      in ssubst)
    apply(rename_tac nat q w)(*strict*)
    prefer 2
    apply(rule drop_and_crop_preserves_proper_l3_l2_seq)
     apply(rename_tac nat q w)(*strict*)
     apply(force)
    apply(rename_tac nat q w)(*strict*)
    apply(force)
   apply(rename_tac nat q w)(*strict*)
   apply(simp add: drop_and_crop_def butn_def cropTol3l2_def cropTol3l2_single_def)
   apply(rename_tac q w)(*strict*)
   apply (metis butlast_snoc_2)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>qX. fillL (drop_and_crop (w2 @ [cons_l2 q1 A1]) (Suc nat)) qX = butn SSw SSn" for SSw SSn)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule fillL_exists)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule proper_l3_l2_seq_drop_prime)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat qX)(*strict*)
  apply(rule_tac
      x="qX"
      in exI)
  apply(simp add: butn_def)
  apply(rule_tac
      x="drop (length w2-nat) w2"
      in exI)
  apply(simp add: fillL_def appL_def fill_def)
  apply(rule_tac
      t="w3 @ cons_l3 q2 A2 qX # drop (length w2 - nat) w2"
      and s="take (length w2 - nat) w2@drop (length w2 - nat) w2"
      in ssubst)
   apply(rename_tac nat qX)(*strict*)
   apply(rule_tac
      t="take (length w2 - nat) w2"
      and s="w3 @ [cons_l3 q2 A2 qX]"
      in ssubst)
    apply(rename_tac nat qX)(*strict*)
    apply(force)
   apply(rename_tac nat qX)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac nat qX)(*strict*)
  apply (metis append_take_drop_id)
  done

lemma take_drop_and_crop_id: "
   n<length w2
   \<Longrightarrow> take (length w1) (drop_and_crop (w1 @ w2) n) = w1"
  apply(simp add: drop_and_crop_def butn_def cropTol3l2_def)
  apply(clarsimp)
  apply(subgoal_tac "take (length w2 - n) w2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply (metis butlast_snoc_2 takePrecise)
  done

definition prod_to_edge :: "
  ('a, 'b, 'c) epda
  \<Rightarrow> (('a, 'c) DT_l2_l3_nonterminals, 'b) cfg_step_label
  \<Rightarrow> ('a, 'b, 'c) epda_step_label"
  where
    "prod_to_edge G' p \<equiv>
  THE e. e \<in> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' p"

lemma prod_to_edge_liftA_liftB: "
  map (case_DT_two_elements teA (\<lambda>p. teA (prod_to_edge G' p)))
  (liftB w) =
  liftA (map (prod_to_edge G') w)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c1 \<pi>1 c2
  \<Longrightarrow> cfgLM.trans_der G d2 c1' \<pi>2 c2'
  \<Longrightarrow> length \<pi>1=length \<pi>2
  \<Longrightarrow> \<forall>k. Suc 0 \<le> k \<and> k \<le> length \<pi>2 \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (the (get_label (d1 k))) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G' (the (get_label (d2 k)))
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2"
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: prod_to_edge_def)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      g="d1"
      and n="Suc i"
      and m="length(\<pi>2)"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac i e ea)(*strict*)
      apply(force)
     apply(rename_tac i e ea)(*strict*)
     apply(force)
    apply(rename_tac i e ea)(*strict*)
    apply(force)
   apply(rename_tac i e ea)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e c ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      g="d2"
      and n="Suc i"
      and m="length(\<pi>2)"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac i e c ea eb)(*strict*)
      apply(force)
     apply(rename_tac i e c ea eb)(*strict*)
     apply(force)
    apply(rename_tac i e c ea eb)(*strict*)
    apply(force)
   apply(rename_tac i e c ea eb)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c ea ca)(*strict*)
  apply(simp add: get_label_def)
  apply(subgoal_tac "e=\<pi>1!i")
   apply(rename_tac i e c ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac i e c ea ca)(*strict*)
       apply(force)
      apply(rename_tac i e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac i e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac i e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac i e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac i e c ea ca)(*strict*)
  apply(subgoal_tac "ea=\<pi>2!i")
   apply(rename_tac i e c ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac i e c ea ca)(*strict*)
       apply(force)
      apply(rename_tac i e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac i e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac i e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac i e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac i e c ea ca)(*strict*)
  apply(clarsimp)
  done

lemma map_foldl_prefix_equal_hlp: "
  \<forall>i. i<n1 \<longrightarrow> i<n2 \<longrightarrow> length (f\<pi>1 ! i) = length (f\<pi>2 ! i)
  \<Longrightarrow> map (prod_to_edge G') (foldl (@) [] f\<pi>1) @ c1 = map (prod_to_edge G') (foldl (@) [] f\<pi>2) @ c2
  \<Longrightarrow> n1 \<le> length f\<pi>1
  \<Longrightarrow> n2 \<le> length f\<pi>2
  \<Longrightarrow> k \<le> n1
  \<Longrightarrow> k \<le> n2
  \<Longrightarrow> map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1)) =
  map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2))"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="map (prod_to_edge G') (foldl (@) [] (take (Suc k) f\<pi>1))"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(rule map_foldl)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="map (prod_to_edge G') (foldl (@) [] (take (Suc k) f\<pi>2))"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(rule map_foldl)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="take (Suc k) f\<pi>1"
      and s="take k f\<pi>1@ [f\<pi>1!k]"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply (metis le_trans less_eq_Suc_le_raw take_nth_split)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="take (Suc k) f\<pi>2"
      and s="take k f\<pi>2@ [f\<pi>2!k]"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply (metis le_trans less_eq_Suc_le_raw take_nth_split)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="map (map (prod_to_edge G')) (take k f\<pi>1 @ [f\<pi>1 ! k])"
      and s=" map (map (prod_to_edge G')) (take k f\<pi>1) @ map (map (prod_to_edge G')) ([f\<pi>1 ! k]) "
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="map (map (prod_to_edge G')) (take k f\<pi>2 @ [f\<pi>2 ! k])"
      and s=" map (map (prod_to_edge G')) (take k f\<pi>2) @ map (map (prod_to_edge G')) ([f\<pi>2 ! k]) "
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>1) @ map (map (prod_to_edge G')) [f\<pi>1 ! k])"
      and s=" foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>1)) @ foldl (@) [] (map (map (prod_to_edge G')) [f\<pi>1 ! k]) "
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>2) @ map (map (prod_to_edge G')) [f\<pi>2 ! k])"
      and s=" foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>2)) @ foldl (@) [] (map (map (prod_to_edge G')) [f\<pi>2 ! k]) "
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>1))"
      and s="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1))"
      in subst)
   apply(rename_tac k)(*strict*)
   apply(rule map_foldl)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (map (prod_to_edge G')) (take k f\<pi>2))"
      and s="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2))"
      in subst)
   apply(rename_tac k)(*strict*)
   apply(rule map_foldl)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2))"
      and s="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1))"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(simp (no_asm))
  apply(erule_tac
      x="k"
      in allE)
  apply(erule impE)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      w="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1))"
      and x="map (prod_to_edge G') (foldl (@) [] f\<pi>1) @ c1"
      and v="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2))"
      and y="map (prod_to_edge G') (foldl (@) [] f\<pi>2)@c2"
      in equal_by_embedding_and_AX_equal_length)
      apply(rename_tac k)(*strict*)
      apply(rule_tac
      t="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1)) @ map (prod_to_edge G') (f\<pi>1 ! k)"
      and s="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>1) @ (f\<pi>1 ! k))"
      in ssubst)
       apply(rename_tac k)(*strict*)
       apply(force)
      apply(rename_tac k)(*strict*)
      apply(rule_tac
      t="foldl (@) [] (take k f\<pi>1) @ f\<pi>1 ! k"
      and s="foldl (@) [] (take (Suc k) f\<pi>1)"
      in ssubst)
       apply(rename_tac k)(*strict*)
       apply (metis foldl_tail le_trans less_eq_Suc_le_raw)
      apply(rename_tac k)(*strict*)
      apply(rule prefix_append_bigger)
      apply(rule map_prefix)
      apply(rule foldl_preserves_prefix)
      apply(rule take_is_prefix)
     apply(rename_tac k)(*strict*)
     apply(rule_tac
      t="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2)) @ map (prod_to_edge G') (f\<pi>2 ! k)"
      and s="map (prod_to_edge G') (foldl (@) [] (take k f\<pi>2) @ (f\<pi>2 ! k))"
      in ssubst)
      apply(rename_tac k)(*strict*)
      apply(force)
     apply(rename_tac k)(*strict*)
     apply(rule_tac
      t="foldl (@) [] (take k f\<pi>2) @ f\<pi>2 ! k"
      and s="foldl (@) [] (take (Suc k) f\<pi>2)"
      in ssubst)
      apply(rename_tac k)(*strict*)
      apply (metis foldl_tail le_trans less_eq_Suc_le_raw)
     apply(rename_tac k)(*strict*)
     apply(rule prefix_append_bigger)
     apply(rule map_prefix)
     apply(rule foldl_preserves_prefix)
     apply(rule take_is_prefix)
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(force)
  done

lemma map_foldl_prefix_equal: "
  \<forall>i. i<length f\<pi>1 \<longrightarrow> i<length f\<pi>2 \<longrightarrow> length (f\<pi>1 ! i) = length (f\<pi>2 ! i)
  \<Longrightarrow> map (prod_to_edge G') (foldl (@) [] f\<pi>1) @ c = map (prod_to_edge G') (foldl (@) [] f\<pi>2) @ d
  \<Longrightarrow> map (prod_to_edge G') (foldl (@) [] (take (length f\<pi>2) f\<pi>1)) =
          map (prod_to_edge G') (foldl (@) [] (take (length f\<pi>1) f\<pi>2))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?n2.0="length f\<pi>2"
      and ?n1.0="length f\<pi>1"
      and ?f\<pi>1.0="f\<pi>1"
      and ?f\<pi>2.0="f\<pi>2"
      and k="min(length f\<pi>2)(length f\<pi>1)"
      in map_foldl_prefix_equal_hlp)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "length f\<pi>1 \<le> length f\<pi>2")
   apply(subgoal_tac "min (length f\<pi>2) (length f\<pi>1) = length f\<pi>1")
    apply(rule_tac
      t="take (length f\<pi>2) f\<pi>1"
      and s="f\<pi>1"
      in ssubst)
     apply(rule take_all)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "min (length f\<pi>2) (length f\<pi>1) = length f\<pi>2")
   apply(rule_tac
      t="take (length f\<pi>1) f\<pi>2"
      and s="f\<pi>2"
      in ssubst)
    apply(rule take_all)
    apply(force)
   apply(force)
  apply(force)
  done

definition last_back_state_if_l3_nonterminal :: "
  ('q, 's) DT_l2_l3_nonterminals list
  \<Rightarrow> 'q option"
  where
    "last_back_state_if_l3_nonterminal w \<equiv>
  case w of
  [] \<Rightarrow> None
  | a # w' \<Rightarrow> (
    case last w of
      cons_l2 q A \<Rightarrow> None
      | cons_l3 q1 A q2 \<Rightarrow> Some q2)"

lemma fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal: "
  w1=drop_and_crop w2 n
  \<Longrightarrow> fillOptL w1 (last_back_state_if_l3_nonterminal (take (length w1) w2)) = take (length w1) w2"
  apply(clarsimp)
  apply(simp add: drop_and_crop_def)
  apply(rule_tac
      t="length (cropTol3l2 (butn w2 n))"
      and s="length w2-n"
      in ssubst)
   apply(simp add: cropTol3l2_def butn_def)
   apply(clarsimp)
   apply(force)
  apply(subgoal_tac "take (length w2 - n) w2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(rule_tac
      t="take (length w2 - n) w2"
      and s="[]"
      in ssubst)
    apply(force)
   apply(clarsimp)
   apply(simp add: last_back_state_if_l3_nonterminal_def)
   apply(simp add: fillOptL_def)
   apply(simp add: cropTol3l2_def butn_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="last_back_state_if_l3_nonterminal (w' @ [a'])"
      and s="last_back_state_if_l3_nonterminal ([a'])"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(simp add: last_back_state_if_l3_nonterminal_def)
   apply(case_tac "w'@[a']")
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "list=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' a' a list)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' a' a list)(*strict*)
   apply(erule disjE)
    apply(rename_tac w' a' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: butn_def cropTol3l2_def)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q b)(*strict*)
   apply(simp add: last_back_state_if_l3_nonterminal_def)
   apply(simp add: fillOptL_def cropTol3l2_single_def)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(simp add: last_back_state_if_l3_nonterminal_def)
  apply(simp add: fillOptL_def cropTol3l2_single_def fill_def fillL_def appL_def)
  done

lemma fillOpt_single_with_last_back_state_if_l3_nonterminal: "
  Y1 = fillOpt (hd (cropTol3l2 (Y1 # w))) (last_back_state_if_l3_nonterminal [Y1])"
  apply(case_tac Y1)
   apply(rename_tac q b)(*strict*)
   apply(clarsimp)
   apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def)
  apply(rename_tac q1 b q2)(*strict*)
  apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
  done

lemma fillOptL_with_last_back_state_if_l3_nonterminal_X: "
  w = fillOptL (cropTol3l2 w) (last_back_state_if_l3_nonterminal w)"
  apply(rule_tac
      xs="w"
      in rev_cases)
   apply(clarsimp)
   apply(simp add: fillOptL_def cropTol3l2_def last_back_state_if_l3_nonterminal_def)
  apply(rename_tac ys y)(*strict*)
  apply(simp add: fillOptL_def cropTol3l2_def last_back_state_if_l3_nonterminal_def)
  apply(clarsimp)
  apply(case_tac ys)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(case_tac y)
    apply(rename_tac y q b)(*strict*)
    apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
   apply(rename_tac y q1 b q2)(*strict*)
   apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
   apply(clarsimp)
   apply(rename_tac q1 b q2)(*strict*)
   apply(simp add: fillL_def appL_def last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
  apply(rename_tac ys y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac y a list)(*strict*)
  apply(case_tac y)
   apply(rename_tac y a list q b)(*strict*)
   apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
  apply(rename_tac y a list q1 b q2)(*strict*)
  apply(simp add: last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
  apply(clarsimp)
  apply(rename_tac a list q1 b q2)(*strict*)
  apply(simp add: fillL_def appL_def last_back_state_if_l3_nonterminal_def fillOpt_def cropTol3l2_def cropTol3l2_single_def fill_def)
  done

lemma fillOptL_cropTol3l2_last_back_state_if_l3_nonterminal: "
  fillOptL (cropTol3l2 w) (last_back_state_if_l3_nonterminal w) = w"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: cropTol3l2_def fillOptL_def last_back_state_if_l3_nonterminal_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: cropTol3l2_def)
  apply(rule_tac
      t="last_back_state_if_l3_nonterminal (w' @ [a'])"
      and s="last_back_state_if_l3_nonterminal ([a'])"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(simp add: last_back_state_if_l3_nonterminal_def)
   apply(case_tac "w'@[a']")
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "list=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac w' a' a list)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac w' a' a list)(*strict*)
   apply(erule disjE)
    apply(rename_tac w' a' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: fillOptL_def cropTol3l2_single_def fill_def fillL_def appL_def last_back_state_if_l3_nonterminal_def)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(simp add: fillL_def appL_def fill_def)
  done

definition l3seq_l2end :: "('a,'b)DT_l2_l3_nonterminals list \<Rightarrow> bool" where
  "l3seq_l2end w = (\<forall>w1 x y w2. w=w1@[x,y]@w2 \<longrightarrow> (
  case x of cons_l2 q A \<Rightarrow> False
  | cons_l3 q1 A1 q1' \<Rightarrow> (case y of cons_l2 q A \<Rightarrow> (q1'=q) \<and> w2=[]
  | cons_l3 q2 A2 q2' \<Rightarrow> (q1'=q2))
  ))"

lemma l3seq_l2end_append_decomp2: "
  l3seq_l2end (x@y)
  \<Longrightarrow> l3seq_l2end y"
  apply(simp add: l3seq_l2end_def)
  done

lemma l3seq_l2end_l2_at_end: "
  l3seq_l2end (cons_l2 q a # w)
  \<Longrightarrow> w=[]"
  apply(case_tac w)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(simp add: l3seq_l2end_def)
  apply(erule_tac
      x="[]"
      in allE)
  apply(clarsimp)
  done

definition getTrg :: "('a,'b)DT_l2_l3_nonterminals \<Rightarrow> 'a option" where
  "getTrg X = (case X of cons_l2 q A \<Rightarrow> None | cons_l3 q1 A q2 \<Rightarrow> Some q2)"

definition getSrc :: "('a,'b)DT_l2_l3_nonterminals \<Rightarrow> 'a" where
  "getSrc X = (case X of cons_l2 q A \<Rightarrow> q | cons_l3 q1 A q2 \<Rightarrow> q1)"

lemma l3seq_getSrc_getTrg: "
  l3seq (w1@ x # y # w2)
  \<Longrightarrow> getSrc y = the (getTrg x)"
  apply(simp add: l3seq_def)
  apply(erule_tac
      x="w1"
      in allE)
  apply(clarsimp)
  apply(simp add: getTrg_def getSrc_def)
  apply(case_tac x)
   apply(rename_tac q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2)(*strict*)
  apply(case_tac y)
   apply(rename_tac q2 q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q2 q1 b q2a)(*strict*)
  apply(clarsimp)
  done

lemma l3seq_l2end_getSrc_getTrg: "
  l3seq_l2end (w1@ x # y # w2)
  \<Longrightarrow> getSrc y = the (getTrg x)"
  apply(simp add: l3seq_l2end_def)
  apply(erule_tac
      x="w1"
      in allE)
  apply(clarsimp)
  apply(simp add: getTrg_def getSrc_def)
  apply(case_tac x)
   apply(rename_tac q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2)(*strict*)
  apply(case_tac y)
   apply(rename_tac q2 q b)(*strict*)
   apply(clarsimp)
  apply(rename_tac q2 q1 b q2a)(*strict*)
  apply(clarsimp)
  done

lemma l3seq_append: "
  l3seq x
  \<Longrightarrow> l3seq y
  \<Longrightarrow> (\<forall>q A. cons_l2 q A \<notin> set x)
  \<Longrightarrow> (\<forall>q A. cons_l2 q A \<notin> set y)
  \<Longrightarrow> getTrg (last x) = Some (getSrc (hd y))
  \<Longrightarrow> l3seq (x@y)"
  apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac y)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' a list)(*strict*)
  apply(clarsimp)
  apply(case_tac a')
   apply(rename_tac w' a' a list q b)(*strict*)
   apply(simp add: getTrg_def)
  apply(rename_tac w' a' a list q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2)(*strict*)
  apply(simp add: l3seq_def)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 w1 x y w2)(*strict*)
  apply(subgoal_tac "strict_prefix w1 w' \<or> SSX" for SSX)
   apply(rename_tac w' a list q1 b q2 w1 x y w2)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac w' a list q1 b q2 w1 x y w2)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a list q1 b q2 w1 x y w2)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac a list q1 b q2 w1 x y w2 c)(*strict*)
   apply(case_tac c)
    apply(rename_tac a list q1 b q2 w1 x y w2 c)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list q1 b q2 w1 x y w2 c aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list q1 b q2 w1 x y w2 lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac a list q1 b q2 w1 x y w2 lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac a list q1 b q2 w1 x)(*strict*)
    apply(erule_tac
      x="w1"
      and P="\<lambda>w1a. \<forall>xa y. (\<exists>w2. w1 @ [x, cons_l3 q1 b q2] = w1a @ xa # y # w2) \<longrightarrow> (case xa of cons_l2 q A \<Rightarrow> False | cons_l3 q1 A1 q1' \<Rightarrow> case y of cons_l2 q A \<Rightarrow> False | cons_l3 q2 A2 q2' \<Rightarrow> q1' = q2)"
      in allE)
    apply(rename_tac a list q1 b q2 w1 x)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list q1 b q2 w1 x y w2 lista aa listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list q1 b q2 w1 x y listb)(*strict*)
   apply(erule_tac
      x="w1"
      and P="\<lambda>w1a. \<forall>xa ya. (\<exists>w2. w1 @ x # y # listb @ [cons_l3 q1 b q2] = w1a @ xa # ya # w2) \<longrightarrow> (case xa of cons_l2 q A \<Rightarrow> False | cons_l3 q1 A1 q1' \<Rightarrow> case ya of cons_l2 q A \<Rightarrow> False | cons_l3 q2 A2 q2' \<Rightarrow> q1' = q2)"
      in allE)
   apply(rename_tac a list q1 b q2 w1 x y listb)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 w1 x y w2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 x y w2 c)(*strict*)
  apply(case_tac c)
   apply(rename_tac w' a list q1 b q2 x y w2 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q1 b q2 y w2)(*strict*)
   apply(case_tac y)
    apply(rename_tac w' q1 b q2 y w2 q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q1 b q2 w2 q ba)(*strict*)
    apply(erule_tac
      x="q"
      and P="\<lambda>qa. \<forall>A. (qa = q \<longrightarrow> A \<noteq> ba) \<and> cons_l2 qa A \<notin> set w2"
      in allE)
    apply(erule_tac
      x="ba"
      in allE)
    apply(force)
   apply(rename_tac w' q1 b q2 y w2 q1a ba q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q1 b q2 w2 q1a ba q2a)(*strict*)
   apply(simp add: getSrc_def getTrg_def)
  apply(rename_tac w' a list q1 b q2 x y w2 c aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 x y w2 lista)(*strict*)
  apply(case_tac x)
   apply(rename_tac w' a list q1 b q2 x y w2 lista q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a list q1 b q2 y w2 lista q ba)(*strict*)
   apply(case_tac a)
    apply(rename_tac w' a list q1 b q2 y w2 lista q ba qa bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' list q1 b q2 y w2 lista q ba qa bb)(*strict*)
    apply(erule_tac
      x="qa"
      and P="\<lambda>q. \<forall> A. (q = qa \<longrightarrow> A \<noteq> bb) \<and> cons_l2 q A \<notin> set list"
      in allE)
    apply(erule_tac
      x="bb"
      in allE)
    apply(force)
   apply(rename_tac w' a list q1 b q2 y w2 lista q ba q1a bb q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' list q1 b q2 y w2 lista q ba q1a bb q2a)(*strict*)
   apply(simp add: getSrc_def getTrg_def)
   apply(clarsimp)
   apply(rename_tac w' list q1 b y w2 lista q ba q1a bb q2a)(*strict*)
   apply(erule_tac
      x="lista"
      in allE)+
   apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 x y w2 lista q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 y w2 lista q1a ba q2a)(*strict*)
  apply(case_tac y)
   apply(rename_tac w' a list q1 b q2 y w2 lista q1a ba q2a q bb)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q bb)(*strict*)
   apply(case_tac a)
    apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q bb qa bc)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' list q1 b q2 w2 lista q1a ba q2a q bb qa bc)(*strict*)
    apply(erule_tac
      x="qa"
      and P="\<lambda>q. \<forall> A. (q = qa \<longrightarrow> A \<noteq> bc) \<and> cons_l2 q A \<notin> set list"
      in allE)
    apply(erule_tac
      x="bc"
      in allE)
    apply(force)
   apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q bb q1b bc q2b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' list q1 b q2 w2 lista q1a ba q2a q bb q1b bc q2b)(*strict*)
   apply(simp add: getSrc_def getTrg_def)
   apply(clarsimp)
   apply(rename_tac w' list q1 b w2 lista q1a ba q2a q bb q1b bc q2b)(*strict*)
   apply(erule_tac
      x="lista"
      in allE)+
   apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 y w2 lista q1a ba q2a q1b bb q2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q1b bb q2b)(*strict*)
  apply(case_tac a)
   apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q1b bb q2b q bc)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' list q1 b q2 w2 lista q1a ba q2a q1b bb q2b q bc)(*strict*)
   apply(erule_tac
      x="q"
      and P="\<lambda>qa. \<forall>A. (qa = q \<longrightarrow> A \<noteq> bc) \<and> cons_l2 qa A \<notin> set list"
      in allE)
   apply(erule_tac
      x="bc"
      in allE)
   apply(force)
  apply(rename_tac w' a list q1 b q2 w2 lista q1a ba q2a q1b bb q2b q1c bc q2c)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' list q1 b q2 w2 lista q1a ba q2a q1b bb q2b q1c bc q2c)(*strict*)
  apply(simp add: getSrc_def getTrg_def)
  apply(clarsimp)
  apply(rename_tac w' list q1 b w2 lista q1a ba q2a q1b bb q2b q1c bc q2c)(*strict*)
  apply(erule_tac
      x="lista"
      in allE)+
  apply(clarsimp)
  done

lemma l3seq_l2end_append: "
  l3seq x
  \<Longrightarrow> l3seq_l2end y
  \<Longrightarrow> (\<forall>q A. cons_l2 q A \<notin> set x)
  \<Longrightarrow> getTrg (last x) = Some (getSrc (hd y))
  \<Longrightarrow> l3seq_l2end (x@y)"
  apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(case_tac a')
   apply(rename_tac w' a' q b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q b)(*strict*)
   apply(force)
  apply(rename_tac w' a' q1 b q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' q1 b q2)(*strict*)
  apply(simp add: getTrg_def)
  apply(clarsimp)
  apply(rename_tac w' q1 b)(*strict*)
  apply(simp add: l3seq_l2end_def)
  apply(clarsimp)
  apply(rename_tac w' q1 b w1 x ya w2)(*strict*)
  apply(subgoal_tac "prefix w' w1 \<or> SSX" for SSX)
   apply(rename_tac w' q1 b w1 x ya w2)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac w' q1 b w1 x ya w2)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' q1 b w1 x ya w2)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac w' q1 b x ya w2 c)(*strict*)
   apply(case_tac x)
    apply(rename_tac w' q1 b x ya w2 c q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q1 b ya w2 c q ba)(*strict*)
    apply(case_tac c)
     apply(rename_tac w' q1 b ya w2 c q ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' q1 b ya w2 c q ba a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q1 b y w2 q ba list)(*strict*)
    apply(erule_tac
      x="list"
      in allE)
    apply(clarsimp)
   apply(rename_tac w' q1 b x ya w2 c q1a ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q1 b ya w2 c q1a ba q2)(*strict*)
   apply(case_tac ya)
    apply(rename_tac w' q1 b ya w2 c q1a ba q2 q bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q1 b w2 c q1a ba q2 q bb)(*strict*)
    apply(case_tac c)
     apply(rename_tac w' q1 b w2 c q1a ba q2 q bb)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' w2 q1a ba q bb)(*strict*)
     apply(simp add: getSrc_def)
     apply(case_tac w2)
      apply(rename_tac w' w2 q1a ba q bb)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' w2 q1a ba q bb a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' q1a ba q bb a list)(*strict*)
     apply(erule_tac
      x="[]"
      in allE)
     apply(clarsimp)
    apply(rename_tac w' q1 b w2 c q1a ba q2 q bb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' q1 b w2 q1a ba q2 q bb list)(*strict*)
    apply(erule_tac
      x="list"
      in allE)
    apply(clarsimp)
   apply(rename_tac w' q1 b ya w2 c q1a ba q2 q1b bb q2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q1 b w2 c q1a ba q2 q1b bb q2a)(*strict*)
   apply(case_tac c)
    apply(rename_tac w' q1 b w2 c q1a ba q2 q1b bb q2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' w2 q1a ba q1b bb q2a)(*strict*)
    apply(simp add: getSrc_def)
   apply(rename_tac w' q1 b w2 c q1a ba q2 q1b bb q2a a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' q1 b w2 q1a ba q2 q1b bb q2a list)(*strict*)
   apply(erule_tac
      x="list"
      in allE)
   apply(clarsimp)
  apply(rename_tac w' q1 b w1 x ya w2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac q1 b w1 x ya w2 c)(*strict*)
  apply(case_tac c)
   apply(rename_tac q1 b w1 x ya w2 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 y w2)(*strict*)
   apply(case_tac y)
    apply(rename_tac q1 b w1 y w2 q ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 b w1 w2 q ba)(*strict*)
    apply(simp add: getSrc_def getTrg_def)
    apply(case_tac w2)
     apply(rename_tac q1 b w1 w2 q ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1 b w1 w2 q ba a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac q1 b w1 q ba a list)(*strict*)
    apply(force)
   apply(rename_tac q1 b w1 y w2 q1a ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 w2 q1a ba q2)(*strict*)
   apply(simp add: getSrc_def getTrg_def)
  apply(rename_tac q1 b w1 x ya w2 c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1 b w1 x ya w2 list)(*strict*)
  apply(case_tac list)
   apply(rename_tac q1 b w1 x ya w2 list)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 x)(*strict*)
   apply(case_tac x)
    apply(rename_tac q1 b w1 x q ba)(*strict*)
    apply(force)
   apply(rename_tac q1 b w1 x q1a ba q2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 q1a ba q2)(*strict*)
   apply(simp add: l3seq_def)
   apply(erule_tac
      x="w1"
      in allE)+
   apply(clarsimp)
  apply(rename_tac q1 b w1 x ya w2 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1 b w1 x ya lista)(*strict*)
  apply(case_tac x)
   apply(rename_tac q1 b w1 x ya lista q ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 ya lista q ba)(*strict*)
   apply(force)
  apply(rename_tac q1 b w1 x ya lista q1a ba q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1 b w1 ya lista q1a ba q2)(*strict*)
  apply(case_tac ya)
   apply(rename_tac q1 b w1 ya lista q1a ba q2 q bb)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 b w1 lista q1a ba q2 q bb)(*strict*)
   apply(force)
  apply(rename_tac q1 b w1 ya lista q1a ba q2 q1b bb q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1 b w1 lista q1a ba q2 q1b bb q2a)(*strict*)
  apply(simp add: l3seq_def)
  apply(erule_tac
      x="w1"
      in allE)+
  apply(force)
  done

definition l3_l2_separation :: "
  ('q, 'x) DT_l2_l3_nonterminals list
  \<Rightarrow> bool"
  where
    "l3_l2_separation w \<equiv>
  \<exists>v q A.
    w = v @ [cons_l2 q A]
    \<and> only_l3_nonterminals v"

lemma l3_l2_separation_replace_front: "
  l3_l2_separation (cons_l3 q1 A1 q1' # v1)
  \<Longrightarrow> l3_l2_separation (cons_l3 q2 A2 q2' # v1)"
  apply(simp add: l3_l2_separation_def)
  apply(clarsimp)
  apply(rename_tac v q A)(*strict*)
  apply(subgoal_tac "v1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac v q A)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac v q A)(*strict*)
  apply(erule disjE)
   apply(rename_tac v q A)(*strict*)
   apply(clarsimp)
  apply(rename_tac v q A)(*strict*)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(rule only_l3_nonterminals_replace_front)
  apply(force)
  done

lemma l3_l2_separation_l2_at_front: "
  l3_l2_separation (cons_l2 q A # v)
  \<Longrightarrow> v=[]"
  apply(simp add: l3_l2_separation_def)
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(rule only_l3_nonterminals_l2_at_front)
  apply(force)
  done

lemma l3_l2_separation_single: "
  l3_l2_separation [cons_l2 x y]"
  apply(simp add: only_l3_nonterminals_def l3_l2_separation_def)
  done

lemma l3_l2_separation_l3_at_front: "
  l3_l2_separation (cons_l3 q A q' # v)
  \<Longrightarrow> v\<noteq>[]"
  apply(simp add: l3_l2_separation_def)
  apply(clarsimp)
  done

lemma l3_l2_separation_drop: "
  l3_l2_separation (w@v)
  \<Longrightarrow> v\<noteq>[]
  \<Longrightarrow> l3_l2_separation v"
  apply(simp add: l3_l2_separation_def)
  apply(clarsimp)
  apply(rename_tac va q A)(*strict*)
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac va q A)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac va q A)(*strict*)
  apply(erule disjE)
   apply(rename_tac va q A)(*strict*)
   apply(clarsimp)
  apply(rename_tac va q A)(*strict*)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply (metis only_l3_nonterminals_drop)
  done

lemma l3_l2_separation_append: "
  only_l3_nonterminals w1
  \<Longrightarrow> l3_l2_separation w2
  \<Longrightarrow> w=w1@w2
  \<Longrightarrow> l3_l2_separation w"
  apply(simp add: l3_l2_separation_def only_l3_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac v w1a w2 xA)(*strict*)
  apply(subgoal_tac "prefix w1 w1a \<or> SSX" for SSX)
   apply(rename_tac v w1a w2 xA)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac v w1a w2 xA)(*strict*)
  apply(erule disjE)
   apply(rename_tac v w1a w2 xA)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac v w1a w2 xA)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac v w1 w2 xA c)(*strict*)
  apply(case_tac c)
   apply(rename_tac v w1 w2 xA c)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 xA)(*strict*)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1a. \<forall>w2 xA. w1 = w1a @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1. \<forall>w2a xAa. xA # w2 = w1 @ xAa # w2a \<longrightarrow> (\<exists>q1 A q2. xAa = cons_l3 q1 A q2)"
      in allE)
   apply(clarsimp)
  apply(rename_tac v w1 w2 xA c a list)(*strict*)
  apply(clarsimp)
  done

lemma only_l3_nonterminals_reachable: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> cfgLM.trans_der G' d \<lparr>cfg_conf=[teA (cons_l3   q A q')]\<rparr> \<pi> c'
  \<Longrightarrow> (\<forall>q A. cons_l2 q A \<notin> setA(cfg_conf c'))"
  apply(induct \<pi> arbitrary: c' rule: rev_induct )
   apply(rename_tac c')(*strict*)
   apply(clarsimp)
   apply(rename_tac c' qa Aa)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x xs c')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs c')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs c' e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs c' e)(*strict*)
     apply(force)
    apply(rename_tac x xs c' e)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e)(*strict*)
   apply(force)
  apply(rename_tac x xs c')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 qa Aa c2)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs c' e1 e2 c1 qa Aa c2)(*strict*)
   apply(rule_tac
      t="xs"
      and s="take(length xs)(xs@[x])"
      in ssubst)
    apply(rename_tac x xs c' e1 e2 c1 qa Aa c2)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e1 e2 c1 qa Aa c2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs c' e1 e2 c1 qa Aa)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs c' e1 e2 c1 qa Aa)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e1 e2 c1 qa Aa)(*strict*)
   apply(force)
  apply(rename_tac x xs c' e1 e2 c1 qa Aa c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 qa Aa c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs c' e1 e2 c1 qa Aa c2 l r cfg_confa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs c' e1 e2 c1 qa Aa c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 qa Aa l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs c' e1 e2 qa Aa l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs c' e1 e2 qa Aa l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 qa Aa r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(simp add: simpY)
  apply(case_tac c')
  apply(rename_tac x xs c' e1 e2 qa Aa r l' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e2 qa Aa r l' cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
  apply(subgoal_tac "e2=x")
   apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="length xs"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
       apply(force)
      apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
      apply(force)
     apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
     apply(force)
    apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
    apply(force)
   apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
   apply(force)
  apply(rename_tac x xs e1 e2 qa Aa r l' w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 qa Aa r l' w)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac x xs e1 qa Aa r l')(*strict*)
  apply(thin_tac "d (length xs) = Some (pair e1 \<lparr>cfg_conf = liftB l' @ teA (prod_lhs x) # r\<rparr>)")
  apply(thin_tac "d (Suc (length xs)) = Some (pair (Some x) \<lparr>cfg_conf = liftB l' @ prod_rhs x @ r\<rparr>)")
  apply(thin_tac "cfgLM.belongs G' d")
  apply(thin_tac "get_labels d (Suc (length xs)) = map Some xs @ [Some x]")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA (cons_l3   q A q')]\<rparr>)")
  apply(rename_tac x xs e1 q A r l')(*strict*)
  apply(thin_tac "cfgLM.derivation G' d")
  apply(simp add: simpY)
  apply(rename_tac x q A r)(*strict*)
  apply(subgoal_tac "x \<in> F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G")
   apply(rename_tac x q A r)(*strict*)
   prefer 2
   apply(simp add: cfg_sub_def F_SDPDA_TO_CFG_STD_def)
   apply(force)
  apply(rename_tac x q A r)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x q A r)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
   apply(erule disjE)
    apply(rename_tac x q A r)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q A r xa)(*strict*)
    apply(case_tac "edge_event xa")
     apply(rename_tac x q A r xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x q A r xa a)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
    apply(clarsimp)
   apply(rename_tac x q A r)(*strict*)
   apply(erule disjE)
    apply(rename_tac x q A r)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q A r xa)(*strict*)
    apply(case_tac "edge_push xa")
     apply(rename_tac x q A r xa)(*strict*)
     prefer 2
     apply(rename_tac x q A r xa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x q A r xa)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
   apply(rename_tac x q A r)(*strict*)
   apply(clarsimp)
   apply(rename_tac x q A r xa)(*strict*)
   apply(case_tac "edge_push xa")
    apply(rename_tac x q A r xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x q A r xa a list)(*strict*)
   apply(clarsimp)
   apply(case_tac "edge_event xa")
    apply(rename_tac x q A r xa a list)(*strict*)
    prefer 2
    apply(rename_tac x q A r xa a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x q A r xa a list)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(clarsimp)
  apply(rename_tac x q A r)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_def)
  apply(erule disjE)
   apply(rename_tac x q A r)(*strict*)
   apply(clarsimp)
   apply(rename_tac x q A r xa)(*strict*)
   apply(case_tac "edge_event xa")
    apply(rename_tac x q A r xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x q A r xa a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x q A r)(*strict*)
  apply(erule disjE)
   apply(rename_tac x q A r)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
   apply(clarsimp)
  apply(rename_tac x q A r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x q A r xa)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac x q A r xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x q A r xa a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event xa")
   apply(rename_tac x q A r xa a list)(*strict*)
   prefer 2
   apply(rename_tac x q A r xa a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x q A r xa a list)(*strict*)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule disjE)
   apply(rename_tac x q A r xa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac r xa a list)(*strict*)
   apply(force)
  apply(rename_tac x q A r xa a list)(*strict*)
  apply(force)
  done

lemma only_prods_with_l3_nonterminals_reachable: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> cfgLM.trans_der G' d \<lparr>cfg_conf=[teA (cons_l3   q A q')]\<rparr> \<pi> c'
  \<Longrightarrow> \<forall>i<length \<pi>. \<exists>q A q'. prod_lhs (\<pi> ! i) = cons_l3 q A q'"
  apply(induct \<pi> arbitrary: c' rule: rev_induct)
   apply(rename_tac c')(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs c')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' i)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs c' i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs c' i e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs c' i e)(*strict*)
     apply(force)
    apply(rename_tac x xs c' i e)(*strict*)
    apply(force)
   apply(rename_tac x xs c' i e)(*strict*)
   apply(force)
  apply(rename_tac x xs c' i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
   apply(rule_tac
      t="xs"
      and s="take(length xs)(xs@[x])"
      in ssubst)
    apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs c' i e1 e2 c1)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs c' i e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac x xs c' i e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
  apply(case_tac "i<length xs")
   apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac x xs c' i e1 e2 c1 c2 qa Aa q'a)(*strict*)
   apply(rule_tac
      t="(xs @ [x]) ! i"
      and s="xs!i"
      in ssubst)
    apply(rename_tac x xs c' i e1 e2 c1 c2 qa Aa q'a)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac x xs c' i e1 e2 c1 c2 qa Aa q'a)(*strict*)
   apply(force)
  apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "i=length xs")
   apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs c' i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2=x")
   apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="length xs"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x xs c' e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 c1 c2)(*strict*)
  apply(subgoal_tac "(\<forall>q A. cons_l2 q A \<notin> setA(cfg_conf c1))")
   apply(rename_tac x xs c' e1 c1 c2)(*strict*)
   apply(case_tac "prod_lhs x")
    apply(rename_tac x xs c' e1 c1 c2 qa b)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x xs c' e1 c1 c2 qa b l r)(*strict*)
    apply(simp add: simpY)
    apply(force)
   apply(rename_tac x xs c' e1 c1 c2 q1 b q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs c' e1 c1 c2)(*strict*)
  apply(rule_tac
      d="d"
      and \<pi>="xs"
      and c'="c1"
      and q="q"
      and A="A"
      and q'="q'"
      in only_l3_nonterminals_reachable)
       apply(rename_tac x xs c' e1 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac x xs c' e1 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac x xs c' e1 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x xs c' e1 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e1 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x xs c' e1 c1 c2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
   apply(rename_tac x xs c' e1 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x xs c' e1 c1 c2)(*strict*)
  apply(force)
  done

lemma cfgLM_preserves_liftB_liftA_splitting: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> cfgLM.trans_der G' d c \<pi> c'
  \<Longrightarrow> (\<exists>w1 w2. cfg_conf c=liftB w1@liftA w2)
  \<Longrightarrow> (\<exists>w1 w2. cfg_conf c'=liftB w1@liftA w2)"
  apply(induct \<pi> arbitrary: c' d rule: rev_induct)
   apply(rename_tac c' d)(*strict*)
   apply(clarsimp)
   apply(rename_tac c' d w1 w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x xs c' d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs c' d w1 w2)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs c' d w1 w2 e)(*strict*)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs c' d w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac x xs c' d w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac x xs c' d w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac x xs c' d w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs c' d w1 w2 e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs c' d w1 w2 e1 e2 c1 c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs c' d w1 w2 e1 e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs c' d w1 w2 e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac x xs c' d w1 w2 e1 e2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 r l' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w)(*strict*)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftB l' @ teA A # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="d"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs c' d w1 w2 e1 r l' A w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs c' d w1 w2 e1 r l' A w)(*strict*)
    apply(force)
   apply(rename_tac x xs c' d w1 w2 e1 r l' A w)(*strict*)
   apply(force)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a w2a)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a)(*strict*)
   apply (metis append_Nil2 list.simps(3) maximalPrefixB_liftB maximalPrefixB_drop_liftB maximalPrefixB_front self_append_conv)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a w2a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a a list)(*strict*)
  apply(subgoal_tac "l'=w1a")
   apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs c' d w1 w2 e1 w w1a a list)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs d w1 w2 e1 w w1a a list)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = a, prod_rhs = w\<rparr>"
      in ballE)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac x xs d w1 w2 e1 w w1a a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs d w1 w2 e1 w1a a list)(*strict*)
     apply(force)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list b A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac x xs d w1 w2 e1 w w1a a list b A B)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs d w1 w2 e1 w1a list b A B)(*strict*)
     apply(rule_tac
      x="w1a@[b]"
      in exI)
     apply(rule_tac
      x="B#list"
      in exI)
     apply(simp add: simpY)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list b A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list A B)(*strict*)
    apply(erule disjE)
     apply(rename_tac x xs d w1 w2 e1 w w1a a list A B)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs d w1 w2 e1 w1a list A B)(*strict*)
     apply(rule_tac
      x="w1a"
      in exI)
     apply(rule_tac
      x="B#list"
      in exI)
     apply(simp add: simpY)
    apply(rename_tac x xs d w1 w2 e1 w w1a a list A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs d w1 w2 e1 w1a list A B C)(*strict*)
    apply(rule_tac
      x="w1a"
      in exI)
    apply(rule_tac
      x="B#C#list"
      in exI)
    apply(simp add: simpY)
   apply(rename_tac x xs d w1 w2 e1 w w1a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs c' d w1 w2 e1 r l' A w w1a a list)(*strict*)
  apply (metis liftA.simps(2) append_Nil2 maximalPrefixB_liftA maximalPrefixB_drop_liftB maximalPrefixB_front)
  done

lemma l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2: "
  \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l2 G
  \<Longrightarrow> Q"
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "edge_event x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(erule disjE)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event x")
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(rename_tac x a list aa)(*strict*)
  apply(clarsimp)
  done

lemma only_cfgLM_accessible_productions: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfg_productions G' \<subseteq> cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G)"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_productions_def)
  apply(simp add: cfgLM.get_accessible_destinations_def cfg_get_destinations_def)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: cfg_destination_def)
   apply(rule disjI2)
   apply(rule inMap)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "prod_lhs x \<in> cfgLM_accessible_nonterminals G'")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def F_SDPDA_TO_CFG_STD_def cfg_sub_def)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'")
  apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac x d n c w1 w2 a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n c w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 option)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 option cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = liftB w1 @ teA (prod_lhs x) # w2\<rparr> x \<lparr>cfg_conf = liftB w1 @ (prod_rhs x) @ w2\<rparr>) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(rule_tac cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (rule cfg_sub_preserves_cfgLM_derivation_initial)
      apply(rename_tac x d n w1 w2 e)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply (rule_tac
      G'="G'"
      in cfg_sub_preserves_cfgLM_derivation)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac x d n w1 w2 e)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB w1"
      in exI)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="Some x"
      in exI)
  apply(simp add: derivation_append_def der2_def)
  done

lemma cfgLM_positions_remain_compatible_l3l3: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> cfgLM.derivation G' d1
  \<Longrightarrow> cfgLM.derivation G' d2
  \<Longrightarrow> cfgLM.belongs G' d1
  \<Longrightarrow> cfgLM.belongs G' d2
  \<Longrightarrow> d1 0 = Some (pair None \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr>)
  \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr>)
  \<Longrightarrow> d1 n = Some (pair e1 \<lparr>cfg_conf=liftB v1@liftA w1\<rparr>)
  \<Longrightarrow> d2 n = Some (pair e2 \<lparr>cfg_conf=liftB v2@liftA w2\<rparr>)
  \<Longrightarrow> v1@x1=v2@x2
  \<Longrightarrow> (\<forall>k. Suc 0\<le>k\<and>k\<le>n \<longrightarrow>
  F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d1 k)))
  = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d2 k))))
  \<and> v1=v2
  \<and> l3seq w1
  \<and> l3seq w2
  \<and> (\<forall>q A. cons_l2 q A \<notin> set w1)
  \<and> (\<forall>q A. cons_l2 q A \<notin> set w2)
  \<and> equal_stacks w1 w2
  \<and> equal_front_states (take (Suc 0) w1) (take (Suc 0) w2)
  \<and> length w1=length w2"
  apply(induct n arbitrary: e1 e2 v1 v2 w1 w2 x1 x2)
   apply(rename_tac e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
   apply(case_tac v1)
    apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
    prefer 2
    apply(rename_tac v1 v2 w1 w2 x1 x2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w1 w2)(*strict*)
   apply(case_tac w1)
    apply(rename_tac v2 w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w1 w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w2 list)(*strict*)
   apply(case_tac list)
    apply(rename_tac v2 w2 list)(*strict*)
    prefer 2
    apply(rename_tac v2 w2 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w2 list)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w2)(*strict*)
   apply(case_tac v2)
    apply(rename_tac v2 w2)(*strict*)
    prefer 2
    apply(rename_tac v2 w2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2)(*strict*)
   apply(case_tac w2)
    apply(rename_tac w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    prefer 2
    apply(rename_tac list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
   apply(simp add: l3seq_def equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n = Some (pair e1 c1) \<and> d1 (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2")
   apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 n = Some (pair e1 c1) \<and> d2 (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2")
   apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
     apply(force)
    apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
    apply(force)
   apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
   apply(force)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac c1a)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra cfg_confa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs e2a = liftB w1 @ liftA w2")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="e2a"
      in ballE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
    apply(rule_tac
      x="[b]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a r e1 e2b ra l' l'a Aa B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs e2b = liftB w1 @ liftA w2")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="e2b"
      in ballE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
    apply(rule_tac
      x="[b]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 ra l' l'a w1a w2a Aa B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(subgoal_tac "(\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = liftB l' @ teA (prod_lhs e2a) # r\<rparr>=liftB w1@liftA w2)")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and c="\<lparr>cfg_conf = [teA (cons_l3   q A q1)]\<rparr>"
      and c'="\<lparr>cfg_conf = liftB l' @ teA (prod_lhs e2a) # r\<rparr>"
      and \<pi>="map the (get_labels d1 n)"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
         apply(force)
        apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
        apply(force)
       apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
       apply(force)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      t="length (get_labels d1 n)"
      and s="n"
      in ssubst)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[cons_l3 q A q1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(subgoal_tac "(\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = liftB l'a @ teA (prod_lhs e2b) # ra\<rparr>=liftB w1@liftA w2)")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and c="\<lparr>cfg_conf = [teA (cons_l3   q A q2)]\<rparr>"
      and c'="\<lparr>cfg_conf = liftB l'a @ teA (prod_lhs e2b) # ra\<rparr>"
      and \<pi>="map the (get_labels d2 n)"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
         apply(force)
        apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
        apply(force)
       apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
       apply(force)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      t="length (get_labels d2 n)"
      and s="n"
      in ssubst)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[cons_l3 q A q2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(subgoal_tac "l'=w1c")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(subgoal_tac "l'a=w1d")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(case_tac w2c)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list)(*strict*)
  apply(case_tac w2d)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "v2=w1d@w1b")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB v2 @ liftA w2 = liftB (w1d @ w1b) @ liftA (w2b @ lista)")
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
    apply(thin_tac "liftB v2 @ liftA w2 = liftB w1d @ liftB w1b @ liftA w2b @ liftA lista")
    apply (metis liftA_commutes_over_concat liftB_liftA_inj1)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   apply(simp add: simpY)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "v1=w1c@w1a")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB v1 @ liftA w1 = liftB (w1c @ w1a) @ liftA (w2a @ list)")
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
    apply(thin_tac "liftB v1 @ liftA w1 = liftB w1c @ liftB w1a @ liftA w2a @ liftA list")
    apply (metis liftA_commutes_over_concat liftB_liftA_inj1)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   apply(simp add: simpY)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(simp add: simpY)
  apply(subgoal_tac "w2=w2b@lista")
   apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: simpY)
  apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "w1=w2a@list")
   apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: simpY)
  apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(thin_tac "liftA (w2b @ lista) = liftA w2b @ liftA lista")
  apply(thin_tac "liftA (w2a @ list) = liftA w2a @ liftA list")
  apply(rename_tac e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule_tac
      x="\<alpha>1"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2"
      in meta_allE)
  apply(erule_tac
      x="prod_lhs e1'#\<beta>1"
      in meta_allE)
  apply(erule_tac
      x="prod_lhs e2'#\<beta>2"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>1'@x1"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2'@x2"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(rename_tac \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2)(*strict*)
  apply(case_tac e1')
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac e2')
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
  apply(rename_tac A1 w1 A2 w2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 w1 A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2)(*strict*)
  apply(case_tac A1)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 qa b)(*strict*)
   apply(erule_tac
      x="qa"
      in allE)+
   apply(erule_tac
      x="b"
      in allE)+
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a)(*strict*)
  apply(case_tac A2)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a qa ba)(*strict*)
   apply(erule_tac
      x="qa"
      in allE)+
   apply(erule_tac
      x="ba"
      in allE)+
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a q1aa ba q2aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 q1a b q2a q1aa ba q2aa)(*strict*)
  apply(rename_tac qx1 A1 q1' qx2 A2 q2')
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
  apply(subgoal_tac "qx1=qx2 \<and> A1=A2")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
    apply(simp add: l3seq_def equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   apply(simp add: equal_stacks_def equal_stack_def)
   apply(erule_tac
      x="0"
      and P="\<lambda>X. X < Suc (length \<beta>2) \<longrightarrow> (let cmp = case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q1 A q2. A) in cmp ((cons_l3 qx1 A1 q1' # \<beta>1) ! X) = cmp ((cons_l3 qx2 A2 q2' # \<beta>2) ! X))"
      in allE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 q1' qx2 A2 q2')(*strict*)
  apply(rename_tac p1 p B p2)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(subgoal_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(subgoal_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G"
      in disjE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "k=Suc n")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(simp add: get_label_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G. \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> (case edge_event x of None \<Rightarrow> {} | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G))"
      in disjE)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*read1/read1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_event xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
     apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
          apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
         apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule only_cfgLM_accessible_productions)
              apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
              apply(force)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
       apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
     apply(simp add: prefix_def)
     apply(simp add: option_to_list_def)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
     apply(case_tac "\<alpha>1")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
      apply(case_tac e1'\<beta>)
       apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
       apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a ab list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a ab list)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
     apply(case_tac "\<alpha>2")
      apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
      apply(case_tac e2'\<beta>)
       apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
       apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list ab lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list ab lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*read1/pop1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_push xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
          apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
         apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule only_cfgLM_accessible_productions)
              apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
              apply(force)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
     apply(simp add: option_to_list_def prefix_def)
    (*read1/push1*)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     prefer 2
     apply(rule valid_simple_dpda_edge_alt)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     prefer 2
     apply(rule valid_simple_dpda_edge_alt)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(case_tac "edge_event x")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(case_tac "edge_push xa")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
    apply(clarsimp)
    apply(case_tac "edge_event xa")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
     prefer 2
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list ab)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
         apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
        apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule only_cfgLM_accessible_productions)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(simp add: option_to_list_def prefix_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G. \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> (case edge_event x of None \<Rightarrow> {} | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G))"
      in disjE)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*pop1/read1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_push xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
   apply(rule sym)
   apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
        apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
       apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in bexI)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule only_cfgLM_accessible_productions)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(simp add: option_to_list_def prefix_def)
  (*push1/read1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_event x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list ab)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)+
  (*pop1/pop1*)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(case_tac "edge_push x")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    prefer 2
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(case_tac "edge_push xa")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    prefer 2
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
        apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
       apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule only_cfgLM_accessible_productions)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(simp add: option_to_list_def prefix_def)
  (*pop1/push1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)
  (*push1/pop1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_event x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  (*push1/push1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event x")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  prefer 2
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_push xa")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  apply(case_tac "edge_event xa")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  prefer 2
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
      apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
     apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule only_cfgLM_accessible_productions)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "\<forall>k. Suc 0 \<le> k \<and> k \<le> n \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the (get_label (d1 k))) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the (get_label (d2 k)))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule_tac
    x="Suc n"
    in allE)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta SSG. edge_event x \<noteq> None \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<or> edge_event x = None \<and> edge_push x = [] \<and> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<or> edge_event x = None \<and> edge_push x \<noteq> [] \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG)) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG))) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG) \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG)" for SSG SSe2 SSe1)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  prefer 2
  apply(rule_tac
    ?e1.0="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and ?e2.0="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_equal_then_from_special_sets)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G")
  apply(thin_tac "F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "cfgLM.derivation G' d1")
  apply(thin_tac "cfgLM.derivation G' d2")
  apply(thin_tac "cfgLM.belongs G' d1")
  apply(thin_tac "cfgLM.belongs G' d2")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teA (cons_l3   q A q1)]\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = [teA (cons_l3   q A q2)]\<rparr>)")
  apply(thin_tac "d1 (Suc n) = Some (pair (Some \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>) \<lparr>cfg_conf = liftB \<alpha> @ liftB \<alpha>1 @ liftA e1'\<beta> @ liftA \<beta>1\<rparr>)")
  apply(thin_tac "d2 (Suc n) = Some (pair (Some \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>) \<lparr>cfg_conf = liftB \<alpha> @ liftB \<alpha>2 @ liftA e2'\<beta> @ liftA \<beta>2\<rparr>)")
  apply(thin_tac "d1 n = Some (pair e1 \<lparr>cfg_conf = liftB \<alpha> @ teA (cons_l3   p B p1) # liftA \<beta>1\<rparr>)")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> cfg_productions G'")
  apply(thin_tac "d2 n = Some (pair e2 \<lparr>cfg_conf = liftB \<alpha> @ teA (cons_l3   p B p2) # liftA \<beta>2\<rparr>)")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> cfg_productions G'")
  apply(erule disjE)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(erule_tac
    P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G)"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "\<alpha>2")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac e2'\<beta>)
   apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "\<alpha>1")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac e1'\<beta>)
   apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "e1'\<beta>")
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "e2'\<beta>")
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(thin_tac "l3seq (cons_l3   (edge_src x) (edge_pop x ! 0) p2 # \<beta>2)")
  apply(rule l3seq_change_initial_state)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(thin_tac "l3seq (cons_l3   (edge_src x) (edge_pop x ! 0) p1 # \<beta>1)")
  apply(rule l3seq_change_initial_state)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i)(*strict*)
  apply(simp add: Let_def)
  apply(erule_tac
    x="i"
    in allE)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(force)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(force)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule_tac
    P=" edge_event x = None \<and> edge_push x = [] \<and> \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "\<alpha>1=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "e1'\<beta>=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "\<alpha>2=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "e2'\<beta>=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule l3seq_drop_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule l3seq_drop_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 i)(*strict*)
  apply(simp add: Let_def)
  apply(case_tac \<beta>1)
   apply(rename_tac \<beta>1 \<beta>2 x s1 i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 i a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 i a list)(*strict*)
  apply(case_tac \<beta>2)
   apply(rename_tac \<beta>2 x s1 i a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 i a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 i a list aa lista)(*strict*)
  apply(erule_tac
    x="Suc i"
    in allE)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(simp add: equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(simp add: Let_def)
  apply(case_tac \<beta>1)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 a list)(*strict*)
  apply(case_tac \<beta>2)
  apply(rename_tac \<beta>2 x s1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 a list aa lista)(*strict*)
  apply(case_tac a)
  apply(rename_tac x s1 a list aa lista q b)(*strict*)
  apply(force)
  apply(rename_tac x s1 a list aa lista q1 b q2)(*strict*)
  apply(case_tac aa)
  apply(rename_tac x s1 a list aa lista q1 b q2 q ba)(*strict*)
  apply(force)
  apply(rename_tac x s1 a list aa lista q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 list lista q1 b q2 q1a ba q2a)(*strict*)
  apply(simp add: l3seq_def)
  apply(erule_tac
    x="[]"
    in allE)+
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(erule_tac
    P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states G)"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac \<alpha>2)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  prefer 2
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac e2'\<beta>)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(case_tac lista)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  prefer 2
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac \<alpha>1)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  prefer 2
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac e1'\<beta>)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(case_tac lista)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  prefer 2
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule l3_seq_add_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule l3_seq_add_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i)(*strict*)
  apply(simp add: Let_def)
  apply(case_tac i)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nata)(*strict*)
  apply(erule_tac
    x="Suc nata"
    in allE)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(simp add: equal_front_states_def equal_front_state_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  done

lemma l2_production_not_in_F_SDPDA_TO_CFG_STD__edges_l3: "
  \<lparr>prod_lhs = cons_l2 p B, prod_rhs = liftB \<alpha> @ liftA \<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G
  \<Longrightarrow> Q"
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "edge_event x")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "edge_push x")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event x")
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac x a list aa)(*strict*)
  apply(clarsimp)
  done

lemma compatible_l3_productions_same_nonterminal_length_rhs: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<pi>1 = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<pi>2
  \<Longrightarrow> prod_lhs \<pi>1 = cons_l3 q1 A1 q1'
  \<Longrightarrow> prod_lhs \<pi>2 = cons_l3 q2 A2 q2'
  \<Longrightarrow> prod_rhs \<pi>1 = liftB x1 @ liftA y1
  \<Longrightarrow> prod_rhs \<pi>2 = liftB x2 @ liftA y2
  \<Longrightarrow> \<pi>1 \<in> cfg_productions G'
  \<Longrightarrow> \<pi>2 \<in> cfg_productions G'
  \<Longrightarrow> length y1=length y2"
  apply(subgoal_tac "(\<exists>x\<in> epda_delta SSG. edge_event x \<noteq> None \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<or> edge_event x = None \<and> edge_push x = [] \<and> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<or> edge_event x = None \<and> edge_push x \<noteq> [] \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG)) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG))) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG) \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG)" for SSG SSe1 SSe2)
   prefer 2
   apply(rule_tac
      ?e1.0="\<pi>1"
      and ?e2.0="\<pi>2"
      in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_equal_then_from_special_sets)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
     apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
    apply(force)
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(force)
  apply(erule disjE)
   prefer 2
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(erule_tac
      P="\<pi>1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G)"
      in disjE)
    apply(rename_tac x y)(*strict*)
    apply(erule disjE)
     apply(rename_tac x y)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
     apply(clarsimp)
     apply(case_tac x1)
      apply(rename_tac x y)(*strict*)
      apply(clarsimp)
      apply(case_tac y1)
       apply(rename_tac x y)(*strict*)
       apply(clarsimp)
      apply(rename_tac x y a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac x y a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac x a list)(*strict*)
      prefer 2
      apply(rename_tac x a list aa lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a)(*strict*)
     apply(case_tac y1)
      apply(rename_tac x a)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac x a list)(*strict*)
      prefer 2
      apply(rename_tac x a list aa lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a)(*strict*)
     apply(case_tac x2)
      apply(rename_tac x a)(*strict*)
      apply(clarsimp)
      apply(case_tac y2)
       apply(rename_tac x a)(*strict*)
       apply(clarsimp)
      apply(rename_tac x a aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x aa list)(*strict*)
     apply(case_tac list)
      apply(rename_tac x aa list)(*strict*)
      prefer 2
      apply(rename_tac x aa list a lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac x aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x aa)(*strict*)
     apply(case_tac y2)
      apply(rename_tac x aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x aa a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x aa list)(*strict*)
     apply(case_tac list)
      apply(rename_tac x aa list)(*strict*)
      prefer 2
      apply(rename_tac x aa list a lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac x aa list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x y)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
   apply(rename_tac x y)(*strict*)
   apply(erule disjE)
    apply(rename_tac x y)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
   apply(rename_tac x y)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
   apply(clarsimp)
   apply(case_tac y1)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(case_tac y2)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      P="\<pi>1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states G)"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(case_tac x1)
     apply(rename_tac x qs qsa)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(clarsimp)
    apply(case_tac x2)
     apply(rename_tac x qs qsa)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(clarsimp)
    apply(case_tac y1)
     apply(rename_tac x qs qsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs qsa list)(*strict*)
    apply(case_tac list)
     apply(rename_tac x qs qsa list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs qsa lista)(*strict*)
    apply(case_tac lista)
     apply(rename_tac x qs qsa lista)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa lista a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(case_tac y2)
     apply(rename_tac x qs qsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs qsa list)(*strict*)
    apply(case_tac list)
     apply(rename_tac x qs qsa list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs qsa lista)(*strict*)
    apply(case_tac lista)
     apply(rename_tac x qs qsa lista)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa lista a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule_tac
      P="\<pi>1 = \<lparr>prod_lhs = cons_l2 (edge_src x) (edge_pop x ! 0), prod_rhs = [teA (cons_l2   (edge_trg x) (edge_push x ! 0))]\<rparr>"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma compatible_l3_productions_same_nonterminal_rhs_are_equal: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<pi>1 = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<pi>2
  \<Longrightarrow> prod_lhs \<pi>1 = cons_l3 q1 A1 q1'
  \<Longrightarrow> prod_lhs \<pi>2 = cons_l3 q2 A2 q2'
  \<Longrightarrow> prod_rhs \<pi>1 = liftB x1 @ liftA y
  \<Longrightarrow> prod_rhs \<pi>2 = liftB x2 @ liftA y
  \<Longrightarrow> \<pi>1 \<in> cfg_productions G'
  \<Longrightarrow> \<pi>2 \<in> cfg_productions G'
  \<Longrightarrow> \<pi>1=\<pi>2"
  apply(subgoal_tac "(\<exists>x\<in> epda_delta SSG. edge_event x \<noteq> None \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<or> edge_event x = None \<and> edge_push x = [] \<and> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<or> edge_event x = None \<and> edge_push x \<noteq> [] \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG)) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG))) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG) \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG)" for SSG SSe1 SSe2)
   prefer 2
   apply(rule_tac
      ?e1.0="\<pi>1"
      and ?e2.0="\<pi>2"
      in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_equal_then_from_special_sets)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
     apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
    apply(force)
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(force)
  apply(erule disjE)
   prefer 2
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x ya)(*strict*)
   apply(erule_tac
      P="\<pi>1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G)"
      in disjE)
    apply(rename_tac x ya)(*strict*)
    apply(erule disjE)
     apply(rename_tac x ya)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
     apply(clarsimp)
     apply(case_tac x1)
      apply(rename_tac x ya)(*strict*)
      apply(clarsimp)
      apply(case_tac y)
       apply(rename_tac x ya)(*strict*)
       apply(clarsimp)
      apply(rename_tac x ya a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac x ya a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac x a list)(*strict*)
      prefer 2
      apply(rename_tac x a list aa lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x a)(*strict*)
     apply(case_tac y)
      apply(rename_tac x a)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a aa list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
   apply(rename_tac x ya)(*strict*)
   apply(erule disjE)
    apply(rename_tac x ya)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
   apply(rename_tac x ya)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      P="\<pi>1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states G)"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(case_tac x1)
     apply(rename_tac x qs qsa)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(clarsimp)
    apply(case_tac x2)
     apply(rename_tac x qs qsa)(*strict*)
     prefer 2
     apply(rename_tac x qs qsa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
    apply(case_tac y)
     apply(rename_tac x qs qsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs qsa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x qs list)(*strict*)
    apply(case_tac list)
     apply(rename_tac x qs list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x qs list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(erule_tac
      P="\<exists>qs qt. \<pi>2 = \<lparr>prod_lhs = cons_l3 (edge_src x) (edge_pop x ! 0) qt, prod_rhs = [teA (cons_l3   (edge_trg x) (edge_push x ! 0) qs), teA (cons_l3   qs (edge_pop x ! 0) qt)]\<rparr> \<and> qs \<in> epda_states G \<and> qt \<in> epda_states G"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x qs)(*strict*)
   apply(erule disjE)
    apply(rename_tac x qs)(*strict*)
    apply(clarsimp)
   apply(rename_tac x qs)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      P="\<pi>1 = \<lparr>prod_lhs = cons_l2 (edge_src x) (edge_pop x ! 0), prod_rhs = [teA (cons_l2   (edge_trg x) (edge_push x ! 0))]\<rparr>"
      in disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma eliminating_derivations_are_equal_with_differing_future1: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> length \<pi>1 \<le> length \<pi>2
  \<Longrightarrow> \<forall>i<length \<pi>1. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1!i) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2!i)
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<pi>1 = take (length \<pi>1) \<pi>2"
  apply(subgoal_tac "\<forall>i<length \<pi>1. \<exists>q A q'. prod_lhs (\<pi>1!i) = cons_l3 q A q'")
   prefer 2
   apply(rule only_prods_with_l3_nonterminals_reachable)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<forall>i<length \<pi>2. \<exists>q A q'. prod_lhs (\<pi>2!i) = cons_l3 q A q'")
   prefer 2
   apply(rule only_prods_with_l3_nonterminals_reachable)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "set \<pi>1 \<subseteq> cfg_productions G'")
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      w="\<pi>1"
      and x="x"
      in set_elem_nth)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="cfg_productions G'"
      and s="cfg_step_labels G'"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(simp add: cfg_step_labels_def)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac i e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length \<pi>1"
      in cfgLM.pre_some_position_is_some_position_prime)
       apply(rename_tac i e ea)(*strict*)
       apply(force)
      apply(rename_tac i e ea)(*strict*)
      apply(force)
     apply(rename_tac i e ea)(*strict*)
     apply(force)
    apply(rename_tac i e ea)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e c)(*strict*)
   apply(subgoal_tac "e=\<pi>1!i")
    apply(rename_tac i e c)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="i"
      in cfgLM.trans_der_getLabel_at_pos)
        apply(rename_tac i e c)(*strict*)
        apply(force)
       apply(rename_tac i e c)(*strict*)
       apply(force)
      apply(rename_tac i e c)(*strict*)
      apply(force)
     apply(rename_tac i e c)(*strict*)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgLM.belongs_step_labels)
    apply(rename_tac i c)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac i c)(*strict*)
   apply(force)
  apply(subgoal_tac "set \<pi>2 \<subseteq> cfg_productions G'")
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      w="\<pi>2"
      and x="x"
      in set_elem_nth)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="cfg_productions G'"
      and s="cfg_step_labels G'"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(simp add: cfg_step_labels_def)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac i e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length \<pi>2"
      in cfgLM.pre_some_position_is_some_position_prime)
       apply(rename_tac i e ea)(*strict*)
       apply(force)
      apply(rename_tac i e ea)(*strict*)
      apply(force)
     apply(rename_tac i e ea)(*strict*)
     apply(force)
    apply(rename_tac i e ea)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e c)(*strict*)
   apply(subgoal_tac "e=\<pi>2!i")
    apply(rename_tac i e c)(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="i"
      in cfgLM.trans_der_getLabel_at_pos)
        apply(rename_tac i e c)(*strict*)
        apply(force)
       apply(rename_tac i e c)(*strict*)
       apply(force)
      apply(rename_tac i e c)(*strict*)
      apply(force)
     apply(rename_tac i e c)(*strict*)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c)(*strict*)
   apply(rule_tac
      d="d2"
      in cfgLM.belongs_step_labels)
    apply(rename_tac i c)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac i c)(*strict*)
   apply(force)
  apply(subgoal_tac "[cons_l3 q A q1]=[cons_l3 q A q2] \<and> \<pi>1 = take (length \<pi>1) \<pi>2")
   prefer 2
   apply(rule_tac
      G="G'"
      and ?\<pi>3.0="drop (length \<pi>1) \<pi>2"
      and ?d2.0="d2"
      and ?\<alpha>1.0="[]"
      and ?\<alpha>1'.0="\<alpha>1"
      and ?\<alpha>2.0="[]"
      and ?\<alpha>2'.0="\<alpha>2"
      in equal_elimination_for_equal_nonterminals_prime_prime_prime)
          apply(force)
         apply(force)
        apply(force)
       apply(clarsimp)
      apply(force)
     apply(clarsimp)
     apply(rename_tac k x1 x2 y1 y2)(*strict*)
     apply(case_tac "\<pi>1!k")
     apply(rename_tac k x1 x2 y1 y2 prod_lhsa prod_rhsa)(*strict*)
     apply(case_tac "\<pi>2!k")
     apply(rename_tac k x1 x2 y1 y2 prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
     apply(rename_tac A1 w1 A2 w2)
     apply(rename_tac k x1 x2 y1 y2 A1 w1 A2 w2)(*strict*)
     apply(clarsimp)
     apply(rename_tac k x1 x2 y1 y2 A1 A2)(*strict*)
     apply(erule_tac
      x="k"
      and P="\<lambda>k. k < length \<pi>1 \<longrightarrow> (\<exists>q A q'. prod_lhs (\<pi>1 ! k) = cons_l3 q A q')"
      in allE)
     apply(erule_tac
      x="k"
      and P="\<lambda>k. k < length \<pi>2 \<longrightarrow> (\<exists>q A q'. prod_lhs (\<pi>2 ! k) = cons_l3 q A q')"
      in allE)
     apply(clarsimp)
     apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
     apply(rule_tac
      ?\<pi>1.0="\<pi>1!k"
      and ?\<pi>2.0="\<pi>2!k"
      in compatible_l3_productions_same_nonterminal_length_rhs)
               apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
               apply(force)
              apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
              apply(force)
             apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
             apply(force)
            apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
            apply(force)
           apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
           apply(force)
          apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
          apply(force)
         apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
         apply(force)
        apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
        apply(force)
       apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
       apply(force)
      apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
      apply(rule_tac
      A="set \<pi>1"
      in set_mp)
       apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
       apply(force)
      apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
      apply(rule nth_mem)
      apply(force)
     apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
     apply(rule_tac
      A="set \<pi>2"
      in set_mp)
      apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
      apply(force)
     apply(rename_tac k x1 x2 y1 y2 qa qaa Aa Aaa q' q'a)(*strict*)
     apply(rule nth_mem)
     apply(force)
    apply(clarsimp)
    apply(rename_tac k x1 x2 y1)(*strict*)
    apply(erule_tac
      x="k"
      and P="\<lambda>k. k < length \<pi>1 \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1 ! k) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2 ! k)"
      in allE)
    apply(erule_tac
      x="k"
      and P="\<lambda>k. k < length \<pi>1 \<longrightarrow> (\<exists>q A q'. prod_lhs (\<pi>1 ! k) = cons_l3 q A q')"
      in allE)
    apply(erule_tac
      x="k"
      in allE)
    apply(clarsimp)
    apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
    apply(rule compatible_l3_productions_same_nonterminal_rhs_are_equal)
              apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
              apply(force)
             apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
             apply(force)
            apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
            apply(force)
           apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
           apply(force)
          apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
          apply(force)
         apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
         apply(force)
        apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
        apply(force)
       apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
       apply(force)
      apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
      apply(force)
     apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
     apply(force)
    apply(rename_tac k x1 x2 y1 qa qaa Aa Aaa q' q'a)(*strict*)
    apply(force)
   apply(force)
  apply(force)
  done

lemma eliminating_derivations_are_equal_with_differing_future2: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> length \<pi>1 \<le> length \<pi>2
  \<Longrightarrow> \<forall>i<length \<pi>1. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1!i) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2!i)
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<pi>1 = take (length \<pi>1) \<pi>2 \<and> q1=q2"
  apply(subgoal_tac "\<pi>1 = take (length \<pi>1) \<pi>2")
   prefer 2
   apply(rule eliminating_derivations_are_equal_with_differing_future1)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac "\<pi>1")
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac ea)(*strict*)
   apply(case_tac \<alpha>1)
    apply(rename_tac ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac ea a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "\<pi>2")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac list aa lista)(*strict*)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>#\<pi>1s)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea e1 e2 c1 c2)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>#\<pi>2s)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e ea e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(case_tac c2)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
  apply(subgoal_tac "e2=\<pi>")
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and n="0"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
  apply(subgoal_tac "e2a=\<pi>")
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="0"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a e2 e2a c1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s e1 e1a l r la ra)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s l r la ra e ea)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac \<pi>1s \<pi> \<pi>2s l r la ra e ea)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s l r la ra e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s r la ra e ea l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac \<pi>1s \<pi> \<pi>2s r la ra e ea l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s r la ra e ea l')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s r ra e ea l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(case_tac l')
   apply(rename_tac \<pi>1s \<pi> \<pi>2s r ra e ea l' l'a)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1s \<pi> \<pi>2s r ra e ea l' l'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s r ra e ea l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s ra e ea l'a)(*strict*)
  apply(case_tac l'a)
   apply(rename_tac \<pi>1s \<pi> \<pi>2s ra e ea l'a)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1s \<pi> \<pi>2s ra e ea l'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1s \<pi> \<pi>2s ra e ea l'a)(*strict*)
  apply(clarsimp)
  done

lemma eliminating_derivations_are_equal_with_differing_future3: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> length \<pi>1 \<le> length \<pi>2
  \<Longrightarrow> \<forall>i<length \<pi>1. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1!i) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2!i)
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<pi>1 = \<pi>2 \<and> q1=q2"
  apply(subgoal_tac "\<pi>1 = take (length \<pi>1) \<pi>2 \<and> q1=q2")
   prefer 2
   apply(rule eliminating_derivations_are_equal_with_differing_future2)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac "length \<pi>1 = length \<pi>2")
   apply(clarsimp)
  apply(subgoal_tac "length \<pi>1 < length \<pi>2")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "d1 (length \<pi>1) = d2 (length \<pi>1)")
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2" for SSd SSn)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length (\<pi>2)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2 e)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2 e l r)(*strict*)
   apply (metis setA_liftB elemInsetA ex_in_conv)
  apply(subgoal_tac "\<forall>k\<le>(length \<pi>1). d1 k = d2 k")
   apply(force)
  apply(rule_tac
      y="length \<pi>2-length \<pi>1"
      and x="0"
      and n="length \<pi>1"
      in cfgLM.equal_labels_is_forward_target_deterministic_coinciding_positions)
          apply(force)
         apply(rule CFGLM0_is_forward_target_deterministic)
         apply(force)
        apply(simp add: cfgLM.trans_der_def)
       apply(simp add: cfgLM.trans_der_def)
      apply(simp add: cfgLM.trans_der_def)
     apply(simp add: cfgLM.trans_der_def)
     apply(rule sym)
     apply(rule_tac
      m="length \<pi>2-length \<pi>1"
      and v="map Some (drop(length \<pi>1)\<pi>2)"
      in get_labels_drop_tail)
      apply(rule_tac
      t="(length \<pi>1 + (length \<pi>2 - length \<pi>1))"
      and s="length \<pi>2"
      in ssubst)
       apply(force)
      apply(rule_tac
      t="map Some \<pi>1 @ map Some (drop (length \<pi>1) \<pi>2)"
      and s="map Some \<pi>2"
      in ssubst)
       apply(clarsimp)
       apply(rename_tac e ea)(*strict*)
       apply(rule_tac
      t="\<pi>1"
      and P="\<lambda>X. map Some X @ map Some (drop (length \<pi>1) \<pi>2) = map Some \<pi>2"
      and s="take (length \<pi>1) \<pi>2"
      in ssubst)
        apply(rename_tac e ea)(*strict*)
        apply(force)
       apply(rename_tac e ea)(*strict*)
       apply(thin_tac "\<pi>1=take(length \<pi>1)\<pi>2")
       apply (metis append_take_drop_id_hlp map_append)
      apply(force)
     apply(force)
    apply(simp add: cfgLM.trans_der_def)
    apply(force)
   apply(simp add: cfgLM.trans_der_def)
   apply(force)
  apply(force)
  done

lemma eliminating_derivations_are_equal_with_differing_future4: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> length \<pi>1 \<le> length \<pi>2
  \<Longrightarrow> \<forall>i<length \<pi>1. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1!i) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2!i)
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<pi>1 = \<pi>2 \<and> q1=q2 \<and> \<alpha>1=\<alpha>2"
  apply(subgoal_tac "\<pi>1 = \<pi>2 \<and> q1=q2")
   prefer 2
   apply(rule eliminating_derivations_are_equal_with_differing_future3)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "d1 (length \<pi>2) = d2 (length \<pi>2)")
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(rule liftB_inj)
   apply(rule sym)
   apply(force)
  apply(subgoal_tac "\<forall>k\<le>(length \<pi>2). d1 k = d2 k")
   apply(force)
  apply(rule_tac
      y="0"
      and x="0"
      and n="length \<pi>2"
      in cfgLM.equal_labels_is_forward_target_deterministic_coinciding_positions)
          apply(force)
         apply(rule CFGLM0_is_forward_target_deterministic)
         apply(force)
        apply(simp add: cfgLM.trans_der_def)
       apply(simp add: cfgLM.trans_der_def)
      apply(simp add: cfgLM.trans_der_def)
     apply(simp add: cfgLM.trans_der_def)
    apply(simp add: cfgLM.trans_der_def)
    apply(force)
   apply(simp add: cfgLM.trans_der_def)
   apply(force)
  apply(force)
  done

lemma cfgLM_positions_remain_compatible_prime_prime: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> LR1ProdFormSimp G'
  \<Longrightarrow> cfgLM.derivation G' d1
  \<Longrightarrow> cfgLM.derivation G' d2
  \<Longrightarrow> cfgLM.belongs G' d1
  \<Longrightarrow> cfgLM.belongs G' d2
  \<Longrightarrow> d1 0 = Some (pair None \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr>)
  \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr>)
  \<Longrightarrow> d1 n = Some (pair e1 \<lparr>cfg_conf=liftB v1@liftA w1\<rparr>)
  \<Longrightarrow> d2 n = Some (pair e2 \<lparr>cfg_conf=liftB v2@liftA w2\<rparr>)
  \<Longrightarrow> v1@x1=v2@x2
  \<Longrightarrow> (\<forall>k. Suc 0\<le>k\<and>k\<le>n \<longrightarrow>
  F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d1 k)))
  = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d2 k))))
  \<and> v1=v2
  \<and> l3seq w1
  \<and> l3seq w2
  \<and> (\<forall>q A. cons_l2 q A \<notin> set w1)
  \<and> (\<forall>q A. cons_l2 q A \<notin> set w2)
  \<and> equal_stacks w1 w2
  \<and> equal_front_states (take (Suc 0) w1) (take (Suc 0) w2)"
  apply(induct n arbitrary: e1 e2 v1 v2 w1 w2 x1 x2)
   apply(rename_tac e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
   apply(case_tac v1)
    apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
    prefer 2
    apply(rename_tac v1 v2 w1 w2 x1 x2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v1 v2 w1 w2 x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w1 w2)(*strict*)
   apply(case_tac w1)
    apply(rename_tac v2 w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w1 w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w2 list)(*strict*)
   apply(case_tac list)
    apply(rename_tac v2 w2 list)(*strict*)
    prefer 2
    apply(rename_tac v2 w2 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w2 list)(*strict*)
   apply(clarsimp)
   apply(rename_tac v2 w2)(*strict*)
   apply(case_tac v2)
    apply(rename_tac v2 w2)(*strict*)
    prefer 2
    apply(rename_tac v2 w2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v2 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2)(*strict*)
   apply(case_tac w2)
    apply(rename_tac w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    prefer 2
    apply(rename_tac list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
   apply(simp add: l3seq_def equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n = Some (pair e1 c1) \<and> d1 (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2")
   apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 v1 v2 w1 w2 x1 x2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 n = Some (pair e1 c1) \<and> d2 (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2")
   apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
     apply(force)
    apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
    apply(force)
   apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
   apply(force)
  apply(rename_tac n e2 v1 v2 w1 w2 x1 x2 e1a e2a c1 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac c1a)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra cfg_confa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a c1 l r e1 e2b c1a la ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a l r e1 e2b la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs e2a = liftB w1 @ liftA w2")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="e2a"
      in ballE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
    apply(rule_tac
      x="[b]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a r e1 e2b ra l' l'a Aa B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs e2b = liftB w1 @ liftA w2")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="e2b"
      in ballE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
    apply(rule_tac
      x="[b]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(erule disjE)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 ra l' l'a w1a w2a Aa B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(subgoal_tac "(\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = liftB l' @ teA (prod_lhs e2a) # r\<rparr>=liftB w1@liftA w2)")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and c="\<lparr>cfg_conf = [teA (cons_l3   q A q1)]\<rparr>"
      and c'="\<lparr>cfg_conf = liftB l' @ teA (prod_lhs e2a) # r\<rparr>"
      and \<pi>="map the (get_labels d1 n)"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
         apply(force)
        apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
        apply(force)
       apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
       apply(force)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      t="length (get_labels d1 n)"
      and s="n"
      in ssubst)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[cons_l3 q A q1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(subgoal_tac "(\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = liftB l'a @ teA (prod_lhs e2b) # ra\<rparr>=liftB w1@liftA w2)")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and c="\<lparr>cfg_conf = [teA (cons_l3   q A q2)]\<rparr>"
      and c'="\<lparr>cfg_conf = liftB l'a @ teA (prod_lhs e2b) # ra\<rparr>"
      and \<pi>="map the (get_labels d2 n)"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
         apply(force)
        apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
        apply(force)
       apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
       apply(force)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      t="length (get_labels d2 n)"
      and s="n"
      in ssubst)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(rule conjI)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
      apply(force)
     apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
     apply(force)
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
    apply(force)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[cons_l3 q A q2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(subgoal_tac "l'=w1c")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(subgoal_tac "l'a=w1d")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra l' l'a w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
  apply(case_tac w2c)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d)(*strict*)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a r e1 e2b ra w1a w2a w1b w2b w1c w1d w2c w2d a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list)(*strict*)
  apply(case_tac w2d)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b ra w1a w2a w1b w2b w1c w1d w2d list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "v2=w1d@w1b")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB v2 @ liftA w2 = liftB (w1d @ w1b) @ liftA (w2b @ lista)")
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
    apply(thin_tac "liftB v2 @ liftA w2 = liftB w1d @ liftB w1b @ liftA w2b @ liftA lista")
    apply (metis liftA_commutes_over_concat liftB_liftA_inj1)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   apply(simp add: simpY)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "v1=w1c@w1a")
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB v1 @ liftA w1 = liftB (w1c @ w1a) @ liftA (w2a @ list)")
    apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
    apply(thin_tac "liftB v1 @ liftA w1 = liftB w1c @ liftB w1a @ liftA w2a @ liftA list")
    apply (metis liftA_commutes_over_concat liftB_liftA_inj1)
   apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   apply(simp add: simpY)
  apply(rename_tac n v1 v2 w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(simp add: simpY)
  apply(subgoal_tac "w2=w2b@lista")
   apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: simpY)
  apply(rename_tac n w1 w2 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(subgoal_tac "w1=w2a@list")
   apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(simp add: simpY)
  apply(rename_tac n w1 x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1a e2a e1 e2b w1a w2a w1b w2b w1c w1d list lista)(*strict*)
  apply(thin_tac "liftA (w2b @ lista) = liftA w2b @ liftA lista")
  apply(thin_tac "liftA (w2a @ list) = liftA w2a @ liftA list")
  apply(rename_tac e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule_tac
      x="\<alpha>1"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2"
      in meta_allE)
  apply(erule_tac
      x="prod_lhs e1'#\<beta>1"
      in meta_allE)
  apply(erule_tac
      x="prod_lhs e2'#\<beta>2"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>1'@x1"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2'@x2"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>1 \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1' e1'\<beta> \<alpha>2' e2'\<beta> \<alpha>2 \<beta>1 \<beta>2)(*strict*)
  apply(rename_tac \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2)(*strict*)
  apply(case_tac e1')
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac e2')
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
  apply(rename_tac A1 w1 A2 w2)
  apply(rename_tac n x1 x2 e1 e1' e2 e2' \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 w1 A2 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2)(*strict*)
  apply(case_tac A1)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 qa b)(*strict*)
   apply(erule_tac
      x="qa"
      in allE)+
   apply(erule_tac
      x="b"
      in allE)+
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a)(*strict*)
  apply(case_tac A2)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a qa ba)(*strict*)
   apply(erule_tac
      x="qa"
      in allE)+
   apply(erule_tac
      x="ba"
      in allE)+
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 A1 A2 q1a b q2a q1aa ba q2aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 q1a b q2a q1aa ba q2aa)(*strict*)
  apply(rename_tac qx1 A1 q1' qx2 A2 q2')
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
  apply(subgoal_tac "qx1=qx2 \<and> A1=A2")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
    apply(simp add: l3seq_def equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   apply(simp add: equal_stacks_def equal_stack_def)
   apply(erule_tac
      x="0"
      and P="\<lambda>X. X < Suc (length \<beta>1) \<and> X < Suc (length \<beta>2) \<longrightarrow> (let cmp = case_DT_l2_l3_nonterminals (\<lambda>q A. A) (\<lambda>q1 A q2. A) in cmp ((cons_l3 qx1 A1 q1' # \<beta>1) ! X) = cmp ((cons_l3 qx2 A2 q2' # \<beta>2) ! X))"
      in allE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 qx1 A1 q1' qx2 A2 q2')(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 q1' qx2 A2 q2')(*strict*)
  apply(rename_tac p1 p B p2)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(subgoal_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(subgoal_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
    apply(simp add: F_SDPDA_TO_CFG_STD_def cfg_sub_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G"
      in disjE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   prefer 2
   apply(rule l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "k=Suc n")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 k)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(simp add: get_label_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_def)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G. \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> (case edge_event x of None \<Rightarrow> {} | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G))"
      in disjE)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*read1/read1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_event xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
     apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
          apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
         apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(rule only_cfgLM_accessible_productions)
              apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
              apply(force)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
       apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
     apply(simp add: prefix_def)
     apply(simp add: option_to_list_def)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
     apply(case_tac "\<alpha>1")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
      apply(case_tac e1'\<beta>)
       apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a)(*strict*)
       apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a ab list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a ab list)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
     apply(case_tac "\<alpha>2")
      apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
      apply(case_tac e2'\<beta>)
       apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list)(*strict*)
       apply(clarsimp)
      apply(rename_tac n e1 e2 e1'\<beta> e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list ab lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p2 x xa a aa s1a list ab lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*read1/pop1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_push xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rule valid_simple_dpda_edge_alt)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
           apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
          apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
         apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(rule only_cfgLM_accessible_productions)
              apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
              apply(force)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
     apply(simp add: option_to_list_def prefix_def)
    (*read1/push1*)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     prefer 2
     apply(rule valid_simple_dpda_edge_alt)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     prefer 2
     apply(rule valid_simple_dpda_edge_alt)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(case_tac "edge_event x")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(case_tac "edge_push xa")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
    apply(clarsimp)
    apply(case_tac "edge_event xa")
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
     prefer 2
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list ab)(*strict*)
     apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{xa}"
      in ssubst)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      G="G"
      in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule_tac
      A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
      in set_mp)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule_tac
      t="epdaS_accessible_edges G"
      and s="epdaH_accessible_edges G"
      in ssubst)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
          apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
         apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
        apply(rule_tac
      x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
      in bexI)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule_tac
      A="cfg_productions G'"
      in set_mp)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(rule only_cfgLM_accessible_productions)
             apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
             apply(force)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(simp add: option_to_list_def prefix_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(erule_tac
      P="\<exists>x\<in> epda_delta G. \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> (case edge_event x of None \<Rightarrow> {} | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G))"
      in disjE)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(erule disjE)
    (*pop1/read1*)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(case_tac "edge_event x")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(case_tac "edge_push xa")
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      prefer 2
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a aa list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
      and s="{x}"
      in ssubst)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
   apply(rule sym)
   apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
        apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
       apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in bexI)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(rule only_cfgLM_accessible_productions)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa a s1 s1a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(simp add: option_to_list_def prefix_def)
  (*push1/read1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_event x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list ab)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_read_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule_tac
    P="\<exists>x\<in> epda_delta G. \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> (case edge_push x of [] \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_pop x | a # y \<Rightarrow> {})"
    in disjE)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)
  (*pop1/pop1*)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    prefer 2
    apply(rule valid_simple_dpda_edge_alt)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(case_tac "edge_push x")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    prefer 2
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(case_tac "edge_push xa")
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    prefer 2
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
         apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
        apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
       apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(rule only_cfgLM_accessible_productions)
            apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
            apply(force)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
     apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(simp add: option_to_list_def prefix_def)
  (*pop1/push1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule disjE)
  (*push1/pop1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   prefer 2
   apply(rule valid_simple_dpda_edge_alt)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_event x")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_push xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_event xa")
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
   prefer 2
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_pop_single_source)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
        apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
       apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
      apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(rule only_cfgLM_accessible_productions)
           apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
           apply(force)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  (*push1/push1*)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop xa=[s1] \<and> ((edge_event xa \<noteq> None \<and> edge_push xa=[s1]) \<or> (edge_event xa = None \<and> edge_push xa=[s2,s1]) \<or> (edge_event xa = None \<and> edge_push xa=[])))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(case_tac "edge_push x")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "edge_event x")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  prefer 2
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(case_tac "edge_push xa")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  apply(case_tac "edge_event xa")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  prefer 2
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and s="{x}"
    in ssubst)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule_tac
    t="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    and s="{xa}"
    in ssubst)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(rule F_SDPDA_TO_CFG_STD__edges_l3_push_single_source)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    G="G"
    in epdaS_apply_is_forward_edge_deterministic_accessibleE_with_ReachableEdge)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule_tac
    A="F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G (cfgLM_accessible_productions (F_SDPDA_TO_CFG_STD G))"
    in set_mp)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule_tac
    t="epdaS_accessible_edges G"
    and s="epdaH_accessible_edges G"
    in ssubst)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(rule epdaH_accessible_edges_vs_epdaS_accessible_edges)
       apply(simp add: valid_simple_dpda_def valid_dpda_def valid_pda_def)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_pt1)
      apply(simp add: F_SDPDA_TO_CFG_STD__SpecInput_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_def)
     apply(rule_tac
    x="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    in bexI)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(simp add: F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_def)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(rule_tac
    A="cfg_productions G'"
    in set_mp)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(rule only_cfgLM_accessible_productions)
          apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
          apply(force)
         apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
         apply(force)
        apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
        apply(force)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2 x xa s1 s1a a aa)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def F_SDPDA_TO_CFG_STD__edges_l3_pop_def F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(simp add: option_to_list_def prefix_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "\<forall>k. Suc 0 \<le> k \<and> k \<le> n \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the (get_label (d1 k))) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the (get_label (d2 k)))")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(erule_tac
    x="Suc n"
    in allE)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "(\<exists>x\<in> epda_delta SSG. edge_event x \<noteq> None \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_read x) \<or> edge_event x = None \<and> edge_push x = [] \<and> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<or> edge_event x = None \<and> edge_push x \<noteq> [] \<and> (SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG)) \<and> (SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states SSG) \<or> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_push x (epda_states SSG))) \<or> SSe1 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG) \<and> SSe2 \<in> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking SSG) (epda_gamma SSG)" for SSG SSe1 SSe2)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  prefer 2
  apply(rule_tac
    ?e1.0="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>"
    and ?e2.0="\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>"
    in F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_equal_then_from_special_sets)
       apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
       apply(force)
      apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
      apply(force)
     apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
     apply(force)
    apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
    apply(force)
   apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
   apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(force)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3 G")
  apply(thin_tac "F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>")
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(thin_tac "cfgLM.derivation G' d1")
  apply(thin_tac "cfgLM.derivation G' d2")
  apply(thin_tac "cfgLM.belongs G' d1")
  apply(thin_tac "cfgLM.belongs G' d2")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teA (cons_l3   q A q1)]\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = [teA (cons_l3   q A q2)]\<rparr>)")
  apply(thin_tac "d1 (Suc n) = Some (pair (Some \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr>) \<lparr>cfg_conf = liftB \<alpha> @ liftB \<alpha>1 @ liftA e1'\<beta> @ liftA \<beta>1\<rparr>)")
  apply(thin_tac "d2 (Suc n) = Some (pair (Some \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr>) \<lparr>cfg_conf = liftB \<alpha> @ liftB \<alpha>2 @ liftA e2'\<beta> @ liftA \<beta>2\<rparr>)")
  apply(thin_tac "d1 n = Some (pair e1 \<lparr>cfg_conf = liftB \<alpha> @ teA (cons_l3   p B p1) # liftA \<beta>1\<rparr>)")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> cfg_productions G'")
  apply(thin_tac "d2 n = Some (pair e2 \<lparr>cfg_conf = liftB \<alpha> @ teA (cons_l3   p B p2) # liftA \<beta>2\<rparr>)")
  apply(thin_tac "\<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> cfg_productions G'")
  apply(erule disjE)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
  apply(rename_tac n x1 x2 e1 e2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<alpha> \<beta>1 \<beta>2 p1 p B p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(erule_tac
    P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_read x (epda_states G)"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x y)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_read_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "\<alpha>2")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac e2'\<beta>)
   apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "\<alpha>1")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac e1'\<beta>)
   apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "e1'\<beta>")
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(case_tac "e2'\<beta>")
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2'\<beta> \<beta>1 \<beta>2 p1 p2 x y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  prefer 2
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(thin_tac "l3seq (cons_l3   (edge_src x) (edge_pop x ! 0) p2 # \<beta>2)")
  apply(rule l3seq_change_initial_state)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(thin_tac "l3seq (cons_l3   (edge_src x) (edge_pop x ! 0) p1 # \<beta>1)")
  apply(rule l3seq_change_initial_state)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
   apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i)(*strict*)
  apply(simp add: Let_def)
  apply(erule_tac
    x="i"
    in allE)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x y)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(subgoal_tac "(\<exists>s1 s2. edge_pop x=[s1] \<and> ((edge_event x \<noteq> None \<and> edge_push x=[s1]) \<or> (edge_event x = None \<and> edge_push x=[s2,s1]) \<or> (edge_event x = None \<and> edge_push x=[])))")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  prefer 2
  apply(rule valid_simple_dpda_edge_alt)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(force)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(force)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule_tac
    P="edge_event x = None \<and> edge_push x = [] \<and> \<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x \<and> \<lparr>prod_lhs = cons_l3 p B p2, prod_rhs = liftB \<alpha>2 @ liftA e2'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop x"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "\<alpha>1=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "e1'\<beta>=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "\<alpha>2=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(subgoal_tac "e2'\<beta>=[]")
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  prefer 2
  apply(metis liftA_empty liftB_empty)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule l3seq_drop_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule l3seq_drop_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 i)(*strict*)
  apply(simp add: Let_def)
  apply(case_tac \<beta>1)
   apply(rename_tac \<beta>1 \<beta>2 x s1 i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 i a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 i a list)(*strict*)
  apply(case_tac \<beta>2)
   apply(rename_tac \<beta>2 x s1 i a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 i a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 i a list aa lista)(*strict*)
  apply(erule_tac
    x="Suc i"
    in allE)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(simp add: equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(simp add: Let_def)
  apply(case_tac \<beta>1)
  apply(rename_tac \<beta>1 \<beta>2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 x s1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 a list)(*strict*)
  apply(case_tac \<beta>2)
  apply(rename_tac \<beta>2 x s1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>2 x s1 a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 a list aa lista)(*strict*)
  apply(case_tac a)
  apply(rename_tac x s1 a list aa lista q b)(*strict*)
  apply(force)
  apply(rename_tac x s1 a list aa lista q1 b q2)(*strict*)
  apply(case_tac aa)
  apply(rename_tac x s1 a list aa lista q1 b q2 q ba)(*strict*)
  apply(force)
  apply(rename_tac x s1 a list aa lista q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 list lista q1 b q2 q1a ba q2a)(*strict*)
  apply(simp add: l3seq_def)
  apply(erule_tac
    x="[]"
    and P="\<lambda>w1. \<forall> xa y. (\<exists>w2. cons_l3 (edge_src x) s1 (edge_trg x) # cons_l3 q1 b q2 # list = w1 @ xa # y # w2) \<longrightarrow> (case xa of cons_l2 q A \<Rightarrow> False | cons_l3 q1 A1 q1' \<Rightarrow> case y of cons_l2 q A \<Rightarrow> False | cons_l3 q2 A2 q2' \<Rightarrow> q1' = q2)"
    in allE)
  apply(rename_tac x s1 list lista q1 b q2 q1a ba q2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x s1 list lista b q2 q1a ba q2a)(*strict*)
  apply(erule_tac
    x="[]"
    in allE)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(erule_tac
    P="\<lparr>prod_lhs = cons_l3 p B p1, prod_rhs = liftB \<alpha>1 @ liftA e1'\<beta>\<rparr> \<in> F_SDPDA_TO_CFG_STD__edges_l3_push x (epda_states G)"
    in disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(erule disjE)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  prefer 2
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_push_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1 s2)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac \<alpha>2)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  prefer 2
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac e2'\<beta>)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> e2'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(case_tac lista)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  prefer 2
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac \<alpha>1)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  prefer 2
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<alpha>1 e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(case_tac e1'\<beta>)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1'\<beta> \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(case_tac list)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(case_tac lista)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  prefer 2
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule l3_seq_add_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule l3_seq_add_initial_state)
  apply(force)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i)(*strict*)
  apply(simp add: Let_def)
  apply(case_tac i)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa nata)(*strict*)
  apply(erule_tac
    x="Suc nata"
    in allE)
  apply(clarsimp)
  apply(rename_tac \<beta>1 \<beta>2 p1 p2 x s1 s2 qs qsa)(*strict*)
  apply(simp add: equal_front_states_def equal_front_state_def)
  apply(rename_tac x1 x2 \<alpha>1 e1'\<beta> \<alpha>2 e2'\<beta> \<beta>1 \<beta>2 p1 p B p2 x s1)(*strict*)
  apply(clarsimp)
  done

lemma eliminating_derivations_are_equal_with_differing_future5: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> length \<pi>1 \<le> length \<pi>2
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<alpha>1@x1=\<alpha>2@x2
  \<Longrightarrow> \<pi>1 = \<pi>2 \<and> q1=q2 \<and> \<alpha>1=\<alpha>2"
  apply(subgoal_tac "LR1ProdFormSimp G'")
   prefer 2
   apply(rule LR1ProdForm_implies_LR1ProdFormSimp)
   apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
   apply(force)
  apply(subgoal_tac "\<forall>i<length \<pi>1. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>1!i) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (\<pi>2!i)")
   apply(rule eliminating_derivations_are_equal_with_differing_future4)
           apply(force)+
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac i e ea)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (length \<pi>1) = Some (pair e c)")
   apply(rename_tac i e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="length \<pi>2"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac i e ea)(*strict*)
     apply(force)
    apply(rename_tac i e ea)(*strict*)
    apply(force)
   apply(rename_tac i e ea)(*strict*)
   apply(force)
  apply(rename_tac i e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea eb c)(*strict*)
  apply(subgoal_tac "(\<exists>w1 w2. cfg_conf c=liftB w1@liftA w2)")
   apply(rename_tac i e ea eb c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and c="\<lparr>cfg_conf = [teA (cons_l3   q A q2)]\<rparr>"
      and c'="c"
      and \<pi>="map the (get_labels d2 (length \<pi>1))"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac i e ea eb c)(*strict*)
         apply(force)
        apply(rename_tac i e ea eb c)(*strict*)
        apply(force)
       apply(rename_tac i e ea eb c)(*strict*)
       apply(force)
      apply(rename_tac i e ea eb c)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb c)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb c)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      t="length (get_labels d2 (length \<pi>1))"
      and s="length \<pi>1"
      in ssubst)
     apply(rename_tac i e ea eb c)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac i e ea eb c)(*strict*)
    apply(rule conjI)
     apply(rename_tac i e ea eb c)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac i e ea eb c)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb c)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb c)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb c)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[cons_l3 q A q2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac i e ea eb c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea eb c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e ea eb c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea eb w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac i e ea eb w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      P="G'"
      and d="d2"
      and i="length \<pi>1"
      and j="length \<pi>2-length \<pi>1"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac i e ea eb w1 w2)(*strict*)
        apply(force)
       apply(rename_tac i e ea eb w1 w2)(*strict*)
       apply(force)
      apply(rename_tac i e ea eb w1 w2)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb w1 w2)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb w1 w2)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w1 w2)(*strict*)
   apply(force)
  apply(rename_tac i e ea eb w1 w2)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(clarsimp)
  apply(rename_tac i e ea eb w1 w2 w)(*strict*)
  apply(subgoal_tac "w1@w=\<alpha>2")
   apply(rename_tac i e ea eb w1 w2 w)(*strict*)
   prefer 2
   apply(rule_tac
      t="w1"
      and s="maxTermPrefix (liftB w1 @ liftA w2)"
      in ssubst)
    apply(rename_tac i e ea eb w1 w2 w)(*strict*)
    apply (metis maxTermPrefix_shift maximalTermPrefix_split)
   apply(rename_tac i e ea eb w1 w2 w)(*strict*)
   apply(rule_tac
      t="\<alpha>2"
      and s="maxTermPrefix (liftB \<alpha>2)"
      in ssubst)
    apply(rename_tac i e ea eb w1 w2 w)(*strict*)
    apply (simp add: maxTermPrefix_term_string)
   apply(rename_tac i e ea eb w1 w2 w)(*strict*)
   apply(force)
  apply(rename_tac i e ea eb w1 w2 w)(*strict*)
  apply(thin_tac "maxTermPrefix (liftB w1 @ liftA w2) @ w = maxTermPrefix (liftB \<alpha>2)")
  apply(clarsimp)
  apply(subgoal_tac "(\<forall>k. Suc 0 \<le> k \<and> k \<le> SSn \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 SSG (the (get_label (SSd1 k))) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 SSG (the (get_label (SSd2 k)))) \<and> SSv1 = SSv2 \<and> l3seq SSw1 \<and> l3seq SSw2 \<and> (\<forall>q A. cons_l2 q A \<notin> set SSw1) \<and> (\<forall>q A. cons_l2 q A \<notin> set SSw2) \<and> equal_stacks SSw1 SSw2 \<and> equal_front_states (take (Suc 0) SSw1) (take (Suc 0) SSw2)" for SSn SSd1 SSG SSd2 SSv1 SSv2 SSw1 SSw2)
   apply(rename_tac i e ea eb w1 w2 w)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="[]"
      and n="length \<pi>1"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in cfgLM_positions_remain_compatible_prime_prime)
                 apply(rename_tac i e ea eb w1 w2 w)(*strict*)
                 apply(force)
                apply(rename_tac i e ea eb w1 w2 w)(*strict*)
                apply(force)
               apply(rename_tac i e ea eb w1 w2 w)(*strict*)
               apply(force)
              apply(rename_tac i e ea eb w1 w2 w)(*strict*)
              apply(force)
             apply(rename_tac i e ea eb w1 w2 w)(*strict*)
             apply(force)
            apply(rename_tac i e ea eb w1 w2 w)(*strict*)
            apply(force)
           apply(rename_tac i e ea eb w1 w2 w)(*strict*)
           apply(force)
          apply(rename_tac i e ea eb w1 w2 w)(*strict*)
          apply(force)
         apply(rename_tac i e ea eb w1 w2 w)(*strict*)
         apply(force)
        apply(rename_tac i e ea eb w1 w2 w)(*strict*)
        apply(force)
       apply(rename_tac i e ea eb w1 w2 w)(*strict*)
       apply(force)
      apply(rename_tac i e ea eb w1 w2 w)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb w1 w2 w)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac i e ea eb w1 w2 w)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w1 w2 w)(*strict*)
   apply(force)
  apply(rename_tac i e ea eb w1 w2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea eb w2 w)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d1 (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e ea eb w2 w)(*strict*)
   prefer 2
   apply(rule_tac
      m="length \<pi>1"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac i e ea eb w2 w)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb w2 w)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb w2 w)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e ea eb w2 w)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e ea eb w2 w)(*strict*)
   prefer 2
   apply(rule_tac
      m="length \<pi>2"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac i e ea eb w2 w)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb w2 w)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb w2 w)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e ea eb w2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
  apply(simp add: get_label_def)
  apply(rule_tac
      t="\<pi>1!i"
      and s="ec"
      in ssubst)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(rule Some_inj)
   apply(rule_tac
      t="Some (\<pi>1!i) "
      and s="(map Some \<pi>1)!i"
      in ssubst)
    apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(rule getLabel_at_pos)
     apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(force)
  apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
  apply(rule_tac
      t="\<pi>2!i"
      and s="ed"
      in ssubst)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(rule Some_inj)
   apply(rule_tac
      t="Some (\<pi>2!i) "
      and s="(map Some \<pi>2)!i"
      in ssubst)
    apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(rule getLabel_at_pos)
     apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
   apply(force)
  apply(rename_tac i e ea eb w2 w ec ed c ca)(*strict*)
  apply(force)
  done

theorem eliminating_derivations_are_equal_with_differing_future6: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfgLM.trans_der G' d1 \<lparr>cfg_conf=[teA (cons_l3   q A q1)]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G' d2 \<lparr>cfg_conf=[teA (cons_l3   q A q2)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> \<alpha>1 @ x1 = \<alpha>2 @ x2
  \<Longrightarrow> \<pi>1 = \<pi>2 \<and> q1 = q2 \<and> \<alpha>1 = \<alpha>2"
  apply(case_tac "length \<pi>1 \<le> length \<pi>2")
   apply(rule eliminating_derivations_are_equal_with_differing_future5)
           apply(force)+
  apply(subgoal_tac "\<pi>2 = \<pi>1 \<and> q2=q1 \<and> \<alpha>2=\<alpha>1")
   apply(force)
  apply(rule_tac
      ?x2.0="x1"
      and ?x1.0="x2"
      in eliminating_derivations_are_equal_with_differing_future5)
          apply(force)+
  done

lemma cfgLM_positions_remain_compatible_prime: "
  valid_simple_dpda G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_cfg (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_sub G' (F_SDPDA_TO_CFG_STD G)
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfgLM.derivation G' d1
  \<Longrightarrow> cfgLM.derivation G' d2
  \<Longrightarrow> cfgLM.belongs G' d1
  \<Longrightarrow> cfgLM.belongs G' d2
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> d1 0 = Some (pair None \<lparr>cfg_conf=[teA A]\<rparr>)
  \<Longrightarrow> d1 n = Some (pair e1 c1)
  \<Longrightarrow> d2 n = Some (pair e2 c2)
  \<Longrightarrow> cfg_conf c1 = (liftB v1) @ teA B1 # (liftA r1)
  \<Longrightarrow> cfg_conf c2 = (liftB v2) @ teA B2 # (liftA r2)
  \<Longrightarrow> v1@x1=v2@x2
  \<Longrightarrow> (\<forall>k. Suc 0\<le>k\<and>k\<le>n \<longrightarrow>
  F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d1 k)))
  = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G (the(get_label(d2 k))))
  \<and> v1=v2
  \<and> equal_stack B1 B2
  \<and> equal_front_state B1 B2"
  apply(subgoal_tac "A \<in> cfg_nonterminals G' \<and> (\<exists>d. cfgLM.derivation_initial G' d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2)))")
   prefer 2
   apply(subgoal_tac "A \<in> cfgLM_accessible_nonterminals G'")
    prefer 2
    apply(subgoal_tac "\<lparr>cfg_conf = [teA A]\<rparr> \<in> cfg_configurations G'")
     apply(simp add: cfg_configurations_def)
    apply(rule_tac
      e="None"
      and d="d1"
      and i="0"
      in cfgLM.belongs_configurations)
     apply(force)
    apply(force)
   apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac d na c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac d na c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na w1 w2)(*strict*)
  apply(case_tac "d na")
   apply(rename_tac d na w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d na w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac d na w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d na w1 w2 e cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d na w1 w2 e cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G' d1 \<lparr>cfg_conf = [teA A]\<rparr> (map the (get_labels d1 n)) \<lparr>cfg_conf = liftB v1 @ teA B1 # liftA r1\<rparr>")
   apply(rename_tac d na w1 w2 e)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      t="length (get_labels d1 n)"
      and s="n"
      in ssubst)
    apply(rename_tac d na w1 w2 e)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac d na w1 w2 e)(*strict*)
   apply(rule conjI)
    apply(rename_tac d na w1 w2 e)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac d na w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac d na w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac d na w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G' d2 \<lparr>cfg_conf = [teA A]\<rparr> (map the (get_labels d2 n)) \<lparr>cfg_conf = liftB v2 @ teA B2 # liftA r2\<rparr>")
   apply(rename_tac d na w1 w2 e)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d na w1 w2 e ea)(*strict*)
   apply(rule_tac
      t="length (get_labels d2 n)"
      and s="n"
      in ssubst)
    apply(rename_tac d na w1 w2 e ea)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac d na w1 w2 e ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d na w1 w2 e ea)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac d na w1 w2 e ea)(*strict*)
     apply(force)
    apply(rename_tac d na w1 w2 e ea)(*strict*)
    apply(force)
   apply(rename_tac d na w1 w2 e ea)(*strict*)
   apply(force)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(thin_tac "cfgLM.derivation G' d2")
  apply(thin_tac "cfgLM.belongs G' d1")
  apply(thin_tac "cfgLM.belongs G' d2")
  apply(thin_tac "Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) = d2 0")
  apply(thin_tac "d1 0 = d2 0")
  apply(thin_tac "d1 n = Some (pair e1 \<lparr>cfg_conf = liftB v1 @ teA B1 # liftA r1\<rparr>)")
  apply(thin_tac "d2 n = Some (pair e2 \<lparr>cfg_conf = liftB v2 @ teA B2 # liftA r2\<rparr>)")
  apply(subgoal_tac "cfgLM.trans_der G' d \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> (map the (get_labels d na)) \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>")
   apply(rename_tac d na w1 w2 e)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d na w1 w2 e ea eb)(*strict*)
   apply(rule_tac
      t="length (get_labels d na)"
      and s="na"
      in ssubst)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac d na w1 w2 e ea eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(rename_tac d na w1 w2 e ea eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac d na w1 w2 e ea eb)(*strict*)
     apply(force)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(force)
   apply(rename_tac d na w1 w2 e ea eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac d na w1 w2 e ea eb)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
     apply(force)
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(force)
   apply(rename_tac d na w1 w2 e ea eb)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac d na w1 w2 e ea eb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d na w1 w2 e ea eb a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d na w1 w2 e ea eb a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d na w1 w2 e ea eb b)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(thin_tac "cfgLM.derivation_initial G' d")
  apply(thin_tac "d na = Some (pair e \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>)")
  apply(thin_tac "cfgLM.derivation G' d1")
  apply(thin_tac "A \<in> cfgLM_accessible_nonterminals G'")
  apply(thin_tac "A \<in> cfgSTD_Nonblockingness_nonterminals G'")
  apply(subgoal_tac "\<exists>\<alpha>1' v1'. cfg_conf \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> = liftB \<alpha>1' @ liftA v1'")
   apply(rename_tac d na w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and c="\<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>"
      and \<pi>="(map the (get_labels d na))"
      in cfgLM_preserves_liftB_liftA_splitting)
         apply(rename_tac d na w1 w2 e)(*strict*)
         apply(force)
        apply(rename_tac d na w1 w2 e)(*strict*)
        apply(force)
       apply(rename_tac d na w1 w2 e)(*strict*)
       apply(force)
      apply(rename_tac d na w1 w2 e)(*strict*)
      apply(force)
     apply(rename_tac d na w1 w2 e)(*strict*)
     apply(rule LR1ProdForm_implies_LR1ProdFormSimp)
     apply(rule sub_of_F_SDPDA_TO_CFG_STD__implies_LR1ProdForm)
     apply(force)
    apply(rename_tac d na w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac d na w1 w2 e)(*strict*)
   apply(clarsimp)
   apply(rename_tac d na w1 w2)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[cfg_initial G']"
      in exI)
   apply(clarsimp)
  apply(rename_tac d na w1 w2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na w1 w2 \<alpha>1' v1')(*strict*)
  apply(subgoal_tac "w1=\<alpha>1'")
   apply(rename_tac d na w1 w2 \<alpha>1' v1')(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac d na w1 w2 \<alpha>1' v1')(*strict*)
  apply(clarsimp)
  apply(rename_tac d na w2 \<alpha>1' v1')(*strict*)
  apply(case_tac v1')
   apply(rename_tac d na w2 \<alpha>1' v1')(*strict*)
   apply(clarsimp)
  apply(rename_tac d na w2 \<alpha>1' v1' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na \<alpha>1' list)(*strict*)
  apply(rename_tac \<beta>)
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (derivation_append SSd1 (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = liftB SSv1 @ cfg_conf v @ SSv4\<rparr>)) (length SSrenPI10)) \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd1 SSd2 SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d1"
      and ?v1.0="\<alpha>1'"
      and ?v2.0="[teA A]"
      and ?v4.0="liftA \<beta>"
      in cfgLM_trans_der_concat_extend)
     apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
     apply(force)
    apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
    apply(force)
   apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
   apply(force)
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (derivation_append SSd1 (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = liftB SSv1 @ cfg_conf v @ SSv4\<rparr>)) (length SSrenPI10)) \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSd1 SSd2 SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d2"
      and ?v1.0="\<alpha>1'"
      and ?v2.0="[teA A]"
      and ?v4.0="liftA \<beta>"
      in cfgLM_trans_der_concat_extend)
     apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
     apply(force)
    apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
    apply(force)
   apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
   apply(force)
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(thin_tac "cfgLM.trans_der G' d1 \<lparr>cfg_conf = [teA A]\<rparr> (map the (get_labels d1 n)) \<lparr>cfg_conf = liftB v1 @ teA B1 # liftA r1\<rparr>")
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(thin_tac "cfgLM.trans_der G' d2 \<lparr>cfg_conf = [teA A]\<rparr> (map the (get_labels d2 n)) \<lparr>cfg_conf = liftB v2 @ teA B2 # liftA r2\<rparr>")
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(thin_tac "cfgLM.trans_der G' d \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> (map the (get_labels d na)) \<lparr>cfg_conf = liftB \<alpha>1' @ teA A # liftA \<beta>\<rparr>")
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(subgoal_tac "(\<forall>k. Suc 0 \<le> k \<and> k \<le> SSn \<longrightarrow> F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 SSG (the (get_label (SSd1 k))) = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 SSG (the (get_label (SSd2 k)))) \<and> SSv1 = SSv2 \<and> equal_stacks (SSB1 # SSr1) (SSB2 # SSr2) \<and> (\<exists>m. equal_front_states (SSB1 # take m SSr1) (SSB2 # take m SSr2) \<and> (case drop m SSr1 of [] \<Rightarrow> True | A1 # w1 \<Rightarrow> case drop m SSr2 of [] \<Rightarrow> True | A2 # w2 \<Rightarrow> \<not> equal_front_state A1 A2))" for SSn SSG SSd1 SSd2 SSv1 SSv2 SSB1 SSr1 SSB2 SSr2)
   apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(subgoal_tac "length (get_labels d na) = na")
    apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
    prefer 2
    apply (metis get_labels_length)
   apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
   apply(subgoal_tac "length (get_labels d1 n) = n")
    apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
    prefer 2
    apply (metis get_labels_length)
   apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
   apply(subgoal_tac "length (get_labels d2 n) = n")
    apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
    prefer 2
    apply (metis get_labels_length)
   apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
   apply(rule_tac
      ?d1.0="(derivation_append d (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>1' @ cfg_conf v @ liftA \<beta>\<rparr>)) (length (map the (get_labels d na))))"
      and ?d2.0="(derivation_append d (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>1' @ cfg_conf v @ liftA \<beta>\<rparr>)) (length (map the (get_labels d na))))"
      and n="na+n"
      and ?v1.0="\<alpha>1'@v1"
      and ?B1.0="B1"
      and ?r1.0="r1@\<beta>"
      and ?v2.0="\<alpha>1'@v2"
      and ?B2.0="B2"
      and ?r2.0="r2@\<beta>"
      in cfgLM_positions_remain_compatible)
             apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
             apply(force)
            apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
            apply(force)
           apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
           apply(force)
          apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
          apply(force)
         apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
         apply(simp add: cfgLM.trans_der_def cfgLM.derivation_initial_def cfg_sub_def F_SDPDA_TO_CFG_STD_def valid_cfg_def cfg_configurations_def cfg_initial_configurations_def)
        apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
        apply(simp add: cfgLM.trans_der_def cfgLM.derivation_initial_def cfg_sub_def F_SDPDA_TO_CFG_STD_def valid_cfg_def cfg_configurations_def cfg_initial_configurations_def)
       apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
       apply(clarsimp)
       apply(force)
      apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
      apply(simp add: derivation_append_def derivation_map_def)
     apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
     apply(simp add: simpY)
    apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
    apply(simp add: simpY)
   apply(rename_tac d na \<alpha>1' \<beta> e ea)(*strict*)
   apply(force)
  apply(rename_tac d na \<alpha>1' \<beta>)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na \<alpha>1' \<beta> m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d na \<alpha>1' \<beta> m)(*strict*)
   prefer 2
   apply(simp add: equal_stacks_def equal_stack_def equal_front_states_def equal_front_state_def Let_def)
   apply(erule_tac
      x="0"
      in allE)+
   apply(clarsimp)
  apply(rename_tac d na \<alpha>1' \<beta> m)(*strict*)
  apply(clarsimp)
  apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
  apply(erule_tac
      x="k+na"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "length (get_labels d na) = na")
   apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
  apply(subgoal_tac "length (get_labels d1 n) = n")
   apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
  apply(subgoal_tac "length (get_labels d2 n) = n")
   apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(case_tac "d1 k")
   apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
   apply(clarsimp)
   apply(case_tac "d2 k")
    apply(rename_tac d na \<alpha>1' \<beta> m k)(*strict*)
    apply(clarsimp)
   apply(rename_tac d na \<alpha>1' \<beta> m k a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac a)
   apply(rename_tac d na \<alpha>1' \<beta> m k a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d na \<alpha>1' \<beta> m k a)(*strict*)
  apply(case_tac "d2 k")
   apply(rename_tac d na \<alpha>1' \<beta> m k a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac a)
   apply(rename_tac d na \<alpha>1' \<beta> m k a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d na \<alpha>1' \<beta> m k a aa)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(case_tac a)
  apply(rename_tac d na \<alpha>1' \<beta> m k a aa option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac d na \<alpha>1' \<beta> m k a aa option b optiona ba)(*strict*)
  apply(clarsimp)
  done

hide_fact cfgLM_trans_der_concat_extend_with_left_degen
hide_fact compatible_l3_productions_same_nonterminal_length_rhs
hide_fact compatible_l3_productions_same_nonterminal_rhs_are_equal
hide_fact cropTol3l2_drop_butn
hide_fact drop_and_crop_prefix1
hide_fact drop_and_crop_prefix2
hide_fact drop_and_crop_shift1
hide_fact drop_and_crop_shiftn
hide_fact drop_and_crop_shiftn_HELPXX
hide_fact eliminating_derivations_are_equal_with_differing_future1
hide_fact eliminating_derivations_are_equal_with_differing_future2
hide_fact eliminating_derivations_are_equal_with_differing_future3
hide_fact eliminating_derivations_are_equal_with_differing_future4
hide_fact eliminating_derivations_are_equal_with_differing_future5
hide_fact l3seq_drop_initial_state
hide_fact notfinishing_use
hide_fact only_prods_with_l3_nonterminals_reachable
hide_fact proper_l3_seq_drop
hide_fact proper_l3_seq_drop_front
hide_fact proper_l3_seq_drop_tail
hide_fact proper_l3_seq_inter_1
hide_fact proper_l3_seq_l3_adjacent
  (* important append_last_back_state_for_proper_l3_seq *)
  (* important cfgLMMIP_drop_leading_liftB *)
  (* important cfgLMMIy_cfgLMMIP_concatenation *)
  (* important cfgLM_positions_remain_compatible_l3l3 *)
  (* important cfgLM_positions_remain_compatible_prime *)
  (* important cfgLM_positions_remain_compatible_prime_prime *)
  (* important cfgLM_preserves_liftB_liftA_splitting *)
  (* important cfgLM_trans_der_concat_extend_prime_with_left_degen *)
  (* important cfgLM_trans_der_slice_prime *)
  (* important crop_cfgLMMP_to_cfgLMMIP *)
  (* important cropTol3l2_drop_butn_drop_and_crop *)
  (* important cropTol3l2_ID *)
  (* important cropTol3l2_length *)
  (* important cropTol3l2_makes_shorter *)
  (* important cropTol3l2_of_tail_of_proper_l3_l2_seq_ident *)
  (* important cropTol3l2_rest_is_junk *)
  (* important cropTol3l2_single_equal_from_cropTol3l2_equal *)
  (* important der1_left_degen *)
  (* important der2_left_degen *)
  (* important derivation_drop_preserves_left_degen *)
  (* important drop_and_crop_length *)
  (* important drop_and_crop_makes_shorter *)
  (* important drop_and_crop_preserves_l3_l2_separation *)
  (* important drop_and_crop_preserves_proper_l3_l2_seq *)
  (* important drop_and_crop_preserves_proper_l3_l2_seq2 *)
  (* important eliminating_derivations_are_equal_with_differing_future6 *)
  (* important enforceSuffixS_finite *)
  (* important enforceSuffixS_shift *)
  (* important enforceSuffixS_smaller *)
  (* important equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge *)
  (* important fillL_exists *)
  (* important fillOptL_cropTol3l2_last_back_state_if_l3_nonterminal *)
  (* important fillOptL_with_drop_and_crop_and_last_back_state_if_l3_nonterminal *)
  (* important fillOptL_with_last_back_state_if_l3_nonterminal_X *)
  (* important fillOpt_single_with_last_back_state_if_l3_nonterminal *)
  (* important l2_in_proper_l3_l2_seq_at_end *)
  (* important l2_production_not_in_F_SDPDA_TO_CFG_STD__edges_l3 *)
  (* important l3_l2_separation_ALT_to_only_l3_nonterminals *)
  (* important l3_l2_separation_append *)
  (* important l3_l2_separation_drop *)
  (* important l3_l2_separation_l2_at_front *)
  (* important l3_l2_separation_l3_at_front *)
  (* important l3_l2_separation_replace_front *)
  (* important l3_l2_separation_single *)
  (* important l3_production_not_in_F_SDPDA_TO_CFG_STD__edges_l2 *)
  (* important l3_seq_add_initial_state *)
  (* important l3seq_append *)
  (* important l3seq_append_decomp2 *)
  (* important l3seq_change_initial_state *)
  (* important l3seq_getSrc_getTrg *)
  (* important l3seq_l2end_append *)
  (* important l3seq_l2end_append_decomp2 *)
  (* important l3seq_l2end_getSrc_getTrg *)
  (* important l3seq_l2end_l2_at_end *)
  (* important last_back_state_empty *)
  (* important last_back_state_l3 *)
  (* important last_back_state_not_empty *)
  (* important left_degen_context_persists *)
  (* important left_degen_context_persists_prime *)
  (* important left_degen_drop_context *)
  (* important map_foldl_prefix_equal *)
  (* important map_foldl_prefix_equal_hlp *)
  (* important Min_enforceSuffixS_single *)
  (* important notfinishingL_drop *)
  (* important notfinishingL_drop2 *)
  (* important notfinishingL_foldl *)
  (* important notfinishingL_prefix *)
  (* important notfinishingL_take *)
  (* important notfinishingL_use *)
  (* important only_cfgLM_accessible_productions *)
  (* important only_l3_nonterminals_append *)
  (* important only_l3_nonterminals_append1 *)
  (* important only_l3_nonterminals_butlast *)
  (* important only_l3_nonterminals_butlast_butn *)
  (* important only_l3_nonterminals_drop *)
  (* important only_l3_nonterminals_l2_at_front *)
  (* important only_l3_nonterminals_nth_l2 *)
  (* important only_l3_nonterminals_reachable *)
  (* important only_l3_nonterminals_replace_front *)
  (* important only_l3_nonterminals_single *)
  (* important only_l3_nonterminals_take *)
  (* important only_l3_nonterminals_to_l3_l2_separation_ALT *)
  (* important prod_to_edge_liftA_liftB *)
  (* important proper_l3_l2_seq_drop *)
  (* important proper_l3_l2_seq_drop_prime *)
  (* important proper_l3_l2_seq_enlarge *)
  (* important proper_l3_l2_seq_nol2 *)
  (* important proper_l3_l2_seq_nol3 *)
  (* important proper_l3_l2_seq_preserved_by_drop_and_crop *)
  (* important proper_l3_l2_seq_proper_l3_seq_slice *)
  (* important proper_l3_l2_seq_replace_first *)
  (* important proper_l3_seq_compose2 *)
  (* important proper_l3_seq_drop_tail_X *)
  (* important proper_l3_seq_no_l2 *)
  (* important proper_l3_seq_take *)
  (* important take_drop_and_crop_id *)
  (* important take_unchanged_prefix_of_drop_and_crop *)

end
