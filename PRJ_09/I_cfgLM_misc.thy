section {*I\_cfgLM\_misc*}
theory
  I_cfgLM_misc

imports
  I_cfgLM_trans_der

begin

definition elim_map :: "('a,'b) cfg \<Rightarrow> 'a list \<Rightarrow> ('a,'b)cfg_step_label list list \<Rightarrow> 'b list list \<Rightarrow> bool" where
  "elim_map G' l f\<pi> fw \<equiv> \<forall>i<length l. \<exists>d n e.
  cfgLM.derivation G' d
  \<and> cfgLM.belongs G' d
  \<and> map the (get_labels d n) = (f\<pi>!i)
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (l!i)]\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB (fw!i)\<rparr>)
  "

lemma elim_map_compose: "
  elim_map G v1 f\<pi>1 fw1
  \<Longrightarrow> elim_map G v2 f\<pi>2 fw2
  \<Longrightarrow> length f\<pi>1=length v1
  \<Longrightarrow> length fw1=length v1
  \<Longrightarrow> length f\<pi>2=length v2
  \<Longrightarrow> length fw2=length v2
  \<Longrightarrow> v=v1@v2
  \<Longrightarrow> f\<pi>=f\<pi>1@f\<pi>2
  \<Longrightarrow> fw=fw1@fw2
  \<Longrightarrow> elim_map G v f\<pi> fw"
  apply(simp add: elim_map_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i<length v1")
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length v1 \<longrightarrow> (\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> (\<exists>n. map the (get_labels d n) = f\<pi>1 ! i \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (v1 ! i)]\<rparr>) \<and> (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (fw1 ! i)\<rparr>))))"
      in allE)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i d n e)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac i d n e)(*strict*)
    apply(rule sym)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(rule conjI)
    apply(rename_tac i d n e)(*strict*)
    apply(rule sym)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(rule_tac
      f="liftB"
      in HOL.arg_cong)
   apply(rule sym)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i-length v1"
      and P="\<lambda>x. x < length v2 \<longrightarrow> (\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> (\<exists>n. map the (get_labels d n) = f\<pi>2 ! x \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (v2 ! x)]\<rparr>) \<and> (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (fw2 ! x)\<rparr>))))"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(erule impE)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule sym)
   apply(rule_tac
      t="length v1"
      and s="length f\<pi>1"
      in ssubst)
    apply(rename_tac i d n e)(*strict*)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule sym)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      f="liftB"
      in HOL.arg_cong)
  apply(rule sym)
  apply(rule_tac
      t="length v1"
      and s="length fw1"
      in ssubst)
   apply(rename_tac i d n e)(*strict*)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule nth_append_2)
  apply(force)
  done

lemma elim_map_restrict2: "
  elim_map G v \<pi>s (map (\<lambda>x. []) w)
  \<Longrightarrow> length x=(length v-i)
  \<Longrightarrow> length \<pi>s=length v
  \<Longrightarrow> length v=length w
  \<Longrightarrow> i\<le>length v
  \<Longrightarrow> elim_map G (drop i v) (drop i \<pi>s) (map (\<lambda>x. []) x)"
  apply(simp add: elim_map_def)
  done

lemma elim_map_decompose2: "
  elim_map G v f\<pi> fw
  \<Longrightarrow> length f\<pi>1=length v1
  \<Longrightarrow> length fw1=length v1
  \<Longrightarrow> length f\<pi>2=length v2
  \<Longrightarrow> length fw2=length v2
  \<Longrightarrow> v=v1@v2
  \<Longrightarrow> f\<pi>=f\<pi>1@f\<pi>2
  \<Longrightarrow> fw=fw1@fw2
  \<Longrightarrow> elim_map G v2 f\<pi>2 fw2"
  apply(simp add: elim_map_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i+length v1"
      in allE)
  apply(clarsimp)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule_tac
      t="length v1"
      and s="length f\<pi>1"
      in ssubst)
    apply(rename_tac i d n e)(*strict*)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(rule_tac
      t="(f\<pi>1 @ f\<pi>2) ! (i + length f\<pi>1)"
      and s="(f\<pi>2) ! (i + length f\<pi>1 - length f\<pi>1)"
      in ssubst)
    apply(rename_tac i d n e)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule_tac
      t="(v1 @ v2) ! (i + length v1)"
      and s=" v2 ! (i + length v1 - length v1)"
      in ssubst)
    apply(rename_tac i d n e)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac i d n e)(*strict*)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      t="length v1"
      and s="length fw1"
      in ssubst)
   apply(rename_tac i d n e)(*strict*)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      t="(fw1 @ fw2) ! (i + length fw1)"
      and s=" fw2 ! (i + length fw1 - length fw1)"
      in ssubst)
   apply(rename_tac i d n e)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(force)
  done

lemma elim_map_restrict: "
  elim_map G v \<pi>s (map (\<lambda>x. []) w)
  \<Longrightarrow> length x=i
  \<Longrightarrow> length v=length w
  \<Longrightarrow> i\<le>length v
  \<Longrightarrow> elim_map G (take i v) (take i \<pi>s) (map (\<lambda>x. []) x)"
  apply(simp add: elim_map_def)
  done

lemma elim_map_from_elim_prod: "
  valid_cfg G
  \<Longrightarrow> prod_rhs e=[]
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> elim_map G [prod_lhs e] [[e]] [[]]"
  apply(simp add: elim_map_def)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (prod_lhs e)]\<rparr> e \<lparr>cfg_conf = []\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgLM.der2_is_derivation)
   apply(simp add: cfgLM_step_relation_def)
  apply(rule conjI)
   apply(rule cfgLM.der2_belongs)
     apply(simp add: cfg_configurations_def)
     apply(simp add: valid_cfg_def)
    apply(simp add: cfg_step_labels_def)
   apply(simp add: cfg_configurations_def)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply (metis der2_get_labels list.map_disc_iff map_eq_Cons_conv option.sel)
  apply(simp add: der2_def)
  done

lemma elim_combine: "
  valid_cfg G
  \<Longrightarrow> length w=length v
  \<Longrightarrow> length \<pi>s=length v
  \<Longrightarrow> elim_map G v \<pi>s (map (\<lambda>x. []) w)
  \<Longrightarrow> \<exists>d. cfgLM.derivation G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = liftA v\<rparr>) \<and> (\<exists>ea. d (length (foldl (@) [] \<pi>s)) = Some (pair ea \<lparr>cfg_conf = []\<rparr>)) \<and> get_labels d (length (foldl (@) [] \<pi>s)) = map Some (foldl (@) [] \<pi>s)"
  apply(induct v arbitrary: w \<pi>s)
   apply(rename_tac w \<pi>s)(*strict*)
   apply(clarsimp)
   apply(simp add: elim_map_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgLM.der1_is_derivation)
   apply(rule conjI)
    apply(simp add: der1_def)
   apply(rule conjI)
    apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac a v w \<pi>s)(*strict*)
  apply(clarsimp)
  apply(rename_tac vH vT w \<pi>s)
  apply(rename_tac vH vT w \<pi>s)(*strict*)
  apply(case_tac \<pi>s)
   apply(rename_tac vH vT w \<pi>s)(*strict*)
   apply(clarsimp)
  apply(rename_tac vH vT w \<pi>s a list)(*strict*)
  apply(rename_tac \<pi> \<pi>S)
  apply(rename_tac vH vT w \<pi>s \<pi> \<pi>S)(*strict*)
  apply(case_tac w)
   apply(rename_tac vH vT w \<pi>s \<pi> \<pi>S)(*strict*)
   apply(clarsimp)
  apply(rename_tac vH vT w \<pi>s \<pi> \<pi>S a list)(*strict*)
  apply(rename_tac wH wT)
  apply(rename_tac vH vT w \<pi>s \<pi> \<pi>S wH wT)(*strict*)
  apply(clarsimp)
  apply(rename_tac vH vT \<pi> \<pi>S wT)(*strict*)
  apply(erule_tac
      x="wT"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="\<pi>S"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac vH vT \<pi> \<pi>S wT)(*strict*)
   apply(simp add: elim_map_def)
   apply(clarsimp)
   apply(rename_tac vH vT \<pi> \<pi>S wT i)(*strict*)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
  apply(rename_tac vH vT \<pi> \<pi>S wT)(*strict*)
  apply(clarsimp)
  apply(rename_tac vH vT \<pi> \<pi>S wT d ea)(*strict*)
  apply(simp add: elim_map_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_map da (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@(liftA vT)\<rparr>)) d n"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(force)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(clarsimp)
     apply(rename_tac vH vT \<pi>S wT d ea da n e a eb b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac vH vT \<pi>S wT d ea da n e a eb b l r)(*strict*)
     apply(rule_tac
      x="l"
      in exI)
     apply(clarsimp)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(force)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule conjI)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule conjI)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(rule_tac
      x="if ((length (foldl (@) [] \<pi>S)))=0 then e else ea"
      in exI)
   apply(case_tac "((length (foldl (@) [] \<pi>S)))=0")
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(clarsimp)
    apply(rename_tac vH vT \<pi>S wT d da n e)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def)
    apply(subgoal_tac "length (get_labels da n)=n")
     apply(rename_tac vH vT \<pi>S wT d da n e)(*strict*)
     apply(case_tac \<pi>S)
      apply(rename_tac vH vT \<pi>S wT d da n e)(*strict*)
      apply(clarsimp)
     apply(rename_tac vH vT \<pi>S wT d da n e a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac vH vT wT d da n e a list)(*strict*)
     apply(case_tac vT)
      apply(rename_tac vH vT wT d da n e a list)(*strict*)
      prefer 2
      apply(rename_tac vH vT wT d da n e a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac vH vT wT d da n e a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac vH vT \<pi>S wT d da n e)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_map_def)
   apply(subgoal_tac "length (get_labels da n)=n")
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(rule conjI)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(rule impI)
     apply(subgoal_tac "False")
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(force)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(subgoal_tac "length (foldl (@) (map the (get_labels da n)) \<pi>S) > n")
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(force)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(rule_tac
      t="foldl (@) (map the (get_labels da n)) \<pi>S"
      and s="(map the (get_labels da n))@foldl (@) [] \<pi>S"
      in ssubst)
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply (metis foldl_first)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(rule_tac
      t="length (map the (get_labels da n) @ foldl (@) [] \<pi>S)"
      and s="length (map the (get_labels da n))+length (foldl (@) [] \<pi>S)"
      in ssubst)
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(force)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(clarsimp)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="length (foldl (@) (map the (get_labels da n)) \<pi>S) - n"
      and s="(length (foldl (@) [] \<pi>S))"
      in ssubst)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(rule_tac
      t="foldl (@) (map the (get_labels da n)) \<pi>S"
      and s="(map the (get_labels da n))@foldl (@) [] \<pi>S"
      in ssubst)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply (metis foldl_first)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(force)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule_tac
      t="(length (foldl (@) (map the (get_labels da n)) \<pi>S))"
      and s="n+(length (foldl (@) [] \<pi>S))"
      in ssubst)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(rule_tac
      t="foldl (@) (map the (get_labels da n)) \<pi>S"
      and s="(map the (get_labels da n))@foldl (@) [] \<pi>S"
      in ssubst)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply (metis foldl_first)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(subgoal_tac "length (get_labels da n)=n")
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    prefer 2
    apply (metis get_labels_length)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(force)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (derivation_map da (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA vT\<rparr>)) d n) (n + length (foldl (@) [] \<pi>S))"
      and s=" (get_labels (derivation_map da (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA vT\<rparr>)) n) @(get_labels d (length (foldl (@) [] \<pi>S)) ) "
      in ssubst)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(rule cfgLM.get_labels_concat2)
       apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
       apply(force)
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(rule cfgLM.derivation_map_preserves_derivation2)
       apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
       apply(force)
      apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
      apply(clarsimp)
      apply(rename_tac vH vT \<pi>S wT d ea da n e a eb b)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac vH vT \<pi>S wT d ea da n e a eb b l r)(*strict*)
      apply(rule_tac
      x="l"
      in exI)
      apply(clarsimp)
     apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
     apply(force)
    apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(force)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(foldl (@) (map the (get_labels da n)) \<pi>S)"
      and s=" ((map the (get_labels da n))) @((foldl (@) [] \<pi>S))"
      in ssubst)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply (metis foldl_first)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="get_labels (derivation_map da (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA vT\<rparr>)) n"
      and s="get_labels da n"
      in ssubst)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(rule get_labels_derivation_map)
  apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
  apply(rule listEqI)
   apply(rename_tac vH vT \<pi>S wT d ea da n e)(*strict*)
   apply(force)
  apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = n + 1 - Suc 0")
   apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq (Suc 0) n ! i"
      and s="Suc 0+i"
      in ssubst)
   apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
    apply(force)
   apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
   apply(force)
  apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. da (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
      apply(force)
     apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
     apply(force)
    apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
    apply(force)
   apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
   apply(force)
  apply(rename_tac vH vT \<pi>S wT d ea da n e i)(*strict*)
  apply(clarsimp)
  apply(rename_tac vH vT \<pi>S wT d ea da n e i eb c)(*strict*)
  apply(simp add: get_label_def)
  done

lemma equal_elim_front: "
  valid_cfg G
  \<Longrightarrow> length \<pi>s1\<le>length \<pi>s2
  \<Longrightarrow> length \<pi>s1\<le>length f
  \<Longrightarrow> elim_map G (take (length \<pi>s1) f) \<pi>s1 (map (\<lambda>x. []) \<pi>s1)
  \<Longrightarrow> elim_map G (take (length \<pi>s1) f) (take (length \<pi>s1) \<pi>s2) (map (\<lambda>x. []) \<pi>s1)
  \<Longrightarrow> foldl (@) [] \<pi>s1 @ x = foldl (@) [] \<pi>s2 @ y
  \<Longrightarrow> take i \<pi>s1 = take i ((take (length \<pi>s1) \<pi>s2))"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length \<pi>s1\<le>i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min i (length \<pi>s1) = (length \<pi>s1)")
    apply(rename_tac i)(*strict*)
    apply(subgoal_tac "min (Suc i) (length \<pi>s1) = (length \<pi>s1)")
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "i<length \<pi>s1")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min i (length \<pi>s1) = i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "min (Suc i) (length \<pi>s1) = Suc i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: elim_map_def)
  apply(erule_tac
      x="i"
      in allE)+
  apply(clarsimp)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = n + 1 - Suc 0")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) na) = na + 1 - Suc 0")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "n=length (\<pi>s1!i)")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="\<pi>s1!i"
      and s="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n)"
      in ssubst)
    apply(rename_tac i d da n na e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da n na e ea)(*strict*)
   apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n))"
      and s="length ((nat_seq (Suc 0) n))"
      in ssubst)
    apply(rename_tac i d da n na e ea)(*strict*)
    apply(rule length_map)
   apply(rename_tac i d da n na e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "na=length (\<pi>s2!i)")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="\<pi>s2!i"
      and s="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na)"
      in ssubst)
    apply(rename_tac i d da n na e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da n na e ea)(*strict*)
   apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na))"
      and s="length ((nat_seq (Suc 0) na))"
      in ssubst)
    apply(rename_tac i d da n na e ea)(*strict*)
    apply(rule length_map)
   apply(rename_tac i d da n na e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac i d da e ea)(*strict*)
  apply(subgoal_tac "strict_prefix (\<pi>s1!i) (\<pi>s2!i) \<or> strict_prefix (\<pi>s2!i) (\<pi>s1!i) \<or> (\<pi>s1!i=\<pi>s2!i)")
   apply(rename_tac i d da e ea)(*strict*)
   prefer 2
   apply(rule_tac
      px="foldl (@) [] (take i \<pi>s1)"
      and py="foldl (@) [] (take i \<pi>s2)"
      and pb="foldl (@) [] (drop (Suc i) \<pi>s1) @ x"
      and qb="foldl (@) [] (drop (Suc i) \<pi>s2) @ y"
      in mutual_strict_prefix_strict_prefix2)
    apply(rename_tac i d da e ea)(*strict*)
    apply(rule_tac
      t="foldl (@) [] (take i \<pi>s1) @ \<pi>s1 ! i @ foldl (@) [] (drop (Suc i) \<pi>s1) @ x"
      and s="foldl (@) [] \<pi>s1 @ x"
      in ssubst)
     apply(rename_tac i d da e ea)(*strict*)
     prefer 2
     apply(rule_tac
      t="foldl (@) [] (take i \<pi>s2) @ \<pi>s2 ! i @ foldl (@) [] (drop (Suc i) \<pi>s2) @ y"
      and s="foldl (@) [] \<pi>s2 @ y"
      in ssubst)
      apply(rename_tac i d da e ea)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i d da e ea)(*strict*)
     apply(clarsimp)
     apply(rule foldl_decomp)
     apply(force)
    apply(rename_tac i d da e ea)(*strict*)
    apply(simp (no_asm))
    apply(rule foldl_decomp)
    apply(force)
   apply(rename_tac i d da e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da e ea)(*strict*)
  apply(erule disjE)
   apply(rename_tac i d da e ea)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac i d da e ea)(*strict*)
    prefer 2
    apply(rule_tac
      t="take (Suc i) \<pi>s1"
      and s="take i \<pi>s1@[\<pi>s1!i]"
      in ssubst)
     apply(rename_tac i d da e ea)(*strict*)
     apply (metis take_n_vs_take_Suc_n)
    apply(rename_tac i d da e ea)(*strict*)
    apply(rule_tac
      t="take (Suc i) \<pi>s2"
      and s="take i \<pi>s2@[\<pi>s2!i]"
      in ssubst)
     apply(rename_tac i d da e ea)(*strict*)
     apply (rule sym, rule take_n_vs_take_Suc_n)
        apply(rename_tac i d da e ea)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac i d da e ea)(*strict*)
       apply(force)
      apply(rename_tac i d da e ea)(*strict*)
      apply(force)
     apply(rename_tac i d da e ea)(*strict*)
     apply(force)
    apply(rename_tac i d da e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da e ea)(*strict*)
   prefer 2
   apply(subgoal_tac "False")
    apply(rename_tac i d da e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da e ea)(*strict*)
   apply(rule_tac
      d="d"
      and da="da"
      and f="f"
      and G="G"
      and i="i"
      and ?\<pi>s1.0="\<pi>s1"
      and ?\<pi>s2.0="\<pi>s2"
      in sym_proof1)
              apply(rename_tac i d da e ea)(*strict*)
              apply(force)
             apply(rename_tac i d da e ea)(*strict*)
             apply(force)
            apply(rename_tac i d da e ea)(*strict*)
            apply(force)
           apply(rename_tac i d da e ea)(*strict*)
           apply(force)
          apply(rename_tac i d da e ea)(*strict*)
          apply(force)
         apply(rename_tac i d da e ea)(*strict*)
         apply(force)
        apply(rename_tac i d da e ea)(*strict*)
        apply(force)
       apply(rename_tac i d da e ea)(*strict*)
       apply(force)
      apply(rename_tac i d da e ea)(*strict*)
      apply(force)
     apply(rename_tac i d da e ea)(*strict*)
     apply(force)
    apply(rename_tac i d da e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da e ea)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac i d da e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da e ea)(*strict*)
  apply(rule_tac
      d="da"
      and da="d"
      and f="f"
      and G="G"
      and i="i"
      and ?\<pi>s1.0="\<pi>s2"
      and ?\<pi>s2.0="\<pi>s1"
      in sym_proof1)
             apply(rename_tac i d da e ea)(*strict*)
             apply(force)
            apply(rename_tac i d da e ea)(*strict*)
            apply(force)
           apply(rename_tac i d da e ea)(*strict*)
           apply(force)
          apply(rename_tac i d da e ea)(*strict*)
          apply(force)
         apply(rename_tac i d da e ea)(*strict*)
         apply(force)
        apply(rename_tac i d da e ea)(*strict*)
        apply(force)
       apply(rename_tac i d da e ea)(*strict*)
       apply(force)
      apply(rename_tac i d da e ea)(*strict*)
      apply(force)
     apply(rename_tac i d da e ea)(*strict*)
     apply(force)
    apply(rename_tac i d da e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da e ea)(*strict*)
  apply(force)
  done

lemma equal_elim_front_prime: "
  valid_cfg G
  \<Longrightarrow> length \<pi>s1\<le>length \<pi>s2
  \<Longrightarrow> length \<pi>s1\<le>length f
  \<Longrightarrow> elim_map G (take (length \<pi>s1) f) \<pi>s1 (map (\<lambda>x. []) \<pi>s1)
  \<Longrightarrow> elim_map G (take (length \<pi>s1) f) (take (length \<pi>s1) \<pi>s2) (map (\<lambda>x. []) \<pi>s1)
  \<Longrightarrow> foldl (@) [] \<pi>s1 @ x = foldl (@) [] \<pi>s2 @ y
  \<Longrightarrow> foldl (@) [] \<pi>s1 = foldl (@) [] ((take (length \<pi>s1) \<pi>s2))"
  apply(rule_tac
      f="\<lambda>w. foldl (@) [] w"
      in arg_cong)
  apply(subgoal_tac "take (length \<pi>s1) \<pi>s1 = take (length \<pi>s1) ((take (length \<pi>s1) \<pi>s2))")
   apply(force)
  apply(rule equal_elim_front)
       apply(force)+
  done

lemma elim_map_decompose1: "
  elim_map G v f\<pi> fw
  \<Longrightarrow> length f\<pi>1=length v1
  \<Longrightarrow> length fw1=length v1
  \<Longrightarrow> length f\<pi>2=length v2
  \<Longrightarrow> length fw2=length v2
  \<Longrightarrow> v=v1@v2
  \<Longrightarrow> f\<pi>=f\<pi>1@f\<pi>2
  \<Longrightarrow> fw=fw1@fw2
  \<Longrightarrow> elim_map G v1 f\<pi>1 fw1"
  apply(simp add: elim_map_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule conjI)
   apply(rename_tac i d n e)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i d n e)(*strict*)
  apply(rule_tac
      f="liftB"
      in HOL.arg_cong)
  apply(rule nth_append_1)
  apply(force)
  done

lemma elim_map_from_trans_der: "
  cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> \<pi> \<lparr>cfg_conf=liftB w\<rparr>
  \<Longrightarrow> elim_map G [A] [\<pi>] [w]"
  apply(simp add: cfgLM.trans_der_def elim_map_def)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule_tac
      x="length \<pi>"
      in exI)
  apply(clarsimp)
  done

lemma elim_map_to_trans_der: "
  valid_cfg G
  \<Longrightarrow> length ws=length \<pi>s
  \<Longrightarrow> length ws=length xs
  \<Longrightarrow> elim_map G ws \<pi>s (map (\<lambda>x. []) xs)
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftA ws\<rparr> (foldl (@) [] \<pi>s) \<lparr>cfg_conf=[]\<rparr>"
  apply(induct "length ws" arbitrary: ws xs \<pi>s)
   apply(rename_tac ws xs \<pi>s)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule cfgLM_trans_der_der1)
    apply(force)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac x ws xs \<pi>s)(*strict*)
  apply(case_tac ws)
   apply(rename_tac x ws xs \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac x ws xs \<pi>s a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs \<pi>s a list)(*strict*)
  apply(rename_tac w ws)
  apply(rename_tac xs \<pi>s w ws)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs \<pi>s w ws)(*strict*)
   apply(force)
  apply(rename_tac xs \<pi>s w ws a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>s w ws list)(*strict*)
  apply(rename_tac xs)
  apply(rename_tac \<pi>s w ws xs)(*strict*)
  apply(case_tac \<pi>s)
   apply(rename_tac \<pi>s w ws xs)(*strict*)
   apply(force)
  apply(rename_tac \<pi>s w ws xs a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w ws xs a list)(*strict*)
  apply(rename_tac \<pi> \<pi>s)
  apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
  apply(erule_tac
      x="ws"
      in meta_allE)
  apply(erule_tac
      x="xs"
      in meta_allE)
  apply(erule_tac
      x="\<pi>s"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(rule_tac
      t="ws"
      and s="drop (Suc 0) (w#ws)"
      in ssubst)
    apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(rule_tac
      t="\<pi>s"
      and s="drop (Suc 0) (\<pi>#\<pi>s)"
      in ssubst)
    apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(rule_tac
      w="(a#xs)"
      in elim_map_restrict2)
       apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
       apply(force)
      apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
      apply(force)
     apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
     apply(force)
    apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi> \<pi>s)(*strict*)
  apply(simp add: elim_map_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(rename_tac w ws xs \<pi>s d da n e)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA w]\<rparr> (map the (get_labels da n)) \<lparr>cfg_conf=[]\<rparr>")
   apply(rename_tac w ws xs \<pi>s d da n e)(*strict*)
   apply(clarsimp)
   apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
   apply(rule_tac
      t="foldl (@) (map the (get_labels da n)) \<pi>s"
      and s="map the (get_labels da n) @ foldl (@) [] \<pi>s"
      in ssubst)
    apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
    apply(rule foldl_first)
   apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
   apply(rule_tac
      t="teA w#liftA ws"
      and s="[teA w]@liftA ws"
      in ssubst)
    apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
   apply(rule_tac
      t="[]"
      and s="liftB []@[]"
      in ssubst)
    apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
   apply(rule cfgLM_trans_der_biextend_prime)
     apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
     apply(force)
    apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi>s d da n e db)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi>s d da n e)(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac w ws xs \<pi>s d da n e ea)(*strict*)
  apply(subgoal_tac "length (get_labels da n)=n")
   apply(rename_tac w ws xs \<pi>s d da n e ea)(*strict*)
   apply(clarsimp)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac w ws xs \<pi>s d da n e ea)(*strict*)
    apply(force)
   apply(rename_tac w ws xs \<pi>s d da n e ea)(*strict*)
   apply(force)
  apply(rename_tac w ws xs \<pi>s d da n e ea)(*strict*)
  apply (metis get_labels_length)
  done

lemma eliminating_derivation_to_elim_map: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w\<rparr> \<pi> \<lparr>cfg_conf = []\<rparr>
  \<Longrightarrow> \<exists>\<pi>s. length \<pi>s = length w \<and> elim_map G w \<pi>s (map (\<lambda>x. []) w) \<and> foldl (@) [] \<pi>s = \<pi>"
  apply(induct w arbitrary: \<pi> d)
   apply(rename_tac \<pi> d)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def elim_map_def)
   apply(clarsimp)
   apply(rename_tac \<pi> d e)(*strict*)
   apply(case_tac "\<pi>")
    apply(rename_tac \<pi> d e)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi> d e a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e a list)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac d e a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(length list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d e a list)(*strict*)
      apply(force)
     apply(rename_tac d e a list)(*strict*)
     apply(force)
    apply(rename_tac d e a list)(*strict*)
    apply(force)
   apply(rename_tac d e a list)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac a w \<pi> d)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 \<pi>1 \<pi>2. cfgLM.trans_der SSG d1 \<lparr>cfg_conf = SSw1\<rparr> \<pi>1 \<lparr>cfg_conf = []\<rparr> \<and> cfgLM.trans_der SSG d2 \<lparr>cfg_conf = SSw2\<rparr> \<pi>2 \<lparr>cfg_conf = []\<rparr> \<and> SSrenPI = \<pi>1 @ \<pi>2" for SSw1 SSG SSw2 SSrenPI)
   apply(rename_tac a w \<pi> d)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="[teA a]"
      and ?w2.0="liftA w"
      in cfgLM_decompose_eliminating_derivation_prime)
    apply(rename_tac a w \<pi> d)(*strict*)
    apply(force)
   apply(rename_tac a w \<pi> d)(*strict*)
   apply(force)
  apply(rename_tac a w \<pi> d)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>2)(*strict*)
  apply(erule_tac
      x="\<pi>2"
      in meta_allE)
  apply(erule_tac
      x="d2"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s)(*strict*)
  apply(rule_tac
      x="[\<pi>1]@\<pi>s"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s)(*strict*)
   prefer 2
   apply(rule foldl_first)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s)(*strict*)
  apply(simp add: elim_map_def)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s i)(*strict*)
  apply(case_tac i)
   apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s i)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s e ea eb)(*strict*)
   apply(rule_tac
      x="length \<pi>1"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>s i nat)(*strict*)
  apply(clarsimp)
  done

definition realizable :: "
  ('a,'b) cfg
  \<Rightarrow> ('a,'b)cfg_step_label list
  \<Rightarrow> ('a,'b)cfg_step_label list" where
  "realizable G \<pi> \<equiv>
    (THE \<pi>'. \<exists>c. prefix \<pi>' \<pi>
    \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA (prod_lhs(hd \<pi>))]\<rparr> \<pi>' c)
  \<and> (setA (cfg_conf c)={} \<or> \<pi>'=\<pi>))"

lemma realizable_not_empty: "
  valid_cfg G
  \<Longrightarrow> \<pi> \<noteq> []
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> realizable G \<pi> \<noteq> []"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?\<pi>1.0="[]"
      and ?\<pi>2.0="[]"
      in unique_existence_of_realizable_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(unfold realizable_def)
  apply(subgoal_tac "(THE \<pi>'. \<exists>c. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)) \<noteq> []")
   apply(rename_tac \<pi>' c da)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(thin_tac "(THE \<pi>'. \<exists>c. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)) = []")
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(rule_tac
      a="\<pi>'"
      in theI2)
    apply(rename_tac \<pi>' c da)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule conjI)
     apply(rename_tac \<pi>' c da)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' c da)(*strict*)
    apply(rule conjI)
     apply(rename_tac \<pi>' c da)(*strict*)
     apply(rule_tac
      x="da"
      in exI)
     apply(force)
    apply(rename_tac \<pi>' c da)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' c da x)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' c da x ca daa)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(erule_tac
      x="\<pi>'"
      in allE)
   apply(force)
  apply(rename_tac \<pi>' c da x)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' c da ca daa)(*strict*)
  apply(case_tac \<pi>)
   apply(rename_tac \<pi>' c da ca daa)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>' c da ca daa a list)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  done

lemma realizable_part_derives_empty_string: "
  valid_cfg G
  \<Longrightarrow> \<pi> \<noteq> []
  \<Longrightarrow> cfgLM.trans_der G d1 c1 \<pi> c2
  \<Longrightarrow> realizable G \<pi> \<noteq> \<pi>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA(prod_lhs(hd(\<pi>)))]\<rparr> (realizable G \<pi>) \<lparr>cfg_conf=w\<rparr>
  \<Longrightarrow> \<forall>i<length (\<pi>).
              \<exists>A. hd (cfg_conf (the (get_configuration (d1 i)))) = teA A
  \<Longrightarrow> w=[]"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?\<pi>1.0="[]"
      and ?\<pi>2.0="[]"
      in unique_existence_of_realizable_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(unfold realizable_def)
  apply(subgoal_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac \<pi>' c d)(*strict*)
   prefer 2
   apply(rule_tac
      t="\<pi>'"
      and s="(THE \<pi>'. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)))"
      in subst)
    apply(rename_tac \<pi>' c d)(*strict*)
    apply(rule_tac
      a="\<pi>'"
      in theI2)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>' c d)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(rule_tac
      x="c"
      in exI)
      apply(rule conjI)
       apply(rename_tac \<pi>' c d)(*strict*)
       apply(rule_tac
      x="d"
      in exI)
       apply(force)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' c d x)(*strict*)
     apply(erule_tac
      x="x"
      in allE)
     apply(erule_tac
      x="\<pi>'"
      in allE)
     apply(force)
    apply(rename_tac \<pi>' c d x)(*strict*)
    apply(erule_tac
      x="x"
      in allE)
    apply(erule_tac
      x="\<pi>'"
      in allE)
    apply(force)
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(thin_tac "\<forall>y y'. y \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = \<pi>)) \<and> y' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = \<pi>)) \<longrightarrow> y = y'")
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(thin_tac "(THE \<pi>'. \<exists>c. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)) \<noteq> \<pi>")
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> (THE \<pi>'. \<exists>c. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)) \<lparr>cfg_conf = w\<rparr>")
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(subgoal_tac "\<pi>' \<noteq> \<pi>")
   apply(rename_tac \<pi>' c d)(*strict*)
   prefer 2
   apply(rule_tac
      t="\<pi>'"
      and s="(THE \<pi>'. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)))"
      in subst)
    apply(rename_tac \<pi>' c d)(*strict*)
    apply(rule_tac
      a="\<pi>'"
      in theI2)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>' c d)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(rule_tac
      x="c"
      in exI)
      apply(rule conjI)
       apply(rename_tac \<pi>' c d)(*strict*)
       apply(rule_tac
      x="d"
      in exI)
       apply(force)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' c d x)(*strict*)
     apply(erule_tac
      x="x"
      in allE)
     apply(erule_tac
      x="\<pi>'"
      in allE)
     apply(force)
    apply(rename_tac \<pi>' c d x)(*strict*)
    apply(erule_tac
      x="x"
      in allE)
    apply(erule_tac
      x="\<pi>'"
      in allE)
    apply(force)
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(thin_tac "\<forall>y y'. y \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = \<pi>)) \<and> y' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = \<pi>)) \<longrightarrow> y = y'")
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(thin_tac "(THE \<pi>'. \<exists>c. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)) \<noteq> \<pi>")
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>' c d)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(subgoal_tac "c=\<lparr>cfg_conf=w\<rparr>")
   apply(rename_tac \<pi>' c d)(*strict*)
   prefer 2
   apply(subgoal_tac "d (length \<pi>') = d2 (length \<pi>')")
    apply(rename_tac \<pi>' c d)(*strict*)
    prefer 2
    apply(rule_tac
      ?\<pi>2.0="[]"
      in cfgLM_trans_der_coincide)
        apply(rename_tac \<pi>' c d)(*strict*)
        apply(force)
       apply(rename_tac \<pi>' c d)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' c d)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' c d)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' c d)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(force)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w")
   apply(rename_tac \<pi>' d)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac \<pi>' d)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac "l'=[]")
   apply(rename_tac \<pi>' d l')(*strict*)
   apply(force)
  apply(rename_tac \<pi>' d l')(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac \<pi>' d l')(*strict*)
   apply(force)
  apply(rename_tac \<pi>' d l')(*strict*)
  apply(case_tac l')
   apply(rename_tac \<pi>' d l')(*strict*)
   apply(force)
  apply(rename_tac \<pi>' d l' a list)(*strict*)
  apply(erule_tac x="0" in allE')
  apply(erule_tac
      x="length \<pi>'"
      in allE)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(subgoal_tac "\<pi>'\<noteq>[]")
   apply(rename_tac \<pi>' d a list A)(*strict*)
   prefer 2
   apply(subgoal_tac "realizable G \<pi> \<noteq> []")
    apply(rename_tac \<pi>' d a list A)(*strict*)
    prefer 2
    apply(rule realizable_not_empty)
      apply(rename_tac \<pi>' d a list A)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' d a list A)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' d a list A)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' d a list A)(*strict*)
   apply(unfold realizable_def)
   apply(rule_tac
      t="\<pi>'"
      and s="(THE \<pi>'. \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>)))"
      in subst)
    apply(rename_tac \<pi>' d a list A)(*strict*)
    apply(rule_tac
      a="\<pi>'"
      in theI2)
      apply(rename_tac \<pi>' d a list A)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>' d a list A)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' d a list A)(*strict*)
      apply(rule_tac
      x="\<lparr>cfg_conf=teB a # liftB list\<rparr>"
      in exI)
      apply(rule conjI)
       apply(rename_tac \<pi>' d a list A)(*strict*)
       apply(rule_tac
      x="d"
      in exI)
       apply(force)
      apply(rename_tac \<pi>' d a list A)(*strict*)
      apply(rule disjI1)
      apply(simp (no_asm) add: cfg_configurations_def setBConcat setA_liftB setB_liftB)
     apply(rename_tac \<pi>' d a list A x)(*strict*)
     apply(erule_tac
      x="x"
      in allE)
     apply(erule_tac
      x="\<pi>'"
      in allE)
     apply(erule_tac
      P="x \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> x c) \<and> (setA (cfg_conf c) = {} \<or> x = \<pi>)) \<and> \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>))"
      in impE)
      apply(rename_tac \<pi>' d a list A x)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>' d a list A x)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' d a list A x)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>' d a list A x)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' d a list A x)(*strict*)
      apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule_tac
      x="\<lparr>cfg_conf=teB a # liftB list\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule disjI1)
  apply(simp (no_asm) add: cfg_configurations_def setBConcat setA_liftB setB_liftB)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(erule_tac
      P="x \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> x c) \<and> (setA (cfg_conf c) = {} \<or> x = \<pi>)) \<and> \<pi>' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = \<pi>))"
      in impE)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule_tac
      x="\<lparr>cfg_conf=teB a # liftB list\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(force)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(rule disjI1)
  apply(simp (no_asm) add: cfg_configurations_def setBConcat setA_liftB setB_liftB)
  apply(rename_tac \<pi>' d a list A x)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(thin_tac "\<forall>y y'. y \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = \<pi>)) \<and> y' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = \<pi>)) \<longrightarrow> y = y'")
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(thin_tac "\<forall>y y'. y \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y c) \<and> (setA (cfg_conf c) = {} \<or> y = \<pi>)) \<and> y' \<sqsubseteq> \<pi> \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> y' c) \<and> (setA (cfg_conf c) = {} \<or> y' = \<pi>)) \<longrightarrow> y = y'")
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(erule impE)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 (length(\<pi>')) = Some (pair e c)")
  apply(rename_tac \<pi>' d a list A)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac \<pi>' d a list A e ea eb Aa)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
      m="length (\<pi>)"
      in cfgLM.pre_some_position_is_some_position)
  apply(rename_tac \<pi>' d a list A e ea eb Aa)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A e ea eb Aa)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A e ea eb Aa)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  apply(rename_tac \<pi>' d a list A)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>' d a list A Aa e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e cfg_confa)(*strict*)
  apply(rename_tac wx)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d1 c1 \<pi>' \<lparr>cfg_conf = wx\<rparr>")
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  prefer 2
  apply(rule_tac
      n="length(\<pi>')"
      in cfgLM.trans_der_crop)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(simp add: )
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>' d a list A Aa e wx cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac wy)
  apply(rename_tac \<pi>' d a list A Aa e wx wy)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
  apply(rename_tac \<pi>' d a list A Aa e wx wy)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
      m="length (\<pi>')"
      in cfgLM.step_detail_before_some_position)
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed)(*strict*)
  apply(simp add: prefix_def)
  apply(case_tac \<pi>')
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx wy ea eb ec ed aa lista)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list A Aa e wx wy)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 c1 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 c1 c2a l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 c1 c2a l r cfg_confa)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 c1 c2a l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 l r)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac l)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 l r)(*strict*)
  prefer 2
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 l r aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list A Aa e wx wy e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e wx wy e1 e2 r)(*strict*)
  apply(case_tac wx)
  apply(rename_tac \<pi>' d a list Aa e wx wy e1 e2 r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length \<pi>') = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r ea eb ec ed)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
      m="length (\<pi>)"
      in cfgLM.step_detail_before_some_position)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r ea eb ec ed)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r ea eb ec ed)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r ea eb ec ed)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e e2 r ea eb ec c)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>' d a list Aa e e2 r ea eb ec c)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list Aa e e2 r ea eb ec c aa lista)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r e2a c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac \<pi>' d a list Aa e wx wy e1 e2 r aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r lista)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r lista c)(*strict*)
  apply(case_tac \<pi>')
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r lista c)(*strict*)
  apply(force)
  apply(rename_tac \<pi>' d a list Aa e wy e1 e2 r lista c aa listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a list Aa e wy e1 e2 r lista c aa listb)(*strict*)
  apply(rename_tac \<pi>2 p \<pi>1)
  apply(rename_tac d a list Aa e wy e1 e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = teA (prod_lhs e2) # r\<rparr> = \<lparr>cfg_conf = wy\<rparr> \<and>e1 = None")
  apply(rename_tac d a list Aa e wy e1 e2 r lista \<pi>2 p \<pi>1)(*strict*)
  prefer 2
  apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac d a list Aa e wy e1 e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(subgoal_tac "e2=p")
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  prefer 2
  apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e e2 r lista \<pi>2 p \<pi>1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSv1 SSw2)
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  prefer 2
  apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  apply(simp add: )
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  apply(force)
  apply(rename_tac d a list Aa e r lista \<pi>2 p \<pi>1)(*strict*)
  apply(clarsimp)
  done

lemma realizable_eq_from_existence: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> \<pi> \<noteq> []
  \<Longrightarrow> \<pi>' \<sqsubseteq> \<pi>
  \<Longrightarrow> setA (cfg_conf ca) = {} \<or> \<pi>' = \<pi>
  \<Longrightarrow> cfgLM.trans_der G da \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>' ca
  \<Longrightarrow> realizable G \<pi> = \<pi>'"
  apply(subgoal_tac "X" for X)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in unique_existence_of_realizable)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(subgoal_tac "\<pi>'a = \<pi>'")
  apply(rename_tac \<pi>'a cb db)(*strict*)
  prefer 2
  apply(erule_tac
      x="\<pi>'a"
      in allE)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(force)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(clarify)
  apply(unfold realizable_def)
  apply(rule_tac
      a="\<pi>'"
      in theI2)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(force)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(force)
  apply(rename_tac \<pi>'a cb db)(*strict*)
  apply(force)
  apply(rename_tac \<pi>'a cb db x)(*strict*)
  apply(erule exE)+
  apply(rename_tac \<pi>'a cb db x caa)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac \<pi>'a cb db x caa daa)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(force)
  apply(rename_tac \<pi>'a cb db x)(*strict*)
  apply(erule exE)+
  apply(rename_tac \<pi>'a cb db x caa)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac \<pi>'a cb db x caa daa)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule_tac
      x="\<pi>'"
      in allE)
  apply(force)
  done

lemma realizable_prefix: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> prefix (realizable G \<pi>) \<pi>"
  apply(subgoal_tac "X" for X)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in existence_of_realizable)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' ca da)(*strict*)
  apply(rule_tac
      t="realizable G \<pi>"
      and s="\<pi>'"
      in ssubst)
  apply(rename_tac \<pi>' ca da)(*strict*)
  defer
  apply(force)
  apply(rename_tac \<pi>' ca da)(*strict*)
  apply(rule realizable_eq_from_existence)
  apply(rename_tac \<pi>' ca da)(*strict*)
  apply(force)+
  done

lemma realizable_rhs_one: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[teA A]
  \<Longrightarrow> cfgLM.trans_der G d c (p#\<pi>) c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> realizable G (p#\<pi>) = p#realizable G \<pi>"
  apply(rule_tac
      t="realizable G (p#\<pi>)"
      and s="(THE \<pi>'. \<pi>' \<sqsubseteq> (p # \<pi>) \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = p # \<pi>)))"
      in ssubst)
  apply(simp add: realizable_def)
  apply(subgoal_tac "X" for X)
  prefer 2
  apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(simp add: )
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d (Suc 0)) ci' \<pi> c'")
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule_tac
      t="\<pi>"
      and s="drop(Suc 0)(p#\<pi>)"
      in ssubst)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(rule cfgLM.trans_der_skip)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(rule_tac
      a="p#realizable G \<pi>"
      in the_equality)
  apply(rename_tac e ci')(*strict*)
  apply(rule conjI)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in realizable_prefix)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in existence_of_realizable)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(subgoal_tac "realizable G \<pi> = \<pi>'")
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  prefer 2
  apply(rule realizable_eq_from_existence)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' \<pi>' ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac e ci' ca da cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e ci' da w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' da w)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="d"
      and i="Suc 0"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e ci' da w)(*strict*)
  apply(simp add: )
  apply(rename_tac e ci' da w)(*strict*)
  apply(force)
  apply(rename_tac e ci' da w)(*strict*)
  apply(force)
  apply(rename_tac e ci' da w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da w ci'a)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ci' da w ci'a cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da w ci'a cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e da wa ci'a w)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a l r la ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac e da wa ci'a l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e da wa ci'a l r la ra)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB l"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e da wa ci'a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a r la ra l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
  apply(rename_tac e da wa ci'a r la ra l')(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB la"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e da wa ci'a r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a r ra l' l'a)(*strict*)
  apply(subgoal_tac "l'a=l'")
  apply(rename_tac e da wa ci'a r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a r l')(*strict*)
  apply(case_tac p)
  apply(rename_tac e da wa ci'a r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da wa ci'a r l' prod_lhsa)(*strict*)
  apply(rename_tac X)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  prefer 2
  apply(rule_tac
      ?w1.0="[teA X]"
      and ?\<pi>1.0="[\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (\<pi> ! 0))]\<rparr>]"
      and ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="der2 \<lparr>cfg_conf = [teA X]\<rparr> \<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (\<pi> ! 0))]\<rparr> \<lparr>cfg_conf = [teA (prod_lhs (\<pi> ! 0))]\<rparr>"
      and ?d2.0="da"
      in cfgLM_trans_der_concat_extend)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(simp add: )
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(clarsimp)
  apply(case_tac \<pi>)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(force)
  apply(rename_tac e da wa ci'a r l' X a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac cfgLM.trans_der_der2)
  apply(rename_tac e da wa ci'a r l' X a list)(*strict*)
  apply(force)
  apply(rename_tac e da wa ci'a r l' X a list)(*strict*)
  apply(simp add: cfg_configurations_def valid_cfg_def)
  apply(clarsimp)
  apply(force)
  apply(rename_tac e da wa ci'a r l' X a list)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = [teA X]\<rparr> \<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (\<pi> ! 0))]\<rparr> \<lparr>cfg_conf = [teA (prod_lhs (\<pi> ! 0))]\<rparr>) (derivation_map da (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ []\<rparr>)) (length [\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (\<pi> ! 0))]\<rparr>])"
      in exI)
  apply(rename_tac e da wa ci'a r l' X)(*strict*)
  apply(force)
  apply(rename_tac e da wa ci'a r ra l' l'a)(*strict*)
  apply (metis simple_identify)
  apply(rename_tac e ci' x)(*strict*)
  apply(case_tac x)
  apply(rename_tac e ci' x)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ci' x a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' a list ca da)(*strict*)
  apply(subgoal_tac "prefix list \<pi> \<and> a = p")
  apply(rename_tac e ci' a list ca da)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac e ci' a list ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' list ca da)(*strict*)
  apply(rule sym)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' list ca da)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="da"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e ci' list ca da)(*strict*)
  apply(simp add: )
  apply(rename_tac e ci' list ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop da (Suc 0)) ci'a list ca")
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  prefer 2
  apply(rule_tac
      t="list"
      and s="drop(Suc 0)(p#list)"
      in ssubst)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(rule cfgLM.trans_der_skip)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> = ci'a")
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(rule realizable_eq_from_existence)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(force)
  apply(rename_tac e ci' list ca da ea ci'a)(*strict*)
  apply(case_tac ci'a)
  apply(rename_tac e ci' list ca da ea ci'a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' list ca da ea cfg_confa)(*strict*)
  apply(case_tac list)
  apply(rename_tac e ci' list ca da ea cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea cfg_confa)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac ci' da cfg_conf eb ec)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac ci' da cfg_confa eb ec)(*strict*)
  apply(clarsimp)
  apply(rename_tac ci' da eb ec l la r ra)(*strict*)
  apply(case_tac la)
  apply(rename_tac ci' da eb ec l la r ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac ci' da eb ec l la r ra a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' list ca da ea cfg_confa a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="da"
      and i="Suc 0"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  apply(simp add: )
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  apply(force)
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  apply(force)
  apply(rename_tac e ci' ca da ea cfg_confa a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea cfg_confa a lista ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea a lista ci'a l la r ra lb rb)(*strict*)
  apply(case_tac la)
  apply(rename_tac e ci' ca da ea a lista ci'a l la r ra lb rb)(*strict*)
  prefer 2
  apply(rename_tac e ci' ca da ea a lista ci'a l la r ra lb rb aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea a lista ci'a l la r ra lb rb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea a lista ci'a l r lb rb)(*strict*)
  apply(case_tac lb)
  apply(rename_tac e ci' ca da ea a lista ci'a l r lb rb)(*strict*)
  prefer 2
  apply(rename_tac e ci' ca da ea a lista ci'a l r lb rb aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea a lista ci'a l r lb rb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca da ea a lista ci'a l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci' ca da ea a lista ci'a l r cfg_confa)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ci' ca da ea a lista ci'a l r cfg_confa cfg_confaa)(*strict*)
  apply(case_tac ci'a)
  apply(rename_tac e ci' ca da ea a lista ci'a l r cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e c da ea a lista l r)(*strict*)
  apply(case_tac \<pi>)
  apply(rename_tac e c da ea a lista l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e c da ea a lista l r aa list)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  done

lemma realizable_rhs_two_part1: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[teA A,teA B]
  \<Longrightarrow> cfgLM.trans_der G d c (p#\<pi>) c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> strict_prefix (realizable G \<pi>) \<pi>
  \<Longrightarrow> realizable G (p#\<pi>) = p#(if
  strict_prefix (realizable G \<pi>) \<pi>
  then
  (realizable G \<pi>)@(realizable G (drop(length(realizable G \<pi>))\<pi>))
  else
  \<pi>
  )"
  apply(subgoal_tac "X" for X)
  prefer 2
  apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(simp add: )
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d (Suc 0)) ci' \<pi> c'")
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule_tac
      t="\<pi>"
      and s="drop(Suc 0)(p#\<pi>)"
      in ssubst)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(rule cfgLM.trans_der_skip)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "prefix (realizable G \<pi>) \<pi>")
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule realizable_prefix)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci')(*strict*)
  prefer 2
  apply(rule_tac
      i="Suc(length (realizable G \<pi>))"
      in cfgLM.trans_der_position_detail)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci' ca caa)(*strict*)
  apply(rule_tac
      xs="caa"
      in rev_cases)
  apply(rename_tac e ci' ca caa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ca caa ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ca ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci' ca ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ca ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci')(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d (Suc(length(realizable G \<pi>)))) ci (drop (length (realizable G \<pi>)) \<pi>) c'")
  apply(rename_tac e ci' ci)(*strict*)
  prefer 2
  apply(rule_tac
      t="drop (length (realizable G \<pi>)) \<pi>"
      and s="drop(Suc(length(realizable G \<pi>)))(p#\<pi>)"
      in ssubst)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule_tac
      ?e1.0="Some ((p # \<pi>) ! length (realizable G \<pi>))"
      in cfgLM.trans_der_skip)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca caa)(*strict*)
  apply(rule_tac
      xs="caa"
      in rev_cases)
  apply(rename_tac e ci' ci ca caa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca caa ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci' ci)(*strict*)
  apply(subgoal_tac "prefix (realizable G (drop (length (realizable G \<pi>)) \<pi>)) SSX" for SSX)
  apply(rename_tac e ci' ci)(*strict*)
  prefer 2
  apply(rule realizable_prefix)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply (metis cfg_step_labels_def cfgLM_trans_der_prods)
  apply(rename_tac e ci' ci)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca caa)(*strict*)
  apply(rule_tac
      xs="caa"
      in rev_cases)
  apply(rename_tac e ci' ci ca caa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca caa ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule_tac
      t="realizable G (p#\<pi>)"
      and s="(THE \<pi>'. \<pi>' \<sqsubseteq> (p # \<pi>) \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = p # \<pi>)))"
      in ssubst)
  apply(rename_tac e ci' ci)(*strict*)
  apply(simp add: realizable_def)
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule_tac the_equality)
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule conjI)
  apply(rename_tac e ci' ci)(*strict*)
  apply(subgoal_tac "prefix (realizable G \<pi> @ realizable G (drop (length (realizable G \<pi>)) \<pi>)) (\<pi>)")
  apply(rename_tac e ci' ci)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule_tac
      t="(realizable G \<pi> @ realizable G (drop (length (realizable G \<pi>)) \<pi>)) \<sqsubseteq> \<pi>"
      and s="(realizable G \<pi> @ realizable G (drop (length (realizable G \<pi>)) \<pi>)) \<sqsubseteq> \<pi>"
      in ssubst)
  apply(rename_tac e ci' ci)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(rename_tac e ci' ci)(*strict*)
  apply(rule two_prefixes_are_prefix)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' ci)(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in existence_of_realizable)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(subgoal_tac "realizable G \<pi> = \<pi>'")
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  prefer 2
  apply(rule realizable_eq_from_existence)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci \<pi>' ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' ci ca da)(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="drop (length (realizable G \<pi>)) \<pi>"
      in existence_of_realizable)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply (metis cfg_step_labels_def cfgLM_trans_der_prods)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da caa cb cc)(*strict*)
  apply(rule_tac
      xs="caa"
      in rev_cases)
  apply(rename_tac e ci' ci ca da caa cb cc)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da caa cb cc ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da cb cc ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci' ci ca da cb cc ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da cb cc ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(subgoal_tac "realizable G (drop (length (realizable G \<pi>)) \<pi>) = \<pi>'")
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  prefer 2
  apply(rule realizable_eq_from_existence)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply (metis cfg_step_labels_def cfgLM_trans_der_prods)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da caa daa cb "cd")(*strict*)
  apply(rule_tac
      xs="cb"
      in rev_cases)
  apply(rename_tac e ci' ci ca da caa daa cb "cd")(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da caa daa cb "cd" ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da caa daa "cd" ys y)(*strict*)
  apply(subgoal_tac "length \<pi> > length (realizable G \<pi>)")
  apply(rename_tac e ci' ci ca da caa daa "cd" ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da caa daa "cd" ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci' ci ca da caa daa "cd" ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da caa daa "cd" ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci ca da \<pi>' caa daa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da caa daa)(*strict*)
  apply(erule_tac
      P="setA (cfg_conf ca) = {}"
      in disjE)
  apply(rename_tac e ci' ci ca da caa daa)(*strict*)
  prefer 2
  apply(simp add: strict_prefix_def prefix_def)
  apply(rename_tac e ci' ci ca da caa daa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e ci' ci ca da caa daa cfg_confa)(*strict*)
  apply(case_tac caa)
  apply(rename_tac e ci' ci ca da caa daa cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci da daa cfg_confa cfg_confaa)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac e ci' ci da daa w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w1")
  apply(rename_tac e ci' ci da daa w1 w2)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB w1"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci' ci da daa w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB l'@w2\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  prefer 2
  apply(erule disjE)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(rule disjI1)
  apply(simp add: setAConcat)
  apply(simp add: setA_liftB)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(rule disjI2)
  apply(rule two_prefixes_are_prefix_and_equal)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(force)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(force)
  apply(rename_tac e ci' ci da daa w2 l')(*strict*)
  apply(case_tac p)
  apply(rename_tac e ci' ci da daa w2 l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci da daa w2 l' prod_lhsa)(*strict*)
  apply(rename_tac X)
  apply(rename_tac e ci' ci da daa w2 l' X)(*strict*)
  apply(subgoal_tac "A = prod_lhs (hd \<pi>)")
  apply(rename_tac e ci' ci da daa w2 l' X)(*strict*)
  prefer 2
  apply(case_tac \<pi>)
  apply(rename_tac e ci' ci da daa w2 l' X)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="derivation_drop d (Suc 0)"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  apply(simp add: )
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci da daa w2 l' X a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea cia ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea cia ci'a l la r ra)(*strict*)
  apply(case_tac cia)
  apply(rename_tac e ci da daa w2 l' X a list ea cia ci'a l la r ra cfg_confa)(*strict*)
  apply(case_tac ci'a)
  apply(rename_tac e ci da daa w2 l' X a list ea cia ci'a l la r ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea l la r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci da daa w2 l' X a list ea l la r ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea l la r ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e ci da daa w2 l' X a list ea l la r ra)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB l"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci da daa w2 l' X a list ea l la r ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea la r ra l'a)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
  apply(rename_tac e ci da daa w2 l' X a list ea la r ra l'a)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB la"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci da daa w2 l' X a list ea la r ra l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea r ra l'a l'b)(*strict*)
  apply(subgoal_tac "l'a=l'b")
  apply(rename_tac e ci da daa w2 l' X a list ea r ra l'a l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X a list ea r ra l'a l'b)(*strict*)
  apply (metis identical_temrinal_maximal_prefix)
  apply(rename_tac e ci' ci da daa w2 l' X)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci da daa w2 l' X l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci' ci da daa w2 l' X l r cfg_confa)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ci' ci da daa w2 l' X l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e ci da daa w2 l' X l r)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB l"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci da daa w2 l' X l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "B = prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>))")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  prefer 2
  apply(case_tac "drop (length (realizable G \<pi>)) \<pi>")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca)(*strict*)
  apply(subgoal_tac "length \<pi> > length (realizable G \<pi>)")
  apply(rename_tac e ci da daa w2 l' X r l'a c ca)(*strict*)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca)(*strict*)
  apply(rule_tac
      xs="ca"
      in rev_cases)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca)(*strict*)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca ys y)(*strict*)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a c ca ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci da daa w2 l' X r l'a a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "ci=\<lparr>cfg_conf = liftB l'a @ liftB l' @ teA B # r\<rparr>")
  apply(rename_tac e ci da daa w2 l' X r l'a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="derivation_drop d (Suc (length (realizable G \<pi>)))"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  apply(simp add: )
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ci')(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ci' l ra)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e da daa w2 l' X r l'a a list ea ci' l ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea l ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e da daa w2 l' X r l'a a list ea l ra)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB l"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e da daa w2 l' X r l'a a list ea l ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra l'b)(*strict*)
  apply(subgoal_tac "l'a@l'=l'b")
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra l'b)(*strict*)
  apply(subgoal_tac "liftB (l'a @ l') @ teA B # r = liftB l'b @ teA (prod_lhs a) # ra")
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra l'b)(*strict*)
  apply (metis identical_temrinal_maximal_prefix)
  apply(rename_tac e da daa w2 l' X r l'a a list ea ra l'b)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a a list)(*strict*)
  apply(case_tac ci)
  apply(rename_tac e ci da daa w2 l' X r l'a a list cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (derivation_drop d (Suc (length (realizable G \<pi>)))) \<lparr>cfg_conf = w\<rparr> (a # list) c'")
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G daa \<lparr>cfg_conf = [teA (prod_lhs a)]\<rparr> (realizable G (a # list)) \<lparr>cfg_conf = w2\<rparr> ")
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(thin_tac "drop (length (realizable G \<pi>)) \<pi> = a # list")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  prefer 2
  apply(rule_tac
      n="length(realizable G \<pi>)"
      and d="derivation_drop d (Suc 0)"
      in cfgLM.trans_der_crop)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(simp add: )
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(rename_tac e da w2 l' X r l'a a list w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb)(*strict*)
  apply(subgoal_tac "length \<pi> > length (realizable G \<pi>)")
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb)(*strict*)
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb)(*strict*)
  apply(rule_tac
      xs="ca"
      in rev_cases)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb)(*strict*)
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb ys y)(*strict*)
  apply(rule_tac
      t="length \<pi>"
      and s="length (realizable G \<pi> @ ys @ [y])"
      in ssubst)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb ys y)(*strict*)
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w c ca cb ys y)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(rule conjI)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da w2 l' X r l'a a list)(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac e da w2 l' X r l'a a list c)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac da w2 l' X r l'a a list c ea)(*strict*)
  apply(case_tac l')
  apply(rename_tac da w2 l' X r l'a a list c ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac da w2 l' X r l'a a list c ea aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and v="l'a"
      and ?w2.0="[]"
      and ?d1.0="da"
      in cfgLM_trans_der_context_prime)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB l'a @ teA (prod_lhs (hd \<pi>)) # teA B # r\<rparr> \<in> cfg_configurations G")
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(rename_tac e da w2 l' X r l'a a list w)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply (metis cfgLM.trans_der_belongs_configurations1 cfgLM_trans_der_der1 )
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(force)
  apply(rename_tac e da daa w2 l' X r l'a a list w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="realizable G \<pi>"
      and ?w1.0="liftB l'a @[teA (prod_lhs (hd \<pi>))]"
      and ?w2.0="teA B # r"
      and ?d2.0="daa"
      and ?d1.0="derivation_drop d (Suc 0)"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  apply(rule_tac
      t="realizable G \<pi>"
      and s="(take (length (realizable G \<pi>)) \<pi>)"
      in ssubst)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  apply (metis prefix_def takePrecise)
  apply(rename_tac e da w2 l' X r l'a a list w daa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  prefer 2
  apply(rule_tac
      c'="\<lparr>cfg_conf=[teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>"
      and c="\<lparr>cfg_conf=[teA X]\<rparr>"
      and e="\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>"
      in cfgLM.trans_der_der2)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  prefer 2
  apply(simp add: cfgLM_step_relation_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(simp add: cfg_configurations_def valid_cfg_def)
  apply(clarsimp)
  apply(force)
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> \<in> cfg_productions G")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftB l'a @ teA X # r\<rparr> (\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> # \<pi>) c'")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "set \<pi> \<subseteq> cfg_productions G")
  apply(thin_tac "\<pi> \<noteq> []")
  apply(thin_tac "d 0 = Some (pair e \<lparr>cfg_conf = liftB l'a @ teA X # r\<rparr>)")
  apply(thin_tac "d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>) \<lparr>cfg_conf = liftB l'a @ teA (prod_lhs (hd \<pi>)) # teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>))) # r\<rparr>)")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (derivation_drop d (Suc 0)) \<lparr>cfg_conf = liftB l'a @ teA (prod_lhs (hd \<pi>)) # teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>))) # r\<rparr> \<pi> c'")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "d (Suc (length (realizable G \<pi>))) = Some (pair (Some ((\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> # \<pi>) ! length (realizable G \<pi>))) ci)")
  apply(rename_tac e ci da daa w2 l' X r l'a)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (derivation_drop d (Suc (length (realizable G \<pi>)))) ci (drop (length (realizable G \<pi>)) \<pi>) c'")
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(thin_tac "setA w2 = {} \<or> realizable G (drop (length (realizable G \<pi>)) \<pi>) = drop (length (realizable G \<pi>)) \<pi>")
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(thin_tac "realizable G (drop (length (realizable G \<pi>)) \<pi>) \<sqsubseteq> drop (length (realizable G \<pi>)) \<pi>")
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="[teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da w2 l' X)(*strict*)
  apply (metis cfgLM.trans_der_belongs_configurations1 cfgLM_trans_der_der1 )
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci d da w2 l' X r l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> (realizable G \<pi>) \<lparr>cfg_conf = liftB l'\<rparr>")
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac d da w2 l' X db)(*strict*)
  prefer 2
  apply(rule_tac
      ?w1.0="[teA X]"
      and ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="der2 \<lparr>cfg_conf = [teA X]\<rparr> \<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>"
      and ?d2.0="db"
      in cfgLM_trans_der_concat_extend_prime)
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(simp add: )
  apply(rename_tac d da w2 l' X db)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(clarsimp)
  apply(force)
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA X]\<rparr> \<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>) \<lparr>cfg_conf = [teA X]\<rparr> [\<lparr>prod_lhs = X, prod_rhs = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>] \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>")
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr> (realizable G \<pi>) \<lparr>cfg_conf = liftB l' @ [teA (prod_lhs (hd (drop (length (realizable G \<pi>)) \<pi>)))]\<rparr>")
  apply(rename_tac d da w2 l' X db)(*strict*)
  apply(clarsimp)
  apply(rename_tac da w2 l' X d)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac da w2 l' X d)(*strict*)
  prefer 2
  apply(rule_tac
      ?v1.0="l'"
      and ?v4.0="[]"
      and ?d1.0="d"
      and ?d2.0="da"
      in cfgLM_trans_der_concat_extend_prime)
  apply(rename_tac da w2 l' X d)(*strict*)
  apply(simp add: )
  apply(rename_tac da w2 l' X d)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac da w2 l' X d)(*strict*)
  apply(clarsimp)
  apply(force)
  apply(rename_tac da w2 l' X d)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci \<pi>')(*strict*)
  apply(case_tac \<pi>')
  apply(rename_tac e ci' ci \<pi>')(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci ca da)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci \<pi>' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci a list ca da)(*strict*)
  apply(subgoal_tac "a=p \<and> prefix list \<pi>")
  apply(rename_tac e ci' ci a list ca da)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac e ci' ci a list ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list ca da)(*strict*)
  apply(thin_tac "(p # list) \<sqsubseteq> (p # \<pi>)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci' ci list ca da)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and d="da"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
  apply(rename_tac e ci' ci list ca da)(*strict*)
  apply(simp add: )
  apply(rename_tac e ci' ci list ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci list ca da)(*strict*)
  apply(force)
  apply(rename_tac e ci' ci list ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list ca da ea ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ci' ci list ca da ea ci'a l la r ra)(*strict*)
  apply(case_tac la)
  apply(rename_tac e ci' ci list ca da ea ci'a l la r ra)(*strict*)
  prefer 2
  apply(rename_tac e ci' ci list ca da ea ci'a l la r ra a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list ca da ea ci'a l la r ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list ca da ea ci'a l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci' ci list ca da ea ci'a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list c da ea ci'a l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e ci' ci list c da ea ci'a l r)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB l"
      in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci' ci list c da ea ci'a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' ci list c da ea ci'a r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac ci')
  apply(rename_tac e ci' ci list c da ea ci'a r l' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list c da ea ci'a r l')(*strict*)
  apply(case_tac ci'a)
  apply(rename_tac e ci list c da ea ci'a r l' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  prefer 2
  apply(rule_tac
      t="\<pi>"
      and s="drop(Suc 0)(p#\<pi>)"
      in ssubst)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(rule_tac
      n="Suc 0"
      and d="da"
      in cfgLM.trans_der_skip_prime)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(force)
  apply(rename_tac e ci list c da ea r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list c da ea r l' daa)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci list c da ea r l' daa cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list da ea r l' daa cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and v="l'"
      and ?w2.0="[]"
      and ?d1.0="da"
      in cfgLM_trans_der_context_prime)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB l' @ teA (prod_lhs p) # r\<rparr> \<in> cfg_configurations G")
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply (metis cfgLM.trans_der_belongs_configurations1 cfgLM_trans_der_der1 )
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr> (p # list) \<lparr>cfg_conf = w\<rparr>")
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(thin_tac "da 0 = Some (pair ea \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr>)")
  apply(thin_tac "da (Suc 0) = Some (pair (Some p) \<lparr>cfg_conf = [teA A, teA B]\<rparr>)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  prefer 2
  apply(rule_tac
      \<pi>="\<pi>"
      in existence_of_realizable)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(force)
  apply(rename_tac e ci list da ea r l' daa w db)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
  apply(subgoal_tac "realizable G \<pi> = \<pi>'")
  apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
  prefer 2
  apply(rule realizable_eq_from_existence)
  apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
  apply(force)
       apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
       apply(force)
      apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
      apply(force)
     apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
     apply(force)
    apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
    apply(force)
   apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da w db \<pi>' c dc)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da w db c dc)(*strict*)
  apply(subgoal_tac "A = prod_lhs (hd \<pi>)")
   apply(rename_tac e ci list r l' da w db c dc)(*strict*)
   prefer 2
   apply(case_tac \<pi>)
    apply(rename_tac e ci list r l' da w db c dc)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="derivation_drop d (Suc 0)"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
      apply(simp add: )
     apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
     apply(force)
    apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
    apply(force)
   apply(rename_tac e ci list r l' da w db c dc a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista ea ci')(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista ea ci' l ra)(*strict*)
   apply(case_tac ci')
   apply(rename_tac e ci list r l' da w db c dc a lista ea ci' l ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista ea l ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac e ci list r l' da w db c dc a lista ea l ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac e ci list r l' da w db c dc a lista ea l ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista ea ra l'a)(*strict*)
   apply(subgoal_tac "l'=l'a")
    apply(rename_tac e ci list r l' da w db c dc a lista ea ra l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ci list r l' da w db c dc a lista ea ra l'a)(*strict*)
   apply (metis identical_temrinal_maximal_prefix)
  apply(rename_tac e ci list r l' da w db c dc)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      P="setA (cfg_conf c) = {}"
      in disjE)
   apply(rename_tac e ci list r l' da w db c dc)(*strict*)
   prefer 2
   apply(simp add: strict_prefix_def)
  apply(rename_tac e ci list r l' da w db c dc)(*strict*)
  apply(case_tac c)
  apply(rename_tac e ci list r l' da w db c dc cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da w db dc cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e ci list r l' da wa db dc w)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w")
  apply(rename_tac e ci list r l' da wa db dc w)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterB w"
    in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci list r l' da wa db dc w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(case_tac "strict_prefix list (realizable G \<pi>)")
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da wa db dc l'a c ca)(*strict*)
  apply(erule disjE)
  apply(rename_tac e ci list r l' da wa db dc l'a c ca)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ca)(*strict*)
  apply (metis append_self_conv mutual_prefix_implies_equality prefix_def)
  apply(rename_tac e ci list r l' da wa db dc l'a c ca)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = wa")
  apply(rename_tac e ci list r l' da wa db dc l'a c ca)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterB wa"
    in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci list r l' da wa db dc l'a c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
  apply(thin_tac "setA (liftB l'b) = {}")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
  prefer 2
  apply(rule_tac
    i="length list"
    and d="dc"
    in cfgLM.trans_der_position_detail)
    apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
    apply(force)
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
  apply(rule_tac
    t="realizable G \<pi>"
    and s="list @ ca"
    in ssubst)
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
  prefer 2
  apply(rule_tac
    n="length list"
    and d="dc"
    in cfgLM.trans_der_crop)
      apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
      apply(force)
     apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
     apply(force)
    apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
    apply(rule_tac
    t="realizable G \<pi>"
    and s="list @ ca"
    in ssubst)
     apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
     apply(force)
    apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia)(*strict*)
  apply(case_tac cia)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
  prefer 2
  apply(rule_tac
    \<pi>="list"
    and ?w1.0="[teA (prod_lhs (hd \<pi>))]"
    and ?w2.0="[teA B]"
    and ?d2.0="dc"
    and ?d1.0="da"
    in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
    apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
  apply(rule_tac
    t="list"
    and s="(take (length list) (realizable G \<pi>))"
    in ssubst)
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
   apply(rule_tac
    t="realizable G \<pi>"
    and s="list @ ca"
    in ssubst)
    apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cia cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cfg_conf)(*strict*)
  apply(rule_tac
    xs="l'b"
    in rev_cases)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da db dc l'a c ca l'b ea cfg_conf ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da db dc l'a c ca ea cfg_conf ys y)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(subgoal_tac "prefix (realizable G \<pi>) list")
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  prefer 2
  apply(rule_tac
    a="realizable G \<pi>"
    and b="list"
    and x="\<pi>"
    in strict_prefix_prefix_from_common_bigger)
   apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
   apply(force)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(erule_tac
    P="strict_prefix (realizable G \<pi>) list"
    in disjE)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(simp add: prefix_def strict_prefix_def)
  apply(force)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(erule_tac
    P="strict_prefix list (realizable G \<pi>)"
    in disjE)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(force)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(simp add: prefix_def strict_prefix_def)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(thin_tac "\<not> strict_prefix list (realizable G \<pi>)")
  apply(subgoal_tac "\<exists>c. realizable G \<pi> @ c = list")
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac e ci list r l' da wa db dc l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
  apply(thin_tac "realizable G \<pi> \<sqsubseteq> (realizable G \<pi> @ c)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
  prefer 2
  apply(rule_tac
    i="length (realizable G \<pi>)"
    and d="da"
    in cfgLM.trans_der_position_detail)
   apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci r l' da wa db dc l'a c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  prefer 2
  apply(rule_tac
    n="length (realizable G \<pi>)"
    and d="da"
    in cfgLM.trans_der_crop)
     apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
     apply(force)
    apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
    apply(force)
   apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  apply(thin_tac "(\<exists>y. ea = Some y) = (ea = Some ((realizable G \<pi> @ c) ! (length (realizable G \<pi>) - Suc 0)))")
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  apply(thin_tac "(realizable G \<pi> = []) = (ea = None)")
  apply(simp (no_asm_simp))
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia)(*strict*)
  apply(case_tac cia)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cia cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ea cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
  apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
  prefer 2
  apply(rule_tac
    \<pi>="realizable G \<pi>"
    and ?w1.0="[teA (prod_lhs (hd \<pi>))]"
    and ?w2.0="[teA B]"
    and ?d2.0="dc"
    and ?d1.0="da"
    in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
   apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  apply(thin_tac "(\<exists>y. ea = Some y) = (ea = Some ((realizable G \<pi> @ c) ! (length (realizable G \<pi>) - Suc 0)))")
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  apply(thin_tac "(realizable G \<pi> = []) = (ea = None)")
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  prefer 2
  apply(rule_tac
    n="length (realizable G \<pi>)"
    and d="da"
    in cfgLM.trans_der_skip_prime)
     apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
     apply(force)
    apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
    apply(force)
   apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  apply(subgoal_tac "B=prod_lhs (hd c)")
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  prefer 2
  apply(case_tac c)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca c)(*strict*)
  apply(case_tac c)
   apply(rename_tac e ci r l' da wa db dc l'a ea dca c)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac ci r l' da db dc l'a ea dca a list eb ec ed ee ef)(*strict*)
  apply(erule disjE)
   apply(rename_tac ci r l' da db dc l'a ea dca a list eb ec ed ee ef)(*strict*)
   apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(rename_tac ci r l' da db dc l'a ea dca a list eb ec ed ee ef)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    and d="dca"
    and i="0"
    and kleene_starT="True"
    and END="False"
    in cfgLM.trans_der_step_detail)
    apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
    apply(simp add: )
   apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ci')(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ci' l ra)(*strict*)
  apply(case_tac ci')
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ci' l ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l ra)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterB l"
    in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ra l'b)(*strict*)
  apply(subgoal_tac "l'a=l'b")
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ra l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ra l'b)(*strict*)
  apply(rule_tac
    xs="ra"
    in rev_cases)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ra l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b)(*strict*)
  apply(rule liftB_inj)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb ra l'b ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ys)(*strict*)
  apply(rule_tac
    xs="ys"
    in rev_cases)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ys)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b)(*strict*)
  apply(rule_tac
    xs="l'a"
    in rev_cases)
   apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b)(*strict*)
   apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc ea dca a list eb l'b ys y)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ys ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ysa y)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ysa y)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a ea dca a list eb l'b ysa y)(*strict*)
  apply(rule liftB_with_nonterminal_inside)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    d="dca"
    and i="0"
    and j="length c"
    in cfgLM.derivation_monotonically_inc)
      apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
      apply(force)
     apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
     apply(force)
    apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
    apply(force)
   apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca eb ec ed ee ef eg eh ei)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (liftB l'a @ [teA (prod_lhs (hd c))])=l'a")
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca w)(*strict*)
  prefer 2
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "p \<in> cfg_productions G")
  apply(thin_tac "prod_rhs p = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd c))]")
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftB l' @ teA (prod_lhs p) # r\<rparr> (p # \<pi>) c'")
  apply(thin_tac "set \<pi> \<subseteq> cfg_productions G")
  apply(thin_tac "\<pi> \<noteq> []")
  apply(thin_tac "strict_prefix (realizable G \<pi>) \<pi>")
  apply(thin_tac "d 0 = Some (pair e \<lparr>cfg_conf = liftB l' @ teA (prod_lhs p) # r\<rparr>)")
  apply(thin_tac "d (Suc 0) = Some (pair (Some p) \<lparr>cfg_conf = liftB l' @ teA (prod_lhs (hd \<pi>)) # teA (prod_lhs (hd c)) # r\<rparr>)")
  apply(thin_tac "cfgLM.trans_der G (derivation_drop d (Suc 0)) \<lparr>cfg_conf = liftB l' @ teA (prod_lhs (hd \<pi>)) # teA (prod_lhs (hd c)) # r\<rparr> \<pi> c'")
  apply(thin_tac "d (Suc (length (realizable G \<pi>))) = Some (pair (Some ((p # \<pi>) ! length (realizable G \<pi>))) ci)")
  apply(thin_tac "cfgLM.trans_der G (derivation_drop d (Suc (length (realizable G \<pi>)))) ci (drop (length (realizable G \<pi>)) \<pi>) c'")
  apply(rename_tac e ci r l' da wa db d l'a c ea dc w)(*strict*)
  apply(thin_tac "realizable G (drop (length (realizable G \<pi>)) \<pi>) \<sqsubseteq> drop (length (realizable G \<pi>)) \<pi>")
  apply(thin_tac "setA wa = {} \<or> realizable G \<pi> @ c = \<pi>")
  apply(thin_tac "(realizable G \<pi> @ c) \<sqsubseteq> \<pi>")
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd c))]\<rparr> (realizable G \<pi> @ c) \<lparr>cfg_conf = wa\<rparr>")
  apply(thin_tac "cfgLM.trans_der G db \<lparr>cfg_conf = liftB l' @ [teA (prod_lhs p)]\<rparr> (p # realizable G \<pi> @ c) \<lparr>cfg_conf = liftB l' @ wa\<rparr>")
  apply(thin_tac "realizable G \<pi> \<sqsubseteq> \<pi>")
  apply(thin_tac "da (length (realizable G \<pi>)) = Some (pair ea \<lparr>cfg_conf = liftB l'a @ [teA (prod_lhs (hd c))]\<rparr>)")
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA (prod_lhs (hd c))]\<rparr> (realizable G \<pi>) \<lparr>cfg_conf = liftB l'a @ [teA (prod_lhs (hd c))]\<rparr>")
  apply(thin_tac "maxTermPrefix (liftB l'a @ [teA (prod_lhs (hd c))]) @ w = maxTermPrefix wa")
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> (realizable G \<pi>) \<lparr>cfg_conf = liftB l'a\<rparr>")
  apply(rename_tac e ci r l' da wa db d l'a c ea dc w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dc \<lparr>cfg_conf = liftB l'a @ [teA (prod_lhs (hd c))]\<rparr> c \<lparr>cfg_conf = wa\<rparr>")
  apply(rename_tac e ci r l' da wa db d l'a c ea dc w)(*strict*)
  apply (metis append_Nil2 maxTermPrefix_shift maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix (liftB(l'a@w)) wa")
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca w)(*strict*)
  prefer 2
  apply (metis maxTermPrefix_mixed_string maxTermPrefix_shift prefix_of_maxTermPrefix_is_terminal_string_prefix)
  apply(rename_tac e ci r l' da wa db dc l'a c ea dca w)(*strict*)
  apply(thin_tac "maxTermPrefix (liftB l'a @ [teA (prod_lhs (hd c))]) = l'a")
  apply(thin_tac "l'a @ w = maxTermPrefix wa")
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd")(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd")(*strict*)
  prefer 2
  apply(rule_tac
    \<alpha>="l'a"
    and d="dca"
    in cfgLM_trans_der_drop_leading_terminals_prime)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd")(*strict*)
  apply(simp add: )
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd")(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(case_tac "realizable G \<pi> @ c = \<pi>")
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="drop (length (realizable G \<pi>)) \<pi>"
    and s="c"
    in ssubst)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(rule_tac
    P="\<lambda>X. drop (length (realizable G \<pi>)) X=c"
    and s="realizable G \<pi> @ c"
    in ssubst)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(rule sym)
  apply(rule_tac
    d="dca"
    in realizable_eq_from_existence)
       apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
       apply(force)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
      apply(force)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
     apply(rule_tac
    B="set \<pi>"
    in subset_trans)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
      apply(rule_tac
    t="\<pi>"
    and s="realizable G \<pi> @ c"
    in ssubst)
       apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
       apply(force)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
     apply(force)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
    apply(case_tac "c=[]")
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ci r l' da db dc l'a ea dca w "cd" dd)(*strict*)
     apply(simp add: strict_prefix_def)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
    apply(force)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(rule disjI2)
  apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = cd")
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  prefer 2
  apply(rule_tac
    x="filterB cd"
    in exI)
  apply (rule liftBDeConv2)
  apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc "cd" dd)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc dd l'b)(*strict*)
  apply(thin_tac "setA (liftB l'b) = {}")
  apply(subgoal_tac "cc=c@cb")
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc dd l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(subgoal_tac "realizable G (c@cb) @ ca = c@cb")
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(thin_tac "realizable G (drop (length (realizable G \<pi>)) \<pi>) @ ca = drop (length (realizable G \<pi>)) \<pi>")
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(rule_tac
    t="drop (length (realizable G \<pi>)) \<pi>"
    and s="c@cb"
    in ssubst)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
   prefer 2
   apply(rule sym)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
    prefer 2
    apply(rule_tac
    n="Suc (length(realizable G \<pi>))"
    and d="d"
    in cfgLM.trans_der_skip_prime)
        apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
        apply(force)
       apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
       apply(force)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
      apply(force)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
     apply(rule_tac
    P="\<lambda>X. Suc (length (realizable G \<pi>)) \<le> length (p # X)"
    and s="realizable G \<pi> @ c @ cb"
    in ssubst)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
      apply(force)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
    apply(force)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
   apply(rule_tac
    d="de"
    and da="dd"
    and ca="\<lparr>cfg_conf = liftB w @ liftB l'b\<rparr>"
    in realizable_eq_from_existence)
         apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
         apply(force)
        apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
        apply(rule_tac
    t="c@cb"
    and s="(drop (length (realizable G \<pi>)) \<pi>)"
    in ssubst)
         apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
         apply(rule_tac
    P="\<lambda>X. c @ cb = drop (length (realizable G \<pi>)) X"
    and s="realizable G \<pi> @ c @ cb"
    in ssubst)
          apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
          apply(force)
         apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
         apply(simp (no_asm))
        apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
        apply(force)
       apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
       apply(rule_tac
    B="set \<pi>"
    in subset_trans)
        apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
        apply(rule_tac
    t="\<pi>"
    and s="realizable G \<pi> @ c @cb"
    in ssubst)
         apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
         apply(force)
        apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
        apply(simp (no_asm))
       apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
       apply(force)
      apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
      apply(force)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
     apply(simp add: prefix_def)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
    apply(rule disjI1)
    prefer 2
    apply(rule_tac
    t="hd (c @ cb)"
    and s="hd c"
    in ssubst)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
    apply(case_tac c)
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
     prefer 2
     apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ci r l' da db dc l'a ea dca w ca cb dd l'b de)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac ci r l' da db dc l'a ea dca w ca cb dd l'b de eb ec ed ee ef ei)(*strict*)
    apply(case_tac w)
     apply(rename_tac ci r l' da db dc l'a ea dca w ca cb dd l'b de eb ec ed ee ef ei)(*strict*)
     apply(clarsimp)
     apply(rename_tac ci r l' da db dc l'a ea dca ca cb dd l'b de eb ec ed ee ef ei)(*strict*)
     apply(case_tac l'b)
      apply(rename_tac ci r l' da db dc l'a ea dca ca cb dd l'b de eb ec ed ee ef ei)(*strict*)
      apply(clarsimp)
     apply(rename_tac ci r l' da db dc l'a ea dca ca cb dd l'b de eb ec ed ee ef ei a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac ci r l' da db dc l'a ea dca w ca cb dd l'b de eb ec ed ee ef ei a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b de)(*strict*)
   apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(rule_tac
    P="\<lambda>X. drop (length (realizable G \<pi>)) X = c @ cb"
    and s="realizable G \<pi> @ c @ cb"
    in ssubst)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(rule_tac
    t="c@cb"
    and s="drop (length (realizable G \<pi>)) \<pi>"
    in subst)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(rule_tac
    P="\<lambda>X. drop (length (realizable G \<pi>)) X = c @ cb"
    and s="realizable G \<pi> @ c @ cb"
    in ssubst)
   apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
   apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb dd l'b)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc dd l'b)(*strict*)
  apply(rule_tac
    w="realizable G \<pi>"
    in append_linj)
  apply(rule_tac
    t="realizable G \<pi> @ cc"
    and s="\<pi>"
    in ssubst)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc dd l'b)(*strict*)
  apply(force)
  apply(rename_tac e ci r l' da db dc l'a c ea dca w ca cb cc dd l'b)(*strict*)
  apply(force)
  done

lemma realizable_rhs_two_part2: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[teA A,teA B]
  \<Longrightarrow> cfgLM.trans_der G d c (p#\<pi>) c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> \<not> strict_prefix (realizable G \<pi>) \<pi>
  \<Longrightarrow> realizable G (p#\<pi>) = p#(if
  strict_prefix (realizable G \<pi>) \<pi>
  then
  (realizable G \<pi>)@(realizable G (drop(length(realizable G \<pi>))\<pi>))
  else
  \<pi>
  )"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(simp add: )
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e ci')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e ci')(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc 0"
      and d="d"
      in cfgLM.trans_der_skip_prime)
       apply(rename_tac e ci')(*strict*)
       apply(force)
      apply(rename_tac e ci')(*strict*)
      apply(force)
     apply(rename_tac e ci')(*strict*)
     apply(force)
    apply(rename_tac e ci')(*strict*)
    apply(force)
   apply(rename_tac e ci')(*strict*)
   apply(force)
  apply(rename_tac e ci')(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da)(*strict*)
  apply(subgoal_tac "realizable G \<pi> = \<pi>")
   apply(rename_tac e ci' da)(*strict*)
   prefer 2
   apply(subgoal_tac "prefix (realizable G \<pi>) \<pi>")
    apply(rename_tac e ci' da)(*strict*)
    apply(simp add: strict_prefix_def prefix_def)
    apply(clarsimp)
    apply(rename_tac e ci' da ca)(*strict*)
    apply(case_tac ca)
     apply(rename_tac e ci' da ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ci' da ca a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ci' da a list)(*strict*)
    apply(force)
   apply(rename_tac e ci' da)(*strict*)
   apply(rule realizable_prefix)
      apply(rename_tac e ci' da)(*strict*)
      apply(force)
     apply(rename_tac e ci' da)(*strict*)
     apply(force)
    apply(rename_tac e ci' da)(*strict*)
    apply(force)
   apply(rename_tac e ci' da)(*strict*)
   apply(force)
  apply(rename_tac e ci' da)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e ci' da)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="\<pi>"
      in unique_existence_of_realizable)
      apply(rename_tac e ci' da)(*strict*)
      apply(force)
     apply(rename_tac e ci' da)(*strict*)
     apply(force)
    apply(rename_tac e ci' da)(*strict*)
    apply(force)
   apply(rename_tac e ci' da)(*strict*)
   apply(force)
  apply(rename_tac e ci' da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
  apply(subgoal_tac "realizable G \<pi> = \<pi>'")
   apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
   prefer 2
   apply(rule realizable_eq_from_existence)
         apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
         apply(force)
        apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
        apply(force)
       apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
       apply(force)
      apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
      apply(force)
     apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
     apply(force)
    apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
    apply(force)
   apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
   apply(force)
  apply(rename_tac e ci' da \<pi>' ca daa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da ca daa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e ci' da ca daa)(*strict*)
   prefer 2
   apply(rule_tac
      c'="\<lparr>cfg_conf=[teA A, teA B]\<rparr>"
      and c="\<lparr>cfg_conf=[teA (prod_lhs p)]\<rparr>"
      and e="p"
      in cfgLM.trans_der_der2)
     apply(rename_tac e ci' da ca daa)(*strict*)
     apply(force)
    apply(rename_tac e ci' da ca daa)(*strict*)
    prefer 2
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac e ci' da ca daa)(*strict*)
   apply(simp add: cfg_configurations_def valid_cfg_def)
  apply(rename_tac e ci' da ca daa)(*strict*)
  apply(subgoal_tac "prod_lhs (hd \<pi>) = A")
   apply(rename_tac e ci' da ca daa)(*strict*)
   prefer 2
   apply(case_tac \<pi>)
    apply(rename_tac e ci' da ca daa)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ci' da ca daa a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e ci' da ca daa a list)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="da"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac e ci' da ca daa a list)(*strict*)
      apply(simp add: )
     apply(rename_tac e ci' da ca daa a list)(*strict*)
     apply(force)
    apply(rename_tac e ci' da ca daa a list)(*strict*)
    apply(force)
   apply(rename_tac e ci' da ca daa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e da ca daa a list ea ci ci'a)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e da ca daa a list ea ci ci'a l la r ra)(*strict*)
   apply(case_tac ci)
   apply(rename_tac e da ca daa a list ea ci ci'a l la r ra cfg_confa)(*strict*)
   apply(case_tac ci'a)
   apply(rename_tac e da ca daa a list ea ci ci'a l la r ra cfg_confa cfg_confaa)(*strict*)
   apply(case_tac c)
   apply(rename_tac e da ca daa a list ea ci ci'a l la r ra cfg_confa cfg_confaa cfg_confb)(*strict*)
   apply(clarsimp)
   apply(rename_tac e da c daa a list ea l la r ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac e da c daa a list ea l la r ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac e da c daa a list ea l la r ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac e da c daa a list ea la r ra l')(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = la")
    apply(rename_tac e da c daa a list ea la r ra l')(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB la"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac e da c daa a list ea la r ra l')(*strict*)
   apply(clarsimp)
   apply(rename_tac e da c daa a list ea r ra l' l'a)(*strict*)
   apply(subgoal_tac "l'a=l'")
    apply(rename_tac e da c daa a list ea r ra l' l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e da c daa a list ea r ra l' l'a)(*strict*)
   apply (metis simple_identify)
  apply(rename_tac e ci' da ca daa)(*strict*)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="[teA (prod_lhs p)]"
      and ?v1.0="[]"
      and ?v4.0="[teA B]"
      and ?d1.0="der2 \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr> p \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>)), teA B]\<rparr>"
      and ?d2.0="daa"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
     apply(simp add: )
    apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ci' da daa cfg_confa)(*strict*)
   apply(force)
  apply(rename_tac e ci' da ca daa cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
  apply(rule realizable_eq_from_existence)
        apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
        apply(force)
       apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
       apply(force)
      apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
      apply(force)
     apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
     apply(force)
    apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
    apply(simp (no_asm) add: prefix_def)
   apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
   apply(rule disjI2)
   apply(force)
  apply(rename_tac e ci' da daa cfg_confa db)(*strict*)
  apply(force)
  done

lemma realizable_rhs_two: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[teA A,teA B]
  \<Longrightarrow> cfgLM.trans_der G d c (p#\<pi>) c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> realizable G (p#\<pi>) = p#(if
  strict_prefix (realizable G \<pi>) \<pi>
  then
  (realizable G \<pi>)@(realizable G (drop(length(realizable G \<pi>))\<pi>))
  else
  \<pi>
  )"
  apply(case_tac "strict_prefix (realizable G \<pi>) \<pi>")
   apply(rule realizable_rhs_two_part1)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule realizable_rhs_two_part2)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma realizable_rhs_one_or_two: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[teA A] \<or> prod_rhs p=[teA A,teA B]
  \<Longrightarrow> cfgLM.trans_der G d c (p#\<pi>) c'
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0 < length \<pi>
  \<Longrightarrow> realizable G (p#\<pi>) = p#realizable G \<pi>@
(if (prod_rhs p=[teA A,teA B]) \<and> (strict_prefix (realizable G \<pi>) \<pi>)
then (realizable G (drop(length(realizable G \<pi>))\<pi>)) else [])"
  apply(erule disjE)
   apply(clarsimp)
   apply(rule realizable_rhs_one)
        apply(force)+
  apply(rule_tac
      t="p # realizable G \<pi> @ (if prod_rhs p = [teA A, teA B] \<and> strict_prefix (realizable G \<pi>) \<pi> then realizable G (drop (length (realizable G \<pi>)) \<pi>) else [])"
      and s="p#(if strict_prefix (realizable G \<pi>) \<pi> then (realizable G \<pi>)@(realizable G (drop(length(realizable G \<pi>))\<pi>)) else \<pi> )"
      in ssubst)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(simp add: )
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac e ci')(*strict*)
   apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d (Suc 0)) ci' \<pi> c'")
    apply(rename_tac e ci')(*strict*)
    prefer 2
    apply(rule_tac
      t="\<pi>"
      and s="drop(Suc 0)(p#\<pi>)"
      in ssubst)
     apply(rename_tac e ci')(*strict*)
     apply(force)
    apply(rename_tac e ci')(*strict*)
    apply(rule cfgLM.trans_der_skip)
       apply(rename_tac e ci')(*strict*)
       apply(force)
      apply(rename_tac e ci')(*strict*)
      apply(force)
     apply(rename_tac e ci')(*strict*)
     apply(force)
    apply(rename_tac e ci')(*strict*)
    apply(force)
   apply(rename_tac e ci')(*strict*)
   apply(subgoal_tac "realizable G \<pi> = \<pi>")
    apply(rename_tac e ci')(*strict*)
    prefer 2
    apply(subgoal_tac "prefix (realizable G \<pi>) \<pi>")
     apply(rename_tac e ci')(*strict*)
     apply(simp add: strict_prefix_def prefix_def)
     apply(clarsimp)
     apply(rename_tac e ci' ca)(*strict*)
     apply(case_tac ca)
      apply(rename_tac e ci' ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac e ci' ca a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ci' a list)(*strict*)
     apply(force)
    apply(rename_tac e ci')(*strict*)
    apply(rule realizable_prefix)
       apply(rename_tac e ci')(*strict*)
       apply(force)
      apply(rename_tac e ci')(*strict*)
      apply(force)
     apply(rename_tac e ci')(*strict*)
     apply(force)
    apply(rename_tac e ci')(*strict*)
    apply(force)
   apply(rename_tac e ci')(*strict*)
   apply(clarsimp)
  apply(rule realizable_rhs_two)
       apply(force)+
  done

lemma realizable_not_empty2: "
  valid_cfg G
  \<Longrightarrow> set (p#w) \<subseteq> cfg_productions G
  \<Longrightarrow> cfgLM.trans_der G d c1 (p#w) c2
  \<Longrightarrow> realizable G (p#w) = []
  \<Longrightarrow> Q"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<pi>="p#w"
      in existence_of_realizable)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(subgoal_tac "realizable G (p # w) = \<pi>'")
   apply(rename_tac \<pi>' c da)(*strict*)
   prefer 2
   apply(rule realizable_eq_from_existence)
         apply(rename_tac \<pi>' c da)(*strict*)
         apply(force)
        apply(rename_tac \<pi>' c da)(*strict*)
        apply(force)
       apply(rename_tac \<pi>' c da)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' c da)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' c da)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' c da)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' c da)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(clarsimp)
  apply(rename_tac c da)(*strict*)
  apply(simp add: prefix_def)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  done

lemma realizable_take_first_production: "
  valid_cfg G
  \<Longrightarrow> set (p#w) \<subseteq> cfg_productions G
  \<Longrightarrow> cfgLM.trans_der G d c1 (p#w) c2
  \<Longrightarrow> hd(realizable G (p#w)) = p"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<pi>="p#w"
      in existence_of_realizable)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(subgoal_tac "realizable G (p # w) = \<pi>'")
   apply(rename_tac \<pi>' c da)(*strict*)
   prefer 2
   apply(rule realizable_eq_from_existence)
         apply(rename_tac \<pi>' c da)(*strict*)
         apply(force)
        apply(rename_tac \<pi>' c da)(*strict*)
        apply(force)
       apply(rename_tac \<pi>' c da)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' c da)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' c da)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' c da)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' c da)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(clarsimp)
  apply(rename_tac c da)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c da ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac c da ca)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac c da ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac c da ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca cfg_conf)(*strict*)
  apply(rename_tac xx)
  apply(rename_tac da ca xx)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = xx")
   apply(rename_tac da ca xx)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB xx"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac da ca xx)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac "realizable G (p # w)")
   apply(rename_tac da ca l')(*strict*)
   apply(rule realizable_not_empty2)
      apply(rename_tac da ca l')(*strict*)
      apply(force)
     apply(rename_tac da ca l')(*strict*)
     apply(force)
    apply(rename_tac da ca l')(*strict*)
    apply(force)
   apply(rename_tac da ca l')(*strict*)
   apply(force)
  apply(rename_tac da ca l' a list)(*strict*)
  apply(force)
  done

lemma entire_realizable: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=w\<rparr>
  \<Longrightarrow> \<pi>1 \<noteq> []
  \<Longrightarrow> realizable G \<pi>1 = \<pi>1"
  apply(simp add: realizable_def)
  apply(rule_tac
      a="\<pi>1"
      in theI2)
    apply(rule conjI)
     apply(simp add: prefix_def)
    apply(clarsimp)
    apply(case_tac \<pi>1)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. d (length(a#list)) = Some (pair e c)")
     apply(rename_tac a list)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac a list e)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      m="length (a#list@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
       apply(rename_tac a list e)(*strict*)
       apply(force)
      apply(rename_tac a list e)(*strict*)
      apply(force)
     apply(rename_tac a list e)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac a list e c)(*strict*)
    apply(subgoal_tac "A=prod_lhs a")
     apply(rename_tac a list e c)(*strict*)
     prefer 2
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
      apply(rename_tac a list e c)(*strict*)
      prefer 2
      apply(unfold cfgLM.trans_der_def)
      apply(erule exE)+
      apply(rename_tac a list e c ea)(*strict*)
      apply(fold cfgLM.trans_der_def)
      apply(rule_tac
      m="length (a # list@\<pi>2)"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac a list e c ea)(*strict*)
        apply(force)
       apply(rename_tac a list e c ea)(*strict*)
       apply(force)
      apply(rename_tac a list e c ea)(*strict*)
      apply(force)
     apply(rename_tac a list e c)(*strict*)
     apply(clarsimp)
     apply(rename_tac a list e c e1 e2 c1 c2)(*strict*)
     apply(subgoal_tac "c1=\<lparr>cfg_conf = [teA A]\<rparr>")
      apply(rename_tac a list e c e1 e2 c1 c2)(*strict*)
      prefer 2
      apply(simp add: cfgLM.trans_der_def)
     apply(rename_tac a list e c e1 e2 c1 c2)(*strict*)
     apply(clarsimp)
     apply(rename_tac a list e c e1 e2 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac a list e c e1 e2 c2 l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac a list e c e1 e2 c2 l r)(*strict*)
      prefer 2
      apply(rename_tac a list e c e1 e2 c2 l r aa lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac a list e c e1 e2 c2 l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac a list e c e1 e2 c2)(*strict*)
     apply(subgoal_tac "e2=a")
      apply(rename_tac a list e c e1 e2 c2)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
          apply(rename_tac a list e c e1 e2 c2)(*strict*)
          apply(force)
         apply(rename_tac a list e c e1 e2 c2)(*strict*)
         apply(force)
        apply(rename_tac a list e c e1 e2 c2)(*strict*)
        apply(force)
       apply(rename_tac a list e c e1 e2 c2)(*strict*)
       apply(force)
      apply(rename_tac a list e c e1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac a list e c e1 e2 c2)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list e c)(*strict*)
    apply(clarsimp)
    apply(case_tac "\<pi>2=[]")
     apply(rename_tac a list e c)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "c=\<lparr>cfg_conf = w\<rparr>")
      apply(rename_tac a list e c)(*strict*)
      apply(clarsimp)
      apply(rename_tac a list e)(*strict*)
      apply(force)
     apply(rename_tac a list e c)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac a list e c)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule_tac
      x="d"
      in exI)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule_tac
      m="length(\<pi>2)"
      and v="map Some (\<pi>2)"
      in get_labels_drop_tail)
     apply(rename_tac a list e c)(*strict*)
     apply(force)
    apply(rename_tac a list e c)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule entire_realizable_hlp)
      apply(rename_tac x)(*strict*)
      apply(force)+
  apply(rename_tac x)(*strict*)
  apply(rule entire_realizable_hlp)
     apply(rename_tac x)(*strict*)
     apply(force)+
  done

lemma realizable_rhs_empty: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_rhs p=[]
  \<Longrightarrow> realizable G (p#\<pi>) = [p]"
  apply(simp add: realizable_def)
  apply(rule_tac
      a="[p]"
      in theI2)
    apply(simp add: prefix_def)
    apply(rule_tac
      x="\<lparr>cfg_conf=[]\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (prod_lhs p)]\<rparr> p \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(case_tac p)
    apply(rename_tac prod_lhsa prod_rhsa)(*strict*)
    apply(clarsimp)
    apply(rename_tac prod_lhs)(*strict*)
    apply(rule cfgLM.trans_der_der2)
      apply(rename_tac prod_lhs)(*strict*)
      apply(force)
     apply(rename_tac prod_lhs)(*strict*)
     apply(simp add: cfg_configurations_def valid_cfg_def)
     apply(rename_tac prod_lhsa)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac prod_lhs)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x c d)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x c d ca)(*strict*)
   apply(case_tac x)
    apply(rename_tac x c d ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
   apply(rename_tac x c d ca a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d ca list)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c d ca list)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac c d ca list)(*strict*)
      apply(simp add: )
     apply(rename_tac c d ca list)(*strict*)
     apply(force)
    apply(rename_tac c d ca list)(*strict*)
    apply(force)
   apply(rename_tac c d ca list)(*strict*)
   apply(case_tac list)
    apply(rename_tac c d ca list)(*strict*)
    apply(force)
   apply(rename_tac c d ca list a lista)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c d ca list a lista)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and i="Suc 0"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac c d ca list a lista)(*strict*)
      apply(simp add: )
     apply(rename_tac c d ca list a lista)(*strict*)
     apply(force)
    apply(rename_tac c d ca list a lista)(*strict*)
    apply(force)
   apply(rename_tac c d ca list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d ca a lista e cia ci'a)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c d ca a lista e cia ci'a l r la ra)(*strict*)
   apply(case_tac l)
    apply(rename_tac c d ca a lista e cia ci'a l r la ra)(*strict*)
    prefer 2
    apply(rename_tac c d ca a lista e cia ci'a l r la ra aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac c d ca a lista e cia ci'a l r la ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x c ca d)(*strict*)
  apply(case_tac x)
   apply(rename_tac x c ca d)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x c ca d a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ca d list)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c ca d list)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac c ca d list)(*strict*)
     apply(simp add: )
    apply(rename_tac c ca d list)(*strict*)
    apply(force)
   apply(rename_tac c ca d list)(*strict*)
   apply(force)
  apply(rename_tac c ca d list)(*strict*)
  apply(case_tac list)
   apply(rename_tac c ca d list)(*strict*)
   apply(force)
  apply(rename_tac c ca d list a lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c ca d list a lista)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="Suc 0"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac c ca d list a lista)(*strict*)
     apply(simp add: )
    apply(rename_tac c ca d list a lista)(*strict*)
    apply(force)
   apply(rename_tac c ca d list a lista)(*strict*)
   apply(force)
  apply(rename_tac c ca d list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ca d a lista e cia ci'a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c ca d a lista e cia ci'a l r la ra)(*strict*)
  apply(case_tac l)
   apply(rename_tac c ca d a lista e cia ci'a l r la ra)(*strict*)
   prefer 2
   apply(rename_tac c ca d a lista e cia ci'a l r la ra aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ca d a lista e cia ci'a l r la ra)(*strict*)
  apply(clarsimp)
  done

lemma realizable_single: "
  valid_cfg G
  \<Longrightarrow> p\<in> cfg_productions G
  \<Longrightarrow> realizable G [p] = [p]"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      c'="\<lparr>cfg_conf=prod_rhs p\<rparr>"
      and c="\<lparr>cfg_conf=[teA (prod_lhs p)]\<rparr>"
      and e="p"
      in cfgLM.trans_der_der2)
     apply(force)
    prefer 2
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(simp add: cfg_configurations_def valid_cfg_def)
  apply(rule realizable_eq_from_existence)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: prefix_def)
   apply(rule disjI2)
   apply(force)
  apply(force)
  done

lemma realizable_single_if_first_prod_has_empty_rhs: "
  valid_cfg G
  \<Longrightarrow> set (p#\<pi>) \<subseteq> cfg_productions G
  \<Longrightarrow> p=\<lparr>prod_lhs=A,prod_rhs=[]\<rparr>
  \<Longrightarrow> realizable G (p#\<pi>) = [p]"
  apply(clarsimp)
  apply(simp add: realizable_def)
  apply(rule the_equality)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(rule_tac
      x="\<lparr>cfg_conf=[]\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = []\<rparr> \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule cfgLM.trans_der_der2)
     apply(force)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="X" for X
      in ballE)
     prefer 2
     apply(force)
    apply(simp add: cfg_configurations_def)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac \<pi>')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' c d)(*strict*)
  apply(case_tac "\<pi>'")
   apply(rename_tac \<pi>' c d)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac \<pi>' c d a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d a list)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c d list ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac c d list ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d list ca cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d list ca w)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d list ca w)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac d list ca w)(*strict*)
     apply(simp add: )
    apply(rename_tac d list ca w)(*strict*)
    apply(force)
   apply(rename_tac d list ca w)(*strict*)
   apply(force)
  apply(rename_tac d list ca w)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d list ca w e ci' l r)(*strict*)
  apply(case_tac ci')
  apply(rename_tac d list ca w e ci' l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d list ca w e l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac d list ca w e l r)(*strict*)
   prefer 2
   apply(rename_tac d list ca w e l r a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d list ca w e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d list ca w e)(*strict*)
  apply(case_tac list)
   apply(rename_tac d list ca w e)(*strict*)
   apply(force)
  apply(rename_tac d list ca w e a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca w e a lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ca w e a lista)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="Suc 0"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac d ca w e a lista)(*strict*)
     apply(simp add: )
    apply(rename_tac d ca w e a lista)(*strict*)
    apply(force)
   apply(rename_tac d ca w e a lista)(*strict*)
   apply(force)
  apply(rename_tac d ca w e a lista)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  done

definition derives :: "
    ('a,'b) cfg
      \<Rightarrow> ('a,'b)cfg_step_label list
      \<Rightarrow> ('a,'b)DT_two_elements list" where
  "derives G \<pi> \<equiv>
    cfg_conf(THE c.
      \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA (prod_lhs(hd \<pi>))]\<rparr> (realizable G \<pi>) c)"

lemma entire_realizable_derives_in_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=teA A#w\<rparr> \<pi> \<lparr>cfg_conf=wx\<rparr>
  \<Longrightarrow> realizable G \<pi> = \<pi>
  \<Longrightarrow> \<pi>\<noteq>[]
  \<Longrightarrow> \<exists>v. derives G \<pi> = v \<and> v@w=wx"
  apply(simp add: derives_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      in existence_of_realizable)
      apply(simp add: )
     apply(force)
    apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
     apply(simp add: cfg_step_labels_def)
    apply(rule cfgLM.trans_der_all_step_labels)
     apply(simp add: )
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac \<pi>' c da)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>' c da cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' da cfg_confa)(*strict*)
  apply(rename_tac wy)
  apply(rename_tac \<pi>' da wy)(*strict*)
  apply(subgoal_tac "prod_lhs (hd (\<pi>)) = A")
   apply(rename_tac \<pi>' da wy)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>' da wy)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac \<pi>' da wy)(*strict*)
      apply(simp add: )
     apply(rename_tac \<pi>' da wy)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da wy)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da wy)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi>' da wy e ci' l r)(*strict*)
   apply(case_tac ci')
   apply(rename_tac \<pi>' da wy e ci' l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' da wy e l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac \<pi>' da wy e l r)(*strict*)
    prefer 2
    apply(rename_tac \<pi>' da wy e l r a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>' da wy e l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>' da wy e)(*strict*)
   apply(case_tac "\<pi>")
    apply(rename_tac \<pi>' da wy e)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>' da wy e a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>' da wy)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>' da wy)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and da="da"
      and ca="\<lparr>cfg_conf=wy\<rparr>"
      in realizable_eq_from_existence)
         apply(rename_tac \<pi>' da wy)(*strict*)
         apply(simp add: )
        apply(rename_tac \<pi>' da wy)(*strict*)
        apply(force)
       apply(rename_tac \<pi>' da wy)(*strict*)
       apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
        apply(rename_tac \<pi>' da wy)(*strict*)
        apply(simp add: cfg_step_labels_def)
       apply(rename_tac \<pi>' da wy)(*strict*)
       apply(rule cfgLM.trans_der_all_step_labels)
        apply(rename_tac \<pi>' da wy)(*strict*)
        apply(simp add: )
       apply(rename_tac \<pi>' da wy)(*strict*)
       apply(force)
      apply(rename_tac \<pi>' da wy)(*strict*)
      apply(force)
     apply(rename_tac \<pi>' da wy)(*strict*)
     apply(force)
    apply(rename_tac \<pi>' da wy)(*strict*)
    apply(force)
   apply(rename_tac \<pi>' da wy)(*strict*)
   apply(force)
  apply(rename_tac \<pi>' da wy)(*strict*)
  apply(clarsimp)
  apply(rename_tac da wy)(*strict*)
  apply(rule_tac
      t="(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi> c)"
      and s="\<lparr>cfg_conf=wy\<rparr>"
      in ssubst)
   apply(rename_tac da wy)(*strict*)
   apply(rule the_equality)
    apply(rename_tac da wy)(*strict*)
    apply(force)
   apply(rename_tac da wy c)(*strict*)
   apply(clarsimp)
   apply(rename_tac da wy c daa)(*strict*)
   apply(case_tac c)
   apply(rename_tac da wy c daa cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac da wy daa cfg_conf)(*strict*)
   apply(rename_tac wy2)
   apply(rename_tac da wy daa wy2)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf=wy\<rparr>=\<lparr>cfg_conf=wy2\<rparr>")
    apply(rename_tac da wy daa wy2)(*strict*)
    apply(force)
   apply(rename_tac da wy daa wy2)(*strict*)
   apply(rule cfgLM_trans_der_unique_result)
     apply(rename_tac da wy daa wy2)(*strict*)
     apply(simp add: )
    apply(rename_tac da wy daa wy2)(*strict*)
    apply(force)
   apply(rename_tac da wy daa wy2)(*strict*)
   apply(force)
  apply(rename_tac da wy)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac da wy)(*strict*)
   prefer 2
   apply(rule_tac
      ?v1.0="wx"
      and ?w1.0="[teA (prod_lhs (hd (\<pi>)))]"
      and \<pi>="\<pi>"
      and ?w2.0="w"
      and ?d2.0="da"
      and ?d1.0="d"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac da wy)(*strict*)
     apply(force)
    apply(rename_tac da wy)(*strict*)
    apply(force)
   apply(rename_tac da wy)(*strict*)
   apply(force)
  apply(rename_tac da wy)(*strict*)
  apply(clarsimp)
  done

lemma derive_entire: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> c'
  \<Longrightarrow> d i = Some (pair e \<lparr>cfg_conf=[teA A]\<rparr>)
  \<Longrightarrow> i<length \<pi>
  \<Longrightarrow> derives G (drop i \<pi>) = cfg_conf c'"
  apply(simp add: derives_def)
  apply(rule_tac
      t="(THE c. \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop i \<pi>)))]\<rparr> (realizable G (drop i \<pi>)) c)"
      and s="c'"
      in ssubst)
   prefer 2
   apply(force)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop d i) \<lparr>cfg_conf=[teA A]\<rparr> (drop i \<pi>) c'")
   prefer 2
   apply(rule cfgLM.trans_der_skip)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac c')
  apply(rename_tac cfg_conf)(*strict*)
  apply(subgoal_tac "realizable G (drop i \<pi>)=SSX" for SSX)
   apply(rename_tac cfg_conf)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_drop d i"
      and ?\<pi>2.0="[]"
      in entire_realizable)
     apply(rename_tac cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac cfg_conf)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prod_lhs (hd (drop i \<pi>)) = A")
   apply(rename_tac cfg_conf)(*strict*)
   apply(rule_tac
      a="\<lparr>cfg_conf = cfg_conf\<rparr>"
      in theI2)
     apply(rename_tac cfg_conf)(*strict*)
     apply(rule_tac
      x="derivation_drop d i"
      in exI)
     apply(force)
    apply(rename_tac cfg_conf x)(*strict*)
    apply(clarsimp)
    apply(rename_tac cfg_conf x da)(*strict*)
    apply (metis cfgLM_trans_der_unique_result)
   apply(rename_tac cfg_conf x)(*strict*)
   apply(clarsimp)
   apply(rename_tac cfg_conf x da)(*strict*)
   apply (metis cfgLM_trans_der_unique_result)
  apply(rename_tac cfg_conf)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac cfg_conf)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="i"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac cfg_conf)(*strict*)
     apply(simp add: )
    apply(rename_tac cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac cfg_conf)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_confa ci' l r)(*strict*)
  apply(case_tac ci')
  apply(rename_tac cfg_confa ci' l r cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_conf l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac cfg_conf l r)(*strict*)
   prefer 2
   apply(rename_tac cfg_conf l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac cfg_conf l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_conf)(*strict*)
  apply(case_tac "drop i \<pi>")
   apply(rename_tac cfg_conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac cfg_conf a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="\<pi>!i"
      and s="a"
      in ssubst)
   apply(rename_tac cfg_conf a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac cfg_conf a list)(*strict*)
  apply (metis nth_via_drop)
  done

lemma entire_derives: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> \<pi> \<lparr>cfg_conf=w\<rparr>
  \<Longrightarrow> \<pi> \<noteq> []
  \<Longrightarrow> derives G \<pi> = w"
  apply(simp add: derives_def)
  apply(rule_tac
      t="realizable G \<pi>"
      and s="\<pi>"
      in ssubst)
   apply(rule_tac
      ?\<pi>2.0="[]"
      in entire_realizable)
     apply(blast)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length \<pi>"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(case_tac \<pi>)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e a list)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c1=\<lparr>cfg_conf = [teA A]\<rparr>")
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2)(*strict*)
  apply(case_tac \<pi>)
   apply(rename_tac e1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 c2 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "A=prod_lhs a")
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac e1 e2 c2 a list)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac e1 e2 c2 a list e)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length (a # list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e1 e2 c2 a list e)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c2 a list e)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c2 a list e)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2 a list l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac e1 e2 c2 a list l r)(*strict*)
    prefer 2
    apply(rename_tac e1 e2 c2 a list l r aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c2 a list l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   apply(subgoal_tac "e2=a")
    apply(rename_tac e1 e2 c2 a list)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
        apply(rename_tac e1 e2 c2 a list)(*strict*)
        apply(force)
       apply(rename_tac e1 e2 c2 a list)(*strict*)
       apply(force)
      apply(rename_tac e1 e2 c2 a list)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c2 a list)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c2 a list)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c2 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "e2 = a")
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   prefer 2
   apply(rule_tac
      n="0"
      and d="d"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac e1 e2 c2 a list)(*strict*)
       apply(force)
      apply(rename_tac e1 e2 c2 a list)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c2 a list)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c2 a list)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c2 a list)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 c2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c2 a list)(*strict*)
  apply(rule_tac
      a="\<lparr>cfg_conf = w\<rparr>"
      in theI2)
    apply(rename_tac e1 c2 a list)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c2 a list x da)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac e1 c2 a list x da)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac e1 c2 a list x da e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length(a#list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e1 c2 a list x da e ea)(*strict*)
      apply(force)
     apply(rename_tac e1 c2 a list x da e ea)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e ea)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac e1 c2 a list x da)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length(a#list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
      apply(force)
     apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
   apply(subgoal_tac "e2 = a")
    apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
    prefer 2
    apply(rule_tac
      n="0"
      and d="da"
      in cfgLM.trans_der_getLabel_at_pos)
        apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
        apply(force)
       apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
       apply(force)
      apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
      apply(force)
     apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c2 a list x da e1a c1 c2a)(*strict*)
   apply(case_tac x)
   apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
   apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
    apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d"
      and ?w2.0="[]"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
      apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
      apply(simp add: )
     apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 c2 a list x)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c2 a list x da)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. da 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac e1 c2 a list x da)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e1 c2 a list x da e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(a#list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e1 c2 a list x da e ea)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e ea)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e ea)(*strict*)
   apply(force)
  apply(rename_tac e1 c2 a list x da)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac e1 c2 a list x da)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(a#list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e ea e1a e2 c1 c2a)(*strict*)
   apply(force)
  apply(rename_tac e1 c2 a list x da)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
  apply(subgoal_tac "e2 = a")
   apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
   prefer 2
   apply(rule_tac
      n="0"
      and d="da"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
       apply(force)
      apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
      apply(force)
     apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
     apply(force)
    apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
   apply(force)
  apply(rename_tac e1 c2 a list x da e1a e2 c1 c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c2 a list x da e1a c1 c2a)(*strict*)
  apply(case_tac x)
  apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_confa)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_confa)(*strict*)
   prefer 2
   apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
   apply(rule_tac
      ?d1.0="d"
      and ?w2.0="[]"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
     apply(simp add: )
    apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac e1 c2 a list x da e1a c1 c2a cfg_confa)(*strict*)
  apply(clarsimp)
  done

lemma derives_single: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = r\<rparr> \<in> cfg_productions G
  \<Longrightarrow> derives G [\<lparr>prod_lhs = A, prod_rhs = r\<rparr>] = r"
  apply(simp add: derives_def)
  apply(rule_tac
      t="THE c. \<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA A]\<rparr> (realizable G [\<lparr>prod_lhs = A, prod_rhs = r\<rparr>]) c"
      and s="\<lparr>cfg_conf=r\<rparr>"
      in ssubst)
   prefer 2
   apply(force)
  apply(subgoal_tac "realizable G [\<lparr>prod_lhs = A, prod_rhs = r\<rparr>] = [\<lparr>prod_lhs = A, prod_rhs = r\<rparr>]")
   prefer 2
   apply(rule realizable_single)
    apply(force)
   apply(force)
  apply(rule the_equality)
   apply(clarsimp)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = r\<rparr> \<lparr>cfg_conf = r\<rparr>"
      in exI)
   apply(rule cfgLM.trans_der_der2)
     apply(force)
    apply(simp add: cfg_configurations_def valid_cfg_def)
    apply(force)
   apply(simp add: cfgLM_step_relation_def)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="True"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac c d)(*strict*)
     apply(simp add: )
    apply(rename_tac c d)(*strict*)
    apply(force)
   apply(rename_tac c d)(*strict*)
   apply(force)
  apply(rename_tac c d)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c d e l ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac c d e l ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e l ra)(*strict*)
  apply(case_tac l)
   apply(rename_tac d e l ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e l ra a list)(*strict*)
  apply(clarsimp)
  done

lemma derive_empty_if_first_prod_has_empty_rhs: "
  valid_cfg G
  \<Longrightarrow> set (p#\<pi>) \<subseteq> cfg_productions G
  \<Longrightarrow> p=\<lparr>prod_lhs=A,prod_rhs=[]\<rparr>
  \<Longrightarrow> derives G (p#\<pi>) = []"
  apply(clarsimp)
  apply(simp add: derives_def)
  apply(rule_tac
      t="realizable X Y" for X Y
      in ssubst)
   apply(rule realizable_single_if_first_prod_has_empty_rhs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="THE c. \<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA A]\<rparr> [\<lparr>prod_lhs = A, prod_rhs = []\<rparr>] c"
      and s="\<lparr>cfg_conf=[]\<rparr>"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule the_equality)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = []\<rparr> \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule cfgLM.trans_der_der2)
     apply(force)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="X" for X
      in ballE)
     prefer 2
     apply(force)
    apply(simp add: cfg_configurations_def)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac c d)(*strict*)
     apply(simp add: )
    apply(rename_tac c d)(*strict*)
    apply(force)
   apply(rename_tac c d)(*strict*)
   apply(force)
  apply(rename_tac c d)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c d e ci' l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac c d e ci' l r)(*strict*)
   prefer 2
   apply(rename_tac c d e ci' l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d e ci' l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d e ci')(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  done

definition applicable :: "('a,'b) cfg \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> ('a, 'b) DT_two_elements list \<Rightarrow> bool" where
  "applicable G \<pi> w = (\<exists>d c. cfgLM.trans_der G d \<lparr>cfg_conf = w\<rparr> \<pi> c)"

lemma applicable_contra2: "
  valid_cfg G
  \<Longrightarrow> \<not> applicable G \<pi>2 (w2@w3)
  \<Longrightarrow> applicable G (\<pi>1@\<pi>2) (w1@w3)
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w2\<rparr>
  \<Longrightarrow> Q"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac da c)(*strict*)
  apply(subgoal_tac "\<exists>e c. da (length \<pi>1) = Some (pair e c)")
   apply(rename_tac da c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac da c e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac da c e ea)(*strict*)
     apply(force)
    apply(rename_tac da c e ea)(*strict*)
    apply(force)
   apply(rename_tac da c e ea)(*strict*)
   apply(force)
  apply(rename_tac da c)(*strict*)
  apply(clarsimp)
  apply(rename_tac da c e ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac da c e ca cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac da c e ca w)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G da \<lparr>cfg_conf = w1@w3\<rparr> \<pi>1 \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac da c e ca w)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac da c e ca w)(*strict*)
       apply(simp add: )
      apply(rename_tac da c e ca w)(*strict*)
      apply(force)
     apply(rename_tac da c e ca w)(*strict*)
     apply(force)
    apply(rename_tac da c e ca w)(*strict*)
    apply(force)
   apply(rename_tac da c e ca w)(*strict*)
   apply(force)
  apply(rename_tac da c e ca w)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac da c e ca w)(*strict*)
   prefer 2
   apply(rule_tac
      ?w2.0="w3"
      and ?d1.0="da"
      and ?d2.0="d"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac da c e ca w)(*strict*)
     apply(simp add: )
    apply(rename_tac da c e ca w)(*strict*)
    apply(force)
   apply(rename_tac da c e ca w)(*strict*)
   apply(force)
  apply(rename_tac da c e ca w)(*strict*)
  apply(clarsimp)
  apply(rename_tac da c e)(*strict*)
  apply(erule_tac
      x="derivation_drop da (length \<pi>1)"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(subgoal_tac "cfgLM.trans_der G (derivation_drop da (length \<pi>1)) \<lparr>cfg_conf = w2 @ w3\<rparr> \<pi>2 c")
   apply(rename_tac da c e)(*strict*)
   apply(force)
  apply(rename_tac da c e)(*strict*)
  apply(thin_tac "\<not>cfgLM.trans_der G (derivation_drop da (length \<pi>1)) \<lparr>cfg_conf = w2 @ w3\<rparr> \<pi>2 c")
  apply(rename_tac da c e)(*strict*)
  apply(rule_tac
      t="\<pi>2"
      and s="drop(length \<pi>1)(\<pi>1@\<pi>2)"
      in ssubst)
   apply(rename_tac da c e)(*strict*)
   apply(force)
  apply(rename_tac da c e)(*strict*)
  apply(rule cfgLM.trans_der_skip)
     apply(rename_tac da c e)(*strict*)
     apply(force)
    apply(rename_tac da c e)(*strict*)
    apply(force)
   apply(rename_tac da c e)(*strict*)
   apply(force)
  apply(rename_tac da c e)(*strict*)
  apply(force)
  done

lemma unseen_nonterminal_tail_can_be_removed: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> \<pi> \<lparr>cfg_conf = w @ c\<rparr>
  \<Longrightarrow> applicable G \<pi> w1
  \<Longrightarrow> set w \<inter> set y = {}
  \<Longrightarrow> \<exists>d c. cfgLM.trans_der G d \<lparr>cfg_conf = w1\<rparr> \<pi> \<lparr>cfg_conf = w @ c\<rparr>"
  apply(subgoal_tac "\<forall>k<length \<pi>. \<exists>w1 A w2. cfg_conf (the(get_configuration(d k))) = liftB w1@teA A#w2 @ y")
   prefer 2
   apply(clarsimp)
   apply(rename_tac k)(*strict*)
   apply(simp add: applicable_def)
   apply(clarsimp)
   apply(rename_tac k da ca)(*strict*)
   apply(rule nonterminal_in_any_pre_configuration)
      apply(rename_tac k da ca)(*strict*)
      apply(force)
     apply(rename_tac k da ca)(*strict*)
     apply(force)
    apply(rename_tac k da ca)(*strict*)
    apply(force)
   apply(rename_tac k da ca)(*strict*)
   apply(force)
  apply(case_tac "\<pi>=[]")
   apply(clarsimp)
   apply(subgoal_tac "w1@y=w@c")
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "prefix w1 w \<or> SSX" for SSX)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(erule disjE)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac ca)(*strict*)
    apply(case_tac ca)
     apply(rename_tac ca)(*strict*)
     prefer 2
     apply(rename_tac ca a list)(*strict*)
     apply(force)
    apply(rename_tac ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = w1\<rparr>"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(rule cfgLM_trans_der_der1)
     apply(force)
    apply(subgoal_tac "\<lparr>cfg_conf = w1@c\<rparr> \<in> cfg_configurations G")
     apply(simp add: cfg_configurations_def)
     apply(simp add: setAConcat)
     apply(simp add: setBConcat)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule cfgLM.belongs_configurations)
     apply(force)
    apply(force)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w@c\<rparr>"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = w@c@y\<rparr> \<in> cfg_configurations G")
    apply(rename_tac c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp add: setAConcat)
    apply(simp add: setBConcat)
   apply(rename_tac c)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)
   apply(rename_tac e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      P="\<lambda>c. \<exists>w. cfg_conf c=w@y"
      and C="\<lambda>c. \<lparr>cfg_conf=butn (cfg_conf c) (length y)\<rparr>"
      and f="derivation_take d (length \<pi>)"
      in cfgLM.derivation_map_preserves_derivation23)
     apply(rename_tac e)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ca i ea)(*strict*)
    apply(simp add: derivation_take_def)
    apply(case_tac "i\<le>(length \<pi>)")
     apply(rename_tac e ca i ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e ca i ea)(*strict*)
    apply(clarsimp)
    apply(case_tac "i=length \<pi>")
     apply(rename_tac e ca i ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea)(*strict*)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length \<pi>-Suc 0) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
      apply(rename_tac ea)(*strict*)
      prefer 2
      apply(rule_tac
      m="length \<pi>"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac ea)(*strict*)
        apply(force)
       apply(rename_tac ea)(*strict*)
       apply(force)
      apply(rename_tac ea)(*strict*)
      apply(force)
     apply(rename_tac ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e1 e2 c1)(*strict*)
     apply(erule_tac
      x="length \<pi> - Suc 0"
      in allE)
     apply(clarsimp)
     apply(rename_tac e1 e2 c1 w1a A w2)(*strict*)
     apply(simp add: get_configuration_def)
     apply(case_tac c1)
     apply(rename_tac e1 e2 c1 w1a A w2 cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e1 e2 w1a A w2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
     apply(subgoal_tac "\<exists>l'. liftB l' = l")
      apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
      prefer 2
      apply(rule_tac
      x="filterB l"
      in exI)
      apply (rule liftBDeConv2)
      apply (metis setA_substring setA_substring_prime)
     apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
     apply(thin_tac "setA (liftB l') = {}")
     apply(subgoal_tac "w1a=l'")
      apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
      apply(clarsimp)
     apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
     apply (metis leading_liftB_prefix_eq)
    apply(rename_tac e ca i ea)(*strict*)
    apply(subgoal_tac "i<length \<pi>")
     apply(rename_tac e ca i ea)(*strict*)
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(rename_tac e ca i ea w1a A w2)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac e ca i ea)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e a ea b i e1 e2 wa waa)(*strict*)
   apply(simp add: butn_def)
   apply(case_tac a)
   apply(rename_tac e a ea b i e1 e2 wa waa cfg_confa)(*strict*)
   apply(case_tac b)
   apply(rename_tac e a ea b i e1 e2 wa waa cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea i e1 e2 wa waa)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e ea i e1 e2 wa waa l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac e ea i e1 e2 wa waa l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_substring setA_substring_prime)
   apply(rename_tac e ea i e1 e2 wa waa l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea i e1 e2 wa waa r l')(*strict*)
   apply(simp add: derivation_take_def)
   apply(case_tac "i\<le>(length \<pi>)")
    apply(rename_tac e ea i e1 e2 wa waa r l')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e ea i e1 e2 wa waa r l')(*strict*)
   apply(case_tac "Suc i\<le>(length \<pi>)")
    apply(rename_tac e ea i e1 e2 wa waa r l')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e ea i e1 e2 wa waa r l')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac e ea i e1 e2 wa waa r l' w1a A w2)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac e ea i e1 e2 wa r l' w1a A w2)(*strict*)
   apply(subgoal_tac "l'=w1a")
    apply(rename_tac e ea i e1 e2 wa r l' w1a A w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea i e1 e2 w1a w2)(*strict*)
    apply(force)
   apply(rename_tac e ea i e1 e2 wa r l' w1a A w2)(*strict*)
   apply (metis leading_liftB_prefix_eq)
  apply(rule_tac
      x="derivation_map (derivation_take d (length \<pi>)) (\<lambda>c. \<lparr>cfg_conf = butn (cfg_conf c) (length y)\<rparr>)"
      in exI)
  apply(rule_tac
      x="butn c (length y)"
      in exI)
  apply(simp (no_asm) add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule cfgLM.derivation_belongs)
      apply(force)
     apply(simp add: derivation_map_def derivation_take_def)
    apply(simp add: butn_def)
    apply(subgoal_tac "\<lparr>cfg_conf = w1@y\<rparr> \<in> cfg_configurations G")
     apply(simp add: cfg_configurations_def)
     apply(simp add: setAConcat)
     apply(simp add: setBConcat)
    apply(rule cfgLM.belongs_configurations)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule_tac
      t="get_labels (derivation_map (derivation_take d (length \<pi>)) (\<lambda>c. \<lparr>cfg_conf = butn (cfg_conf c) (length y)\<rparr>)) (length \<pi>)"
      in ssubst)
    apply(rule get_labels_derivation_map)
   apply(rule_tac
      t="get_labels (derivation_take d (length \<pi>)) (length \<pi>)"
      in subst)
    apply(rule cfgLM.get_labels_derivation_take)
      apply(force)
     apply(simp add: cfgLM.trans_der_def)
    apply(simp add: cfgLM.trans_der_def)
    apply(force)
   apply(simp add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(simp add: derivation_map_def derivation_take_def)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: butn_def)
  apply(simp add: derivation_map_def derivation_take_def)
  apply(simp add: butn_def)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length \<pi>-Suc 0) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule_tac
      m="length \<pi>"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1)(*strict*)
  apply(erule_tac
      x="length \<pi> - Suc 0"
      in allE)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1 w1a A w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c1)
  apply(rename_tac e1 e2 c1 w1a A w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 w1a A w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac e1 e2 w1a A w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "w1a=l'")
   apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
   prefer 2
   apply (rule leading_liftB_prefix_eq)
   apply(force)
  apply(rename_tac e1 e2 w1a A w2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 w2 l')(*strict*)
  apply(simp add: butn_def)
  apply(rule_tac
      v="y"
      in append_injr)
  apply(rule_tac
      t="(liftB l' @ prod_rhs e2 @ w2) @ y"
      and s="w@c"
      in ssubst)
   apply(rename_tac e1 e2 w2 l')(*strict*)
   apply(force)
  apply(rename_tac e1 e2 w2 l')(*strict*)
  apply(simp (no_asm))
  apply(subgoal_tac "prefix w (liftB l' @ prod_rhs e2 @ w2) \<or> SSX" for SSX)
   apply(rename_tac e1 e2 w2 l')(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac e1 e2 w2 l')(*strict*)
  apply(erule disjE)
   apply(rename_tac e1 e2 w2 l')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 w2 l' ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac e1 e2 w2 l' ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 w2 l' ca a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 w2 l' a list)(*strict*)
   apply(subgoal_tac "c=a#list@y")
    apply(rename_tac e1 e2 w2 l' a list)(*strict*)
    prefer 2
    apply (metis Cons_eq_appendI append_assoc append_eq_appendI append_injective2)
   apply(rename_tac e1 e2 w2 l' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 w2 l')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e1 e2 w2 l' ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac e1 e2 w2 l' ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 w2 l' ca a list)(*strict*)
  apply(clarsimp)
  done

lemma applicable_with_empty_source: "
  applicable G \<pi> []
  \<Longrightarrow> \<pi>=[]"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
   apply(rename_tac d c)(*strict*)
   prefer 2
   apply(rule_tac cfgLM_trans_der_from_empty)
   apply(force)
  apply(rename_tac d c)(*strict*)
  apply(force)
  done

lemma applicable_drop_prods: "
  valid_cfg G
  \<Longrightarrow> applicable G (\<pi>1@\<pi>2) w
  \<Longrightarrow> applicable G \<pi>1 w"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (length \<pi>1) = Some (pair e c)")
   apply(rename_tac d c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d c e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac d c e)(*strict*)
     apply(force)
    apply(rename_tac d c e)(*strict*)
    apply(force)
   apply(rename_tac d c e)(*strict*)
   apply(force)
  apply(rename_tac d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c e ca)(*strict*)
  apply(case_tac "\<pi>2=[]")
   apply(rename_tac d c e ca)(*strict*)
   apply(force)
  apply(rename_tac d c e ca)(*strict*)
  apply(rule_tac
      x="derivation_take d (length \<pi>1)"
      in exI)
  apply(rule_tac
      x="ca"
      in exI)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d c e ca)(*strict*)
   prefer 2
   apply(rule cfgLM_trans_der_crop)
      apply(rename_tac d c e ca)(*strict*)
      apply(force)
     apply(rename_tac d c e ca)(*strict*)
     apply(force)
    apply(rename_tac d c e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d c e ca)(*strict*)
   apply(force)
  apply(rename_tac d c e ca)(*strict*)
  apply(force)
  done

lemma applicable_drop_liftB: "
  valid_cfg G
  \<Longrightarrow> applicable G \<pi> (liftB w @ v)
  \<Longrightarrow> applicable G \<pi> v"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac d c)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d c e)(*strict*)
   apply(rule_tac
      d="d"
      and i="0"
      and j="length \<pi>"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac d c e)(*strict*)
        apply(simp add: )
       apply(rename_tac d c e)(*strict*)
       apply(force)
      apply(rename_tac d c e)(*strict*)
      apply(force)
     apply(rename_tac d c e)(*strict*)
     apply(force)
    apply(rename_tac d c e)(*strict*)
    apply(force)
   apply(rename_tac d c e)(*strict*)
   apply(force)
  apply(rename_tac d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c wa)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(case_tac c)
  apply(rename_tac d c wa cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d wa cfg_conf)(*strict*)
  apply(rename_tac x)
  apply(rename_tac d wa x)(*strict*)
  apply(subgoal_tac "maxTermPrefix (liftB w @ v) = w@maxTermPrefix v")
   apply(rename_tac d wa x)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_shift)
  apply(rename_tac d wa x)(*strict*)
  apply(subgoal_tac "prefix (liftB w) x")
   apply(rename_tac d wa x)(*strict*)
   prefer 2
   apply (metis concat_asso prefix_of_maxTermPrefix_is_terminal_string_prefix)
  apply(rename_tac d wa x)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d wa c)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> SSrenPI \<lparr>cfg_conf = SSw2\<rparr>" for SSG SSw1 SSrenPI SSw2)
   apply(rename_tac d wa c)(*strict*)
   prefer 2
   apply(rule cfgLM_trans_der_drop_leading_terminals_prime)
    apply(rename_tac d wa c)(*strict*)
    apply(force)
   apply(rename_tac d wa c)(*strict*)
   apply(force)
  apply(rename_tac d wa c)(*strict*)
  apply(force)
  done

lemma applicable_contra: "
  valid_cfg G
  \<Longrightarrow> \<not> applicable G \<pi>1 (w1 @ w2)
  \<Longrightarrow> \<lparr>cfg_conf = liftB \<alpha>@w2\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> applicable G (\<pi>1 @ \<pi>2) (liftB \<alpha> @ w1)
  \<Longrightarrow> Q"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (length \<pi>1) = Some (pair e c)")
   apply(rename_tac d c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d c e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac d c e)(*strict*)
     apply(force)
    apply(rename_tac d c e)(*strict*)
    apply(force)
   apply(rename_tac d c e)(*strict*)
   apply(force)
  apply(rename_tac d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c e ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d c e ca cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d c e ca w)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<alpha>@w1\<rparr> \<pi>1 \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac d c e ca w)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac d c e ca w)(*strict*)
       apply(simp add: )
      apply(rename_tac d c e ca w)(*strict*)
      apply(force)
     apply(rename_tac d c e ca w)(*strict*)
     apply(force)
    apply(rename_tac d c e ca w)(*strict*)
    apply(force)
   apply(rename_tac d c e ca w)(*strict*)
   apply(force)
  apply(rename_tac d c e ca w)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<alpha>@w1\<rparr> (\<pi>1 @ \<pi>2) c")
  apply(rename_tac d c e ca w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w)(*strict*)
  apply(thin_tac "d (length \<pi>1) = Some (pair e \<lparr>cfg_conf = w\<rparr>)")
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac d e w)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="[]"
      and ?w2.0="w2"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac d e w)(*strict*)
     apply(force)
    apply(rename_tac d e w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d e w)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(rename_tac d w)(*strict*)
   apply(simp add: setAConcat)
   apply(simp add: setBConcat)
  apply(rename_tac d e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = liftB \<alpha> @ w1\<rparr> \<pi>1 \<lparr>cfg_conf = w\<rparr>")
  apply(rename_tac d w da)(*strict*)
  apply(thin_tac "\<lparr>cfg_conf = liftB \<alpha> @ w2\<rparr> \<in> cfg_configurations G")
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac d w da)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d w da e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      d="da"
      and i="0"
      and j="length \<pi>1"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac d w da e)(*strict*)
        apply(simp add: )
       apply(rename_tac d w da e)(*strict*)
       apply(force)
      apply(rename_tac d w da e)(*strict*)
      apply(force)
     apply(rename_tac d w da e)(*strict*)
     apply(force)
    apply(rename_tac d w da e)(*strict*)
    apply(force)
   apply(rename_tac d w da e)(*strict*)
   apply(force)
  apply(rename_tac d w da)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(rename_tac w da)(*strict*)
  apply(clarsimp)
  apply(rename_tac w da wa)(*strict*)
  apply(subgoal_tac "maxTermPrefix (liftB \<alpha> @ w1 @ w2) = \<alpha>@maxTermPrefix (w1 @ w2)")
   apply(rename_tac w da wa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac w da wa)(*strict*)
    prefer 2
    apply(rule prefix_of_maxTermPrefix_is_terminal_string_prefix)
    apply(force)
   apply(rename_tac w da wa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac w da wa c)(*strict*)
   apply(subgoal_tac "\<exists>da. cfgLM.trans_der G da \<lparr>cfg_conf = w1 @ w2\<rparr> \<pi>1 \<lparr>cfg_conf = c\<rparr>")
    apply(rename_tac w da wa c)(*strict*)
    apply(force)
   apply(rename_tac w da wa c)(*strict*)
   apply(rule_tac
      \<alpha>="\<alpha>"
      in cfgLM_trans_der_drop_leading_terminals_prime)
    apply(rename_tac w da wa c)(*strict*)
    apply(force)
   apply(rename_tac w da wa c)(*strict*)
   apply(force)
  apply(rename_tac w da wa)(*strict*)
  apply (metis maxTermPrefix_shift)
  done

lemma applicable_liftB: "
  valid_cfg G
  \<Longrightarrow> applicable G \<pi> (liftB w)
  \<Longrightarrow> \<pi>\<noteq>[]
  \<Longrightarrow> Q"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(case_tac \<pi>)
   apply(rename_tac d c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d c a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d c a list e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (a # list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d c a list e)(*strict*)
     apply(force)
    apply(rename_tac d c a list e)(*strict*)
    apply(force)
   apply(rename_tac d c a list e)(*strict*)
   apply(force)
  apply(rename_tac d c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c a list e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d c a list e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d c a list e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d c a list e1 e2 c1 c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c a list e1 e2 l r)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d c a list e2 l r e)(*strict*)
  apply (metis liftB_with_nonterminal_inside)
  done

lemma applicable_append_liftB: "
  valid_cfg G
  \<Longrightarrow> applicable G \<pi> v
  \<Longrightarrow> set w \<subseteq> cfg_events G
  \<Longrightarrow> applicable G \<pi> (liftB w @ v)"
  apply(simp add: applicable_def)
  apply(clarsimp)
  apply(rename_tac d c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac d cfg_conf)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and v="w"
      and ?w2.0="[]"
      and ?d1.0="d"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac d cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac d cfg_conf)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(rule conjI)
     apply(rename_tac d cfg_conf)(*strict*)
     apply (simp add: setA_liftB)
    apply(rename_tac d cfg_conf)(*strict*)
    apply (simp add: setB_liftB)
   apply(rename_tac d cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac d cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d cfg_conf da)(*strict*)
  apply(force)
  done

definition cfgLM_accessible_nonterminals_ALT2 :: "('a,'b) cfg \<Rightarrow> 'a set" where
  "cfgLM_accessible_nonterminals_ALT2 G = {A. \<exists>d \<pi> w1 w2.
  cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf=liftB w1@teA A#w2\<rparr>}"

lemma cfgLM_accessible_nonterminals_ALT2_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> A \<in> cfgLM_accessible_nonterminals_ALT2 G
  \<Longrightarrow> A \<in> cfgLM_accessible_nonterminals G"
  apply(simp add: cfgLM_accessible_nonterminals_def cfgLM_accessible_nonterminals_ALT2_def)
  apply(clarsimp)
  apply(rename_tac d \<pi> w1 w2)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d \<pi> w1 w2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w1 w2 e)(*strict*)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac d \<pi> w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w1 w2)(*strict*)
  apply(simp add: cfg_configurations_def setAConcat setA_liftB setB_liftB)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d \<pi> w1 w2 e)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<pi> w1 w2 e)(*strict*)
   apply(rule cfgLM.derivation_initialI)
    apply(rename_tac d \<pi> w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w1 w2 e)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d \<pi> w1 w2 e)(*strict*)
  apply(rule_tac
      x="length \<pi>"
      in exI)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(force)
  done

lemma cfgLM_accessible_nonterminals_cfgLM_accessible_nonterminals_ALT2: "
  valid_cfg G
  \<Longrightarrow> A \<in> cfgLM_accessible_nonterminals G
  \<Longrightarrow> A \<in> cfgLM_accessible_nonterminals_ALT2 G"
  apply(simp add: cfgLM_accessible_nonterminals_def cfgLM_accessible_nonterminals_ALT2_def)
  apply(clarsimp)
  apply(rename_tac d n c w1 w2)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="map the (get_labels d n)"
      in exI)
  apply(case_tac "d n")
   apply(rename_tac d n c w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d n c w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c w1 w2 option b)(*strict*)
  apply(case_tac c)
  apply(rename_tac d n c w1 w2 option b cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n w1 w2 option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule_tac
      x="w2"
      in exI)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(rule cfgLM.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(rule cfgLM.derivation_initial_belongs)
    apply(rename_tac d n w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule_tac
      t="length (get_labels d n)"
      and s="n"
      in ssubst)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d n w1 w2 option)(*strict*)
    apply(rule cfgLM.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n w1 w2 option a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n w1 w2 option a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n w1 w2 option b)(*strict*)
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  done

definition cfgSTD_Nonblockingness_nonterminals_ALT3 :: "('a,'b) cfg \<Rightarrow> 'a set" where
  "cfgSTD_Nonblockingness_nonterminals_ALT3 G = {A. \<exists>d \<pi> w.
  cfgLM.trans_der G d \<lparr>cfg_conf=[teA A]\<rparr> \<pi> \<lparr>cfg_conf=liftB w\<rparr>}"

end
