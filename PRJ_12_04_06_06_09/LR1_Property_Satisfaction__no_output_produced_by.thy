section {*LR1\_Property\_Satisfaction\_\_no\_output\_produced\_by*}
theory
  LR1_Property_Satisfaction__no_output_produced_by

imports
  PRJ_12_04_06_06_09__ENTRY

begin

definition lastProduces :: "
  (nat
  \<Rightarrow> ((('b, 'c) DT_l2_l3_nonterminals, 'd) cfg_step_label, (('b, 'c) DT_l2_l3_nonterminals, 'd) cfg_configuration) derivation_configuration option)
  \<Rightarrow> (('b, 'c) DT_l2_l3_nonterminals, 'd) cfg_step_label list
  \<Rightarrow> bool"
  where
    "lastProduces d \<pi> \<equiv>
  \<forall>i < length \<pi>.
    case hd (cfg_conf (the (get_configuration (d i)))) of
      teA A \<Rightarrow> True
      | teB b \<Rightarrow> False"

lemma state_stack_compatible_nonterminals_generate_terminal_with_unique_length: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=e#liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=e#liftA t2\<rparr>
  \<Longrightarrow> lastProduces d1 \<pi>1
  \<Longrightarrow> lastProduces d2 \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> length \<pi>1 < length \<pi>2
  \<Longrightarrow> e = teB b
  \<Longrightarrow> Q"
  apply(clarsimp)
  apply(subgoal_tac "\<pi>1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rename_tac \<pi>1 p1)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(subgoal_tac "\<pi>2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 p1)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 w' a')(*strict*)
  apply(rename_tac \<pi>2 p2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@[p1])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = teB b # liftA t1\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2=p1")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A1]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p1]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
   apply(case_tac list)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba)(*strict*)
    apply(case_tac t1)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>1"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r)(*strict*)
  apply(case_tac p1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C1 r1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
  apply(case_tac r1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1)(*strict*)
   apply(case_tac w1)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1)(*strict*)
    apply(case_tac w2)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
  apply(case_tac w1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
  apply(thin_tac "liftA (l1 @ l2) = liftA l1 @ liftA l2")
  apply(subgoal_tac "lista=l2")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = C1, prod_rhs = teB b # liftA l1\<rparr>"
      in ballE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B)(*strict*)
  apply(case_tac l1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
  apply(case_tac list)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (length(\<pi>1)) = Some (pair e c)")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> (take(length \<pi>1)\<pi>2) c")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="(take(length \<pi>1)\<pi>2)"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>2) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = teB b # liftA t2\<rparr>")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
  apply(subgoal_tac "e2=p2")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a c1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p2]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a l r)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r list)(*strict*)
   apply(case_tac list)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r list)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r a lista aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r a lista ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r lista ba)(*strict*)
    apply(case_tac t2)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r lista ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r lista ba a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>2"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r)(*strict*)
  apply(case_tac p2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C2 r2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2)(*strict*)
  apply(case_tac r2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a C2)(*strict*)
   apply(case_tac w1a)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a C2)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a C2)(*strict*)
    apply(case_tac w2a)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a C2)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a C2 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a C2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2 a list)(*strict*)
  apply(case_tac w1a)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2 a list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w1a w2a r C2 r2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a r C2 list)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a r C2 list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a w2a r C2 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list lista)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 lista l1 l2a)(*strict*)
  apply(thin_tac "liftA (l1 @ l2a) = liftA l1 @ liftA l2a")
  apply(subgoal_tac "lista=l2a")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 lista l1 l2a)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 lista l1 l2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = C2, prod_rhs = teB b # liftA l1\<rparr>"
      in ballE)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a Ba)(*strict*)
  apply(case_tac l1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a Ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l1 l2a Ba a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba list)(*strict*)
  apply(case_tac list)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba)(*strict*)
  apply(case_tac w1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="d2"
      and i="length \<pi>1"
      and j="length (\<pi>2) - length \<pi>1"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (teB a # liftB list @ liftA w2) = a#maxTermPrefix (liftB list @ liftA w2)")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
    prefer 2
    apply (metis maxTermPrefix_pull_out)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "a # maxTermPrefix (liftB list @ liftA w2) @ w = []")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
   apply(rule_tac
      t="a # maxTermPrefix (liftB list @ liftA w2) @ w"
      and s="maxTermPrefix (teA C2 # liftA l2a)"
      in ssubst)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba a list w)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 e1a C2 l2a Ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba e2 c2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 e1a C2 l2a Ba e2 c2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 c2 a list)(*strict*)
  apply(case_tac c2)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 c2 a list cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="take(Suc(length \<pi>1))\<pi>2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(subgoal_tac "min (length \<pi>2) (Suc (length \<pi>1)) = Suc (length \<pi>1)")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w ea)(*strict*)
   apply(subgoal_tac "min (length \<pi>2) (length \<pi>1) = length \<pi>1")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w ea)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e1a C2 l2a Ba e2 a list w ea)(*strict*)
   apply(rule_tac
      m="(length \<pi>2)-((length \<pi>1))"
      and v="map Some (drop (Suc (length \<pi>1)) (\<pi>2 @ [\<lparr>prod_lhs = C2, prod_rhs = [teB b, teA Ba]\<rparr>]))"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e1a C2 l2a Ba e2 a list w ea)(*strict*)
    apply(clarsimp)
    apply (metis List.map_append append_take_drop_id)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e1a C2 l2a Ba e2 a list w ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w1 w2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w1 w2 l r)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w1 w2 l r aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 a list w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 list w1 w2)(*strict*)
  apply(case_tac e2)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2 l2a Ba e2 list w1 w2 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C2 r2)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba e2 list w1 w2 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w1 w2 C2 r2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w1 w2 C2 r2)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w1 w2 C2 r2 a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2 a lista)(*strict*)
   apply(case_tac r2)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2 a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista aa listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2 a lista aa listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="d2"
      and i="Suc(length \<pi>1)"
      and j="length (\<pi>2) - Suc(length \<pi>1)"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ea eb ec)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ec)(*strict*)
    apply(case_tac "length \<pi>2")
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb ec nat)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (teB a # listb @ liftA list) = a#maxTermPrefix (listb @ liftA list) ")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
    prefer 2
    apply (metis maxTermPrefix_pull_out)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "a # maxTermPrefix (listb @ liftA list) @ w = []")
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
   apply(rule_tac
      t="a # maxTermPrefix (listb @ liftA list) @ w"
      and s="maxTermPrefix (teA C2a # liftA l2a)"
      in ssubst)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 a lista listb w)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w1 w2 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list w2 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list C2 l1 l2b)(*strict*)
  apply(thin_tac "liftA (l1 @ l2b) = liftA l1 @ liftA l2b")
  apply(subgoal_tac "list=l2b")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list C2 l1 l2b)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba list C2 l1 l2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b)(*strict*)
  apply(case_tac "l1@l2b")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (Suc(length \<pi>1)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length (\<pi>2@[p])"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b a list)(*strict*)
  apply(rename_tac C w)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w)(*strict*)
  apply(case_tac A1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q ba)(*strict*)
   apply(clarsimp)
   apply(case_tac A2)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q ba qa baa)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_single_def)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      ?v2.0="[]"
      and ?B2.0="C"
      and ?r2.0="w"
      and ?v1.0="[b]"
      and ?B1.0="B"
      and ?r1.0="l2a"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G'"
      and G'="G"
      in cfgLM_positions_remain_compatible_prime)
                    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
                    apply(simp add: F2LR1inputx_def)
                   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
                   apply(simp add: F2LR1inputx_def)
                  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
                  apply(simp add: F2LR1inputx_def)
                 apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
                apply(simp add: F2LR1inputx_def)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
               apply(force)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
              apply(force)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
             apply(force)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
            apply(force)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
      apply(clarsimp)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ec)(*strict*)
      apply(rule_tac
      t="liftA l1 @ liftA l2b"
      and s="liftA (l1@l2b)"
      in ssubst)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ec)(*strict*)
       apply(simp (no_asm) add: liftA_commutes_over_concat)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ec)(*strict*)
      apply(rule_tac
      t="l1@l2b"
      and s="C#w"
      in ssubst)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ec)(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w qa ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q ba q1 baa q2)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?v2.0="[]"
      and ?w2.0="l1@l2b"
      and ?v1.0="[b]"
      and ?w1.0="B#l2a"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
       apply(clarsimp)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
      apply(clarsimp)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
      apply(rule conjI)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
      apply(rule_tac
      t="liftA l1 @ liftA l2b"
      and s="liftA (l1@l2b)"
      in ssubst)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
       apply(simp (no_asm) add: liftA_commutes_over_concat)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
      apply(rule_tac
      t="l1@l2b"
      and s="C#w"
      in ssubst)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ec)(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2)(*strict*)
  apply(case_tac A2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[b]"
      and ?x2.0="[]"
      and ?v1.0="[]"
      and ?w1.0="l1@l2b"
      and ?v2.0="[b]"
      and ?w2.0="B#l2a"
      and n="Suc(length \<pi>1)"
      and ?d2.0="d1"
      and ?d1.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
          apply(simp add: F2LR1inputx_def)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
         apply(simp add: F2LR1inputx_def)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
     apply(rule conjI)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
     apply(rule_tac
    t="liftA l1 @ liftA l2b"
    and s="liftA (l1@l2b)"
    in ssubst)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
     apply(rule_tac
    t="l1@l2b"
    and s="C#w"
    in ssubst)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q2 q ba ec)(*strict*)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa ea eb ec)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q baa)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_single_def)
  apply(subgoal_tac "X" for X)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a)(*strict*)
  prefer 2
  apply(unfold cfgLM.trans_der_def)
  apply(erule exE)+
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
  apply(fold cfgLM.trans_der_def)
  apply(rule_tac
    ?x1.0="[]"
    and ?x2.0="[b]"
    and ?v2.0="[]"
    and ?w2.0="l1@l2b"
    and ?v1.0="[b]"
    and ?w1.0="B#l2"
    and n="Suc(length \<pi>1)"
    and ?d1.0="d1"
    and ?d2.0="d2"
    in cfgLM_positions_remain_compatible_prime_prime)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
               apply(simp add: F2LR1inputx_def)
               apply(force)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
              apply(simp add: F2LR1inputx_def)
              apply(force)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
          apply(simp add: split_TSstructure_def)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
  apply(rule conjI)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
  apply(rule_tac
    t="liftA l1 @ liftA l2b"
    and s="liftA (l1@l2b)"
    in ssubst)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
   apply(simp (no_asm) add: liftA_commutes_over_concat)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
  apply(rule_tac
    t="l1@l2b"
    and s="C#w"
    in ssubst)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q2 q1a ba q2a ec)(*strict*)
  apply(simp (no_asm) add: liftA_commutes_over_concat)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e e1a C2a l2a Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e e1a C2a l2aa Ba C2 l1 l2b C w q1 ba q2 q1a baa q2a)(*strict*)
  apply(force)
  done

lemma state_stack_compatible_nonterminals_generate_nonterminal_with_unique_length: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf = e # liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf = e # liftA t2\<rparr>
  \<Longrightarrow> case e of teA A \<Rightarrow> left_degen G d1 \<and> left_degen G d2 | teB b \<Rightarrow> lastProduces d1 \<pi>1 \<and> lastProduces d2 \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> length \<pi>1 < length \<pi>2
  \<Longrightarrow> e = teA B1
  \<Longrightarrow> Q"
  apply(subgoal_tac "\<exists>e c. d2 (length(\<pi>1)) = Some (pair e c)")
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac ea eaa)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac ea eaa)(*strict*)
     apply(force)
    apply(rename_tac ea eaa)(*strict*)
    apply(force)
   apply(rename_tac ea eaa)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e c ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      d="d2"
      and n="0"
      and m="length \<pi>1"
      in left_degen_preserves_leading_nonterminal_prime)
        apply(rename_tac e c ea eb)(*strict*)
        apply(force)
       apply(rename_tac e c ea eb)(*strict*)
       apply(force)
      apply(rename_tac e c ea eb)(*strict*)
      apply(force)
     apply(rename_tac e c ea eb)(*strict*)
     apply(force)
    apply(rename_tac e c ea eb)(*strict*)
    apply(force)
   apply(rename_tac e c ea eb)(*strict*)
   apply(force)
  apply(rename_tac e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A w)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> (take(length \<pi>1)\<pi>2) \<lparr>cfg_conf = teA A # w\<rparr>")
   apply(rename_tac e A w)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac e A w)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac e A w)(*strict*)
      apply(force)
     apply(rename_tac e A w)(*strict*)
     apply(force)
    apply(rename_tac e A w)(*strict*)
    apply(force)
   apply(rename_tac e A w)(*strict*)
   apply(force)
  apply(rename_tac e A w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac e A w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac e A w)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="take(length \<pi>1)\<pi>2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = teA A # w\<rparr>"
      in allE)
  apply(erule impE)
   apply(rename_tac e A w)(*strict*)
   apply(force)
  apply(rename_tac e A w)(*strict*)
  apply(erule impE)
   apply(rename_tac e A w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac e A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A w w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac e A w w1 w2)(*strict*)
   prefer 2
   apply(rename_tac e A w w1 w2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e A w w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e A w w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac e A w w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac e A w w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e a list)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e a w)(*strict*)
  apply(rename_tac e B2 w)
  apply(rename_tac e B2 w)(*strict*)
  apply(subgoal_tac "cropTol3l2_single B1 = cropTol3l2_single B2")
   apply(rename_tac e B2 w)(*strict*)
   prefer 2
   apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf = teA B1 # liftA t2\<rparr>")
   apply(rename_tac e B2 w)(*strict*)
   apply(thin_tac "d2 (length \<pi>1) = Some (pair e \<lparr>cfg_conf = teA B2 # liftA w\<rparr>)")
   apply(rule left_degen_derivation_preserve_equivalent_state_stack_top)
          apply(rename_tac e B2 w)(*strict*)
          apply(force)
         apply(rename_tac e B2 w)(*strict*)
         apply(force)
        apply(rename_tac e B2 w)(*strict*)
        apply(force)
       apply(rename_tac e B2 w)(*strict*)
       apply(force)
      apply(rename_tac e B2 w)(*strict*)
      apply(force)
     apply(rename_tac e B2 w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e B2 w)(*strict*)
    apply(force)
   apply(rename_tac e B2 w)(*strict*)
   apply(force)
  apply(rename_tac e B2 w)(*strict*)
  apply(subgoal_tac "\<exists>\<pi> d. cfgLM.trans_der G d \<lparr>cfg_conf = teA B2 # liftA w\<rparr> \<pi> \<lparr>cfg_conf = teA B1 # liftA t2\<rparr> \<and> left_degen G d \<and> \<pi>\<noteq>[]")
   apply(rename_tac e B2 w)(*strict*)
   prefer 2
   apply(rule_tac
      x="drop(length \<pi>1)\<pi>2"
      in exI)
   apply(rule_tac
      x="derivation_drop d2 (length \<pi>1)"
      in exI)
   apply(rule conjI)
    apply(rename_tac e B2 w)(*strict*)
    apply(rule cfgLM.trans_der_skip)
       apply(rename_tac e B2 w)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac e B2 w)(*strict*)
      apply(force)
     apply(rename_tac e B2 w)(*strict*)
     apply(force)
    apply(rename_tac e B2 w)(*strict*)
    apply(force)
   apply(rename_tac e B2 w)(*strict*)
   apply(rule conjI)
    apply(rename_tac e B2 w)(*strict*)
    apply(rule derivation_drop_preserves_left_degen)
     apply(rename_tac e B2 w)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac e B2 w)(*strict*)
    apply(force)
   apply(rename_tac e B2 w)(*strict*)
   apply(force)
  apply(rename_tac e B2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e B2 w \<pi> d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e B2 w \<pi> d)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in left_degen_context_persists)
     apply(rename_tac e B2 w \<pi> d)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac e B2 w \<pi> d)(*strict*)
    apply(force)
   apply(rename_tac e B2 w \<pi> d)(*strict*)
   apply(force)
  apply(rename_tac e B2 w \<pi> d)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac e B2 w \<pi> d c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e B2 w \<pi> d c)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac e B2 w \<pi> d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e B2 w \<pi> d l1 l2)(*strict*)
  apply(thin_tac "liftA (l1 @ l2) = liftA l1 @ liftA l2")
  apply(subgoal_tac "w=l2")
   apply(rename_tac e B2 w \<pi> d l1 l2)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac e B2 w \<pi> d l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in left_degen_drop_context)
     apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
    apply(force)
   apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
   apply(force)
  apply(rename_tac e B2 \<pi> d l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = teA B2 # liftA l2\<rparr> \<pi> \<lparr>cfg_conf = teA B1 # liftA l1 @ liftA l2\<rparr>")
  apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
  apply(thin_tac "left_degen G d")
  apply(subgoal_tac "\<pi>=[]")
   apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
   apply(force)
  apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
  apply(rule_tac
      d="da"
      in no_repeating_leading_nonterminal_Extended)
      apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
      apply(force)
     apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
     apply(force)
    apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
    apply(force)
   apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
   apply(force)
  apply(rename_tac e B2 \<pi> d l1 l2 da)(*strict*)
  apply(force)
  done

lemma no_shorter_production_of_terminal_or_nonterminal: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=e#liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=e#liftA t2\<rparr>
  \<Longrightarrow> case e of teA A \<Rightarrow> left_degen G d1 \<and> left_degen G d2 | teB b \<Rightarrow> lastProduces d1 \<pi>1 \<and> lastProduces d2 \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> length \<pi>1 < length \<pi>2
  \<Longrightarrow> Q"
  apply(case_tac e)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rename_tac b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      ?\<pi>1.0="\<pi>1"
      and ?\<pi>2.0="\<pi>2"
      in state_stack_compatible_nonterminals_generate_terminal_with_unique_length)
           apply(rename_tac b)(*strict*)
           apply(force)
          apply(rename_tac b)(*strict*)
          apply(force)
         apply(rename_tac b)(*strict*)
         apply(force)
        apply(rename_tac b)(*strict*)
        apply(force)
       apply(rename_tac b)(*strict*)
       apply(force)
      apply(rename_tac b)(*strict*)
      apply(force)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(rename_tac b)(*strict*)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule_tac
      ?\<pi>1.0="\<pi>1"
      and ?\<pi>2.0="\<pi>2"
      in state_stack_compatible_nonterminals_generate_nonterminal_with_unique_length)
         apply(rename_tac a)(*strict*)
         apply(force)+
  done

lemma lastProduces_intro: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c \<pi> \<lparr>cfg_conf = option_to_list (Some (teB b)) @ wx\<rparr>
  \<Longrightarrow> \<forall>i<length (\<pi>). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> teB b
  \<Longrightarrow> lastProduces d (\<pi>)"
  apply(simp add: lastProduces_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
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
     apply(simp add: split_TSstructure_def)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci ci')(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac ci)
  apply(rename_tac i e ci ci' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci' cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac i e ci' w)(*strict*)
  apply(case_tac w)
   apply(rename_tac i e ci' w)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e ci')(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac i e ci' w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci' a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac i e ci' a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e ci' a list ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci' list ba)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac i e ci' list ba)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e ci' list ba ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      d="d"
      and i="i"
      and j="length (\<pi>)-i"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac i e ci' list ba ea)(*strict*)
        apply(force)
       apply(rename_tac i e ci' list ba ea)(*strict*)
       apply(force)
      apply(rename_tac i e ci' list ba ea)(*strict*)
      apply(force)
     apply(rename_tac i e ci' list ba ea)(*strict*)
     apply(force)
    apply(rename_tac i e ci' list ba ea)(*strict*)
    apply(force)
   apply(rename_tac i e ci' list ba ea)(*strict*)
   apply(force)
  apply(rename_tac i e ci' list ba)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(clarsimp)
  apply(rename_tac i e ci' list ba w)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "maxTermPrefix (teB b # wx) = b#maxTermPrefix wx")
   apply(rename_tac i e ci' list ba w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (teB ba # list) = ba#maxTermPrefix list")
    apply(rename_tac i e ci' list ba w)(*strict*)
    apply(clarsimp)
   apply(rename_tac i e ci' list ba w)(*strict*)
   apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
  apply(rename_tac i e ci' list ba w)(*strict*)
  apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
  done

theorem AX_equal_length_production_of_terminal_or_nonterminal: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=e#liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=e#liftA t2\<rparr>
  \<Longrightarrow> case e of teA A \<Rightarrow> left_degen G d1 \<and> left_degen G d2 | teB b \<Rightarrow> lastProduces d1 \<pi>1 \<and> lastProduces d2 \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> length \<pi>1 = length \<pi>2"
  apply(case_tac "length \<pi>1 < length \<pi>2")
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in no_shorter_production_of_terminal_or_nonterminal)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "length \<pi>2 < length \<pi>1")
   apply(rule_tac
      ?d1.0="d2"
      and ?d2.0="d1"
      in no_shorter_production_of_terminal_or_nonterminal)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(case_tac e)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma prod_to_edge_equality_for_terminal_generation: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf = teB b # liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf = teB b # liftA t2\<rparr>
  \<Longrightarrow> length \<pi>1 = length \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> lastProduces d1 \<pi>1
  \<Longrightarrow> lastProduces d2 \<pi>2
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2"
  apply(subgoal_tac "\<pi>1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rename_tac \<pi>1 p1)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(subgoal_tac "\<pi>2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 p1)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 w' a')(*strict*)
  apply(rename_tac \<pi>2 p2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@[p1])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = teB b # liftA t1\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2=p1")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply(rule_tac
      t="length \<pi>2"
      and s="length \<pi>1"
      in ssubst)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply (metis nth_append_beyond)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A1]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p1]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
   apply(case_tac list)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r a lista ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba)(*strict*)
    apply(case_tac t1)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r lista ba a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>1"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r)(*strict*)
  apply(case_tac p1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C1 r1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
  apply(case_tac r1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1)(*strict*)
   apply(case_tac w1)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1)(*strict*)
    apply(case_tac w2)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 C1 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 C1 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
  apply(case_tac w1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 w2 r C1 r1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w2 r C1 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
  apply(thin_tac "liftA (l1 @ l2) = liftA l1 @ liftA l2")
  apply(subgoal_tac "lista=l2")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 lista l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = C1, prod_rhs = teB b # liftA l1\<rparr>"
      in ballE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B)(*strict*)
  apply(case_tac l1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l1 l2 B a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
  apply(case_tac list)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (length(\<pi>1)) = Some (pair e c)")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> (take(length \<pi>1)\<pi>2) c")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(\<pi>1)"
      in cfgLM.trans_der_crop)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="(take(length \<pi>1)\<pi>2)"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>2) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = teB b # liftA t2\<rparr>")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
  apply(subgoal_tac "e2=p2")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 l r)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r list)(*strict*)
   apply(case_tac list)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r list)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r a lista aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r a lista ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r lista ba)(*strict*)
    apply(case_tac t2)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r lista ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r lista ba a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>2"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r)(*strict*)
  apply(case_tac p2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C2 r2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 C1 l2 B e w1 w2 r C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2)(*strict*)
  apply(case_tac r2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 C2)(*strict*)
   apply(case_tac w1)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 C2)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 C2)(*strict*)
    apply(case_tac w2)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 C2)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 C2 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 C2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2 a list)(*strict*)
  apply(case_tac w1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2 a list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2 a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w1 w2 r C2 r2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 r C2 list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 r C2 list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e w2 r C2 list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list lista)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list lista)(*strict*)
   prefer 2
   apply(rule liftA_append)
   apply(rule sym)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 lista l1 l2a)(*strict*)
  apply(thin_tac "liftA (l1 @ l2a) = liftA l1 @ liftA l2a")
  apply(subgoal_tac "lista=l2a")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 lista l1 l2a)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 lista l1 l2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a)(*strict*)
  apply(subgoal_tac "LR1ProdFormSimp G")
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(erule_tac
      x="\<lparr>prod_lhs = C2, prod_rhs = teB b # liftA l1\<rparr>"
      in ballE)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a Ba)(*strict*)
  apply(case_tac l1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a Ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l1 l2a Ba a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba list)(*strict*)
  apply(case_tac list)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba list)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba)(*strict*)
  apply(case_tac A1)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q ba)(*strict*)
   apply(clarsimp)
   apply(case_tac A2)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q ba qa baa)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_single_def)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="[b]"
      and ?B2.0="Ba"
      and ?r2.0="l2aa"
      and ?v1.0="[b]"
      and ?B1.0="B"
      and ?r1.0="l2a"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G'"
      and G'="G"
      in cfgLM_positions_remain_compatible_prime)
                    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
                    apply(simp add: F2LR1inputx_def)
                   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
                   apply(simp add: F2LR1inputx_def)
                  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
                  apply(simp add: F2LR1inputx_def)
                 apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
                apply(simp add: F2LR1inputx_def)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
               apply(force)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
              apply(force)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
             apply(force)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
            apply(force)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
     prefer 2
     apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba qa ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q ba q1 baa q2)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="[b]"
      and ?w2.0="Ba#l2aa"
      and ?v1.0="[b]"
      and ?w1.0="B#l2a"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2)(*strict*)
  apply(case_tac A2)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="[b]"
      and ?w1.0="Ba#l2aa"
      and ?v1.0="[b]"
      and ?w2.0="B#l2a"
      and n="Suc(length \<pi>1)"
      and ?d2.0="d1"
      and ?d1.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q baa)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_single_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="[b]"
      and ?w2.0="Ba#l2a"
      and ?v1.0="[b]"
      and ?w1.0="B#l2"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in cfgLM_positions_remain_compatible_prime_prime)
                 apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                 apply(force)
                apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
                apply(simp add: F2LR1inputx_def)
                apply(force)
               apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
            apply(simp add: split_TSstructure_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2 B e C2 l2a Ba q1 ba q2 q1a baa q2a ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
       apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 C1 l2a B e C2 l2aa Ba q1 ba q2 q1a baa q2a)(*strict*)
  apply(force)
  done

lemma prod_to_edge_equality_for_terminal_and_nonterminal_generation: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=e#liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=e#liftA t2\<rparr>
  \<Longrightarrow> length \<pi>1 = length \<pi>2
  \<Longrightarrow> case e of teA A \<Rightarrow> left_degen G d1 \<and> left_degen G d2 | teB b \<Rightarrow> lastProduces d1 \<pi>1 \<and> lastProduces d2 \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2"
  apply(case_tac e)
   apply(rename_tac a)(*strict*)
   apply(rule prod_to_edge_equality_for_nonterminal_generation)
          apply(rename_tac a)(*strict*)
          apply(force)+
  apply(rename_tac b)(*strict*)
  apply(clarsimp)
  apply(rule prod_to_edge_equality_for_terminal_generation)
         apply(rename_tac b)(*strict*)
         apply(force)+
  done

lemma compatibel_derivation_compatible_first_nonterminal_at_end: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cropTol3l2_single X1 = cropTol3l2_single X2
  \<Longrightarrow> cfgLM.trans_der G d1x \<lparr>cfg_conf = [teA X1]\<rparr> \<pi>1 \<lparr>cfg_conf = teB b # liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2x \<lparr>cfg_conf = [teA X2]\<rparr> \<pi>2 \<lparr>cfg_conf = teB b # liftA t2\<rparr>
  \<Longrightarrow> lastProduces d1x \<pi>1
  \<Longrightarrow> lastProduces d2x \<pi>2
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2
  \<Longrightarrow> cropTol3l2_single (hd t1) = cropTol3l2_single (hd t2)"
  apply(rule_tac
      xs="\<pi>1"
      in rev_cases)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      xs="\<pi>2"
      in rev_cases)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d1x"
      and i="length \<pi>1"
      and kleene_starT="False"
      and END="True"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d2x"
      and i="length \<pi>2"
      and kleene_starT="False"
      and END="True"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
  apply(erule_tac
      x="d1x"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA X1]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>1"
      in allE)
  apply(erule_tac
      x="ci"
      in allE)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p1]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[X]" for X
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia w1 w2)(*strict*)
  apply(case_tac ci)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ci ea cia w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
  apply(erule_tac
      x="d2x"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA X2]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>2"
      in allE)
  apply(erule_tac
      x="cia"
      in allE)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p2]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[X]" for X
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2 w1a w2a)(*strict*)
  apply(case_tac cia)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea cia w1 w2 w1a w2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast w2)")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
    prefer 2
    apply(rule_tac
      \<alpha>="[]"
      and w="[X1]"
      and d="d1x"
      and n="length \<pi>1"
      in only_l3_nonterminals_butlast_preserved)
          apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
        apply(clarsimp)
        apply(force)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
       apply(clarsimp)
       apply(simp add: only_l3_nonterminals_def)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
   apply(subgoal_tac "w1=v1 \<and> w2=v2")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
   apply (metis liftB_liftA_inj1 liftB_liftA_inj2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast w2a)")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
    prefer 2
    apply(rule_tac
      \<alpha>="[]"
      and w="[X2]"
      and d="d2x"
      and n="length \<pi>2"
      in only_l3_nonterminals_butlast_preserved)
          apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
        apply(clarsimp)
        apply(force)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
       apply(clarsimp)
       apply(simp add: only_l3_nonterminals_def)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
   apply(subgoal_tac "w1a=v1 \<and> w2a=v2")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a v1 v2)(*strict*)
   apply (metis liftB_liftA_inj1 liftB_liftA_inj2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(subgoal_tac "notfinishing p1")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(simp add: notfinishing_def)
   apply(clarsimp)
   apply(case_tac "prod_lhs p1")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q1 ba q2)(*strict*)
    apply(simp add: isl3_def)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(thin_tac "cfgLM_step_relation G \<lparr>cfg_conf = liftB w1a @ liftA w2a\<rparr> p2 \<lparr>cfg_conf = teB b # liftA t2\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
   apply(subgoal_tac "w1=l'")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
    prefer 2
    apply (metis initial_liftB_strings_coincide)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a q ba r l')(*strict*)
   apply(case_tac w2)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a q ba r l')(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a q ba r l' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l' list)(*strict*)
   apply(rule_tac
      xs="list"
      in rev_cases)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l' list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l')(*strict*)
    apply(case_tac l')
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l')(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba list)(*strict*)
    apply(subgoal_tac "t1=[] \<and> list=[]")
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba list)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba)(*strict*)
     apply(thin_tac "lastProduces d2x (\<pi>2 @ [p2])")
     apply(simp add: lastProduces_def)
     apply(erule_tac
      x="length \<pi>1"
      in allE)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba list)(*strict*)
    apply (metis liftB_eq_liftA_empty)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l' list ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1a w2a q ba l' ys y)(*strict*)
   apply(simp add: only_l3_nonterminals_def)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1. \<forall>w2 xA. cons_l2 q ba # ys = w1 @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(subgoal_tac "notfinishing p2")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(simp add: notfinishing_def)
   apply(clarsimp)
   apply(case_tac "prod_lhs p2")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
    prefer 2
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q1 ba q2)(*strict*)
    apply(simp add: isl3_def)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(thin_tac "cfgLM_step_relation G \<lparr>cfg_conf = liftB w1 @ liftA w2\<rparr> p1 \<lparr>cfg_conf = teB b # liftA t1\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
   apply(subgoal_tac "w1a=l'")
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
    prefer 2
    apply (metis initial_liftB_strings_coincide)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a q ba r l')(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w2a q ba r l')(*strict*)
   apply(case_tac w2a)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w2a q ba r l')(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w2a q ba r l' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l' list)(*strict*)
   apply(rule_tac
      xs="list"
      in rev_cases)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l' list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l')(*strict*)
    apply(case_tac l')
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l')(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba list)(*strict*)
    apply(subgoal_tac "t2=[] \<and> list=[]")
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba list)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba)(*strict*)
     apply(thin_tac "lastProduces d1x (\<pi>1 @ [p1])")
     apply(simp add: lastProduces_def)
     apply(erule_tac
      x="length \<pi>2"
      in allE)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba list)(*strict*)
    apply (metis liftB_eq_liftA_empty)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l' list ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 q ba l' ys y)(*strict*)
   apply(simp add: only_l3_nonterminals_def)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1. \<forall>w2a xA. butlast w2 = w1 @ xA # w2a \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="[]"
      and P="\<lambda>w1. \<forall>w2 xA. cons_l2 q ba # ys = w1 @ xA # w2 \<longrightarrow> (\<exists>q1 A q2. xA = cons_l3 q1 A q2)"
      in allE)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(rule_tac
      ?p1.0="p1"
      and ?p2.0="p2"
      in nonfinal_prod_to_edge_to_special_production_set)
         apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
       apply(simp add: cfgLM_step_relation_def)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
    apply(simp add: notfinishing_def)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   apply(simp add: notfinishing_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_final_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea w1 w2 w1a w2a i ia A Aa)(*strict*)
   apply(simp add: notfinishing_def)
   apply(simp add: isl3_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x r la ra l')(*strict*)
  apply(subgoal_tac "w1=l'")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x r la ra l')(*strict*)
   prefer 2
   apply (metis initial_liftB_strings_coincide)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x r la ra l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x r la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w1 w2 w1a w2a x r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a x r ra l' l'a)(*strict*)
  apply(subgoal_tac "w1a=l'a")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a x r ra l' l'a)(*strict*)
   prefer 2
   apply (metis initial_liftB_strings_coincide)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w1a w2a x r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w2a x r ra l' l'a)(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w2a x r ra l' l'a)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w2a x r ra l' l'a a list)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w2a x r ra l' l'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea w2 w2a x r ra l' l'a a list aa lista)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(thin_tac "setA (liftB l') = {}")
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l' l'a list lista)(*strict*)
  apply(case_tac l')
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l' l'a list lista)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l' l'a list lista a listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l'a list lista listb)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>1"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l' l'a list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l'a list lista)(*strict*)
  apply(case_tac l'a)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l'a list lista)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l'a list lista a listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista listb)(*strict*)
   apply(simp add: lastProduces_def)
   apply(erule_tac
      x="length \<pi>2"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x l'a list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista y)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
    apply(clarsimp)
    apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_pop_def)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 e ea x list lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista a listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(simp add: F_SDPDA_TO_CFG_STD__edges_l3_push_def F_SDPDA_TO_CFG_STD__edges_l2_push_def)
   apply(clarsimp)
   apply(erule disjE)+
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(erule disjE)+
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(erule disjE)+
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(erule disjE)+
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista y)(*strict*)
  apply(simp add: F_SDPDA_TO_CFG_STD__edges_l2_read_def F_SDPDA_TO_CFG_STD__edges_l3_read_def)
  apply(erule disjE)+
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista y)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta)(*strict*)
    apply(case_tac t1)
     apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta a listb)(*strict*)
    apply(case_tac t2)
     apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta a listb)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta a listb aa listc)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt qta listb listc)(*strict*)
    apply(simp add: cropTol3l2_single_def)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista y)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt)(*strict*)
   apply(case_tac t1)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb)(*strict*)
   apply(case_tac t2)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb aa listc)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt listb listc)(*strict*)
   apply(simp add: cropTol3l2_single_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea x list lista y)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e ea x list lista)(*strict*)
  apply(erule disjE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e ea x list lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt)(*strict*)
   apply(case_tac t1)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb)(*strict*)
   apply(case_tac t2)
    apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt a listb aa listc)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista qt listb listc)(*strict*)
   apply(simp add: cropTol3l2_single_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e ea x list lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e ea x list lista)(*strict*)
  apply(case_tac t1)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e ea x list lista a listb)(*strict*)
  apply(case_tac t2)
   apply(rename_tac \<pi>1 \<pi>2 e ea x list lista a listb)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e ea x list lista a listb aa listc)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_biextend_with_lastProducesX: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G de \<lparr>cfg_conf = [e]\<rparr> \<pi>e \<lparr>cfg_conf = liftB \<alpha>e\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w\<rparr> \<pi> \<lparr>cfg_conf = liftB (\<alpha>@[b])@liftA w'\<rparr>
  \<Longrightarrow> lastProducesX d \<pi> (\<alpha> @ [b])
  \<Longrightarrow> \<exists>d.
  cfgLM.trans_der G d \<lparr>cfg_conf = e#liftA w\<rparr> (\<pi>e@\<pi>) \<lparr>cfg_conf = liftB (\<alpha>e@\<alpha>@[b])@liftA w'\<rparr>
  \<and> lastProducesX d (\<pi>e@\<pi>) (\<alpha>e@\<alpha> @ [b])"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?d1.0="de"
      and ?d2.0="d"
      in cfgLM_trans_der_biextend)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      x="derivation_append (derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>)) (derivation_map d (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>e @ cfg_conf v\<rparr>)) (length \<pi>e)"
      in exI)
  apply(rule conjI)
   apply (simp add: liftB_commutes_over_concat)
  apply(simp add: lastProducesX_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i\<le>length \<pi>e")
   apply(rename_tac i)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: derivation_map_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule_tac
      i="i"
      and d="de"
      in cfgLM.trans_der_position_detail)
      apply(rename_tac i)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea ci)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac i ea ci)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac i ea ci eaa eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="de"
      and i="i"
      and j="length \<pi>e-i"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac i ea ci eaa eb ec)(*strict*)
         apply(simp add: split_TSstructure_def)
        apply(rename_tac i ea ci eaa eb ec)(*strict*)
        apply(force)
       apply(rename_tac i ea ci eaa eb ec)(*strict*)
       apply(force)
      apply(rename_tac i ea ci eaa eb ec)(*strict*)
      apply(force)
     apply(rename_tac i ea ci eaa eb ec)(*strict*)
     apply(force)
    apply(rename_tac i ea ci eaa eb ec)(*strict*)
    apply(force)
   apply(rename_tac i ea ci)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(thin_tac "derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>) 0 = Some (pair None \<lparr>cfg_conf = e # liftA w\<rparr>)")
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(thin_tac " (if \<pi> = [] then derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>) (length (\<pi>e @ \<pi>)) else derivation_map d (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>e @ cfg_conf v\<rparr>) (length (\<pi>e @ \<pi>) - length \<pi>e)) = Some (pair eaa \<lparr>cfg_conf = liftB \<alpha>e @ liftB (\<alpha> @ [b]) @ liftA w'\<rparr>)")
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(thin_tac "cfgLM.derivation G (\<lambda>x. if x \<le> length \<pi>e then derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>) x else derivation_map d (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>e @ cfg_conf v\<rparr>) (x - length \<pi>e))")
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(thin_tac "cfgLM.belongs G (\<lambda>x. if x \<le> length \<pi>e then derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>) x else derivation_map d (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>e @ cfg_conf v\<rparr>) (x - length \<pi>e))")
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(thin_tac "get_labels (\<lambda>x. if x \<le> length \<pi>e then derivation_map de (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftA w\<rparr>) x else derivation_map d (\<lambda>v. \<lparr>cfg_conf = liftB \<alpha>e @ cfg_conf v\<rparr>) (x - length \<pi>e)) (length \<pi>e + length \<pi>) = map Some \<pi>e @ map Some \<pi>")
   apply(rename_tac i ea ci wa eaa)(*strict*)
   apply(simp add: get_configuration_def)
   apply(rename_tac i ea ci wa)(*strict*)
   apply(case_tac ci)
   apply(rename_tac i ea ci wa cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea wa cfg_confa)(*strict*)
   apply(rename_tac wx)
   apply(rename_tac i ea wa wx)(*strict*)
   apply(subgoal_tac "maxTermPrefix wx @ wa = \<alpha>e")
    apply(rename_tac i ea wa wx)(*strict*)
    apply(thin_tac "maxTermPrefix wx @ wa = maxTermPrefix (liftB \<alpha>e)")
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac i ea wa wx c)(*strict*)
    apply(case_tac "setA wx = {}")
     apply(rename_tac i ea wa wx c)(*strict*)
     apply(subgoal_tac "\<exists>l'. liftB l' = wx")
      apply(rename_tac i ea wa wx c)(*strict*)
      prefer 2
      apply(rule_tac
      x="filterB wx"
      in exI)
      apply (rule liftBDeConv2)
      apply (metis setA_liftB_substring liftB_commutes_over_concat)
     apply(rename_tac i ea wa wx c)(*strict*)
     apply(clarsimp)
     apply(rename_tac i ea wa c l')(*strict*)
     apply(subgoal_tac "liftB (l' @ wa @ \<alpha> @ [b]) @ c = liftB l' @ liftA w")
      apply(rename_tac i ea wa c l')(*strict*)
      apply (simp add:liftB_commutes_over_concat)
      apply(case_tac w)
       apply(rename_tac i ea wa c l')(*strict*)
       apply(clarsimp)
      apply(rename_tac i ea wa c l' a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac i ea w c l' a list)(*strict*)
      apply(case_tac w)
       apply(rename_tac i ea w c l' a list)(*strict*)
       apply(clarsimp)
       apply(rename_tac i ea c l' a list)(*strict*)
       apply(case_tac \<alpha>)
        apply(rename_tac i ea c l' a list)(*strict*)
        apply(clarsimp)
       apply(rename_tac i ea c l' a list aa lista)(*strict*)
       apply(clarsimp)
      apply(rename_tac i ea w c l' a list aa lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac i ea wa c l')(*strict*)
     apply(rule_tac
      t="liftB l' @ liftA w"
      and s="liftB (maxTermPrefix (liftB l') @ wa @ \<alpha> @ [b]) @ c"
      in subst)
      apply(rename_tac i ea wa c l')(*strict*)
      apply(force)
     apply(rename_tac i ea wa c l')(*strict*)
     apply(rule_tac
      t="maxTermPrefix (liftB l')"
      and s="l'"
      in ssubst)
      apply(rename_tac i ea wa c l')(*strict*)
      apply (metis maxTermPrefix_term_string)
     apply(rename_tac i ea wa c l')(*strict*)
     apply(force)
    apply(rename_tac i ea wa wx c)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac i ea wa wx c)(*strict*)
     prefer 2
     apply(rule left_most_terminal_exists)
     apply(force)
    apply(rename_tac i ea wa wx c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i ea wa c w1 w2 A)(*strict*)
    apply(thin_tac "setA (liftB w1 @ teA A # w2) \<noteq> {}")
    apply(subgoal_tac "liftB (w1 @ wa @ \<alpha> @ [b]) @ c = liftB w1 @ teA A # w2 @ liftA w")
     apply(rename_tac i ea wa c w1 w2 A)(*strict*)
     apply(thin_tac "liftB (maxTermPrefix (liftB w1 @ teA A # w2) @ wa @ \<alpha> @ [b]) @ c = liftB w1 @ teA A # w2 @ liftA w")
     apply(rename_tac i ea wa c w1 w2 A)(*strict*)
     apply (simp add:liftB_commutes_over_concat)
     apply(case_tac wa)
      apply(rename_tac i ea wa c w1 w2 A)(*strict*)
      apply(clarsimp)
      apply(rename_tac i ea c w1 w2 A)(*strict*)
      apply(case_tac \<alpha>)
       apply(rename_tac i ea c w1 w2 A)(*strict*)
       apply(clarsimp)
      apply(rename_tac i ea c w1 w2 A a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac i ea wa c w1 w2 A a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac i ea wa c w1 w2 A)(*strict*)
    apply(rule_tac
      t="liftB w1 @ teA A # w2 @ liftA w"
      and s="liftB (maxTermPrefix (liftB w1 @ teA A # w2) @ wa @ \<alpha> @ [b]) @ c"
      in subst)
     apply(rename_tac i ea wa c w1 w2 A)(*strict*)
     apply(force)
    apply(rename_tac i ea wa c w1 w2 A)(*strict*)
    apply(rule_tac
      t="maxTermPrefix (liftB w1 @ teA A # w2)"
      and s="w1"
      in ssubst)
     apply(rename_tac i ea wa c w1 w2 A)(*strict*)
     apply(rule maxTermPrefix_mixed_string)
    apply(rename_tac i ea wa c w1 w2 A)(*strict*)
    apply(force)
   apply(rename_tac i ea wa wx)(*strict*)
   apply(rule_tac
      t="\<alpha>e"
      and s="maxTermPrefix (liftB \<alpha>e)"
      in subst)
    apply(rename_tac i ea wa wx)(*strict*)
    apply (rule maxTermPrefix_term_string)
   apply(rename_tac i ea wa wx)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length \<pi>e<i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      i="i-length \<pi>e"
      and d="d"
      in cfgLM.trans_der_position_detail)
     apply(rename_tac i)(*strict*)
     apply(simp add: split_TSstructure_def)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ci)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="i-length \<pi>e"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac i ci)(*strict*)
   apply(force)
  apply(rename_tac i ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac i ci cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i cfg_confa)(*strict*)
  apply(rename_tac wx)
  apply(rename_tac i wx)(*strict*)
  apply(simp add: prefix_def)
  apply (simp add: liftB_commutes_over_concat)
  done

lemma cfgLM_trans_der_concat_extend_with_lastProducesX: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = w1\<rparr> \<pi>1 \<lparr>cfg_conf = liftB v1 @ v2 @ v4\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = v2\<rparr> \<pi>2 \<lparr>cfg_conf = v3\<rparr>
  \<Longrightarrow> \<not> prefix w (maxTermPrefix(v2 @ v4))
  \<Longrightarrow> lastProducesX d2 \<pi>2 w
  \<Longrightarrow> cfgLM.trans_der G (derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v @ v4\<rparr>)) (length \<pi>1)) \<lparr>cfg_conf = w1\<rparr> (\<pi>1 @ \<pi>2) \<lparr>cfg_conf = liftB v1 @ v3 @ v4\<rparr> \<and> lastProducesX (derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v @ v4\<rparr>)) (length \<pi>1)) (\<pi>1@\<pi>2) (v1@w)"
  apply(rule context_conjI)
   apply(rule cfgLM_trans_der_concat_extend)
     apply(force)+
  apply(simp add: lastProducesX_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i=length \<pi>1")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac e ea c)(*strict*)
   apply (simp only: liftB_commutes_over_concat)
   apply(clarsimp)
   apply (metis maxTermPrefix_shift)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i<length \<pi>1")
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac i e ea eb)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      g="d1"
      and n="i"
      and m="length(\<pi>1)"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac i e ea eb)(*strict*)
      apply(force)
     apply(rename_tac i e ea eb)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
   apply(case_tac c)
   apply(rename_tac i e c cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e cfg_confa)(*strict*)
   apply(rename_tac wx)
   apply(rename_tac i e wx)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac i e wx)(*strict*)
    prefer 2
    apply(simp (no_asm_use) add: cfgLM.trans_der_def)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac i e wx ea eb ec)(*strict*)
    apply(rule_tac
      d="d1"
      and i="i"
      and j="length \<pi>1-i"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac i e wx ea eb ec)(*strict*)
         apply(force)
        apply(rename_tac i e wx ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac i e wx ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac i e wx ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac i e wx ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac i e wx ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac i e wx)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e wx wa)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac i e wa c)(*strict*)
   apply(subgoal_tac "maxTermPrefix (liftB (v1 @ w) @ c) = (v1@w)@maxTermPrefix c")
    apply(rename_tac i e wa c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "maxTermPrefix (liftB v1@v2@v4) = v1@maxTermPrefix (v2@v4)")
     apply(rename_tac i e wa c)(*strict*)
     apply(force)
    apply(rename_tac i e wa c)(*strict*)
    apply (metis maxTermPrefix_shift)
   apply(rename_tac i e wa c)(*strict*)
   apply (metis maxTermPrefix_shift)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length \<pi>1 < i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      g="d2"
      and n="i-length \<pi>1"
      and m="length(\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac i e ea eb)(*strict*)
     apply(force)
    apply(rename_tac i e ea eb)(*strict*)
    apply(force)
   apply(rename_tac i e ea eb)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(simp (no_asm_use) add: cfgLM.trans_der_def)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac i e c ea eb ec)(*strict*)
   apply(rule_tac
      d="derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v @ v4\<rparr>)) (length \<pi>1)"
      and i="length \<pi>1"
      and j="i-length \<pi>1"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac i e c ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac i e c ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac i e c ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac i e c ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac i e c ea eb ec)(*strict*)
    apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
   apply(rename_tac i e c ea eb ec)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
  apply(rename_tac i e c)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e c ea eb ec wa)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      d="derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v @ v4\<rparr>)) (length \<pi>1)"
      and i="i"
      and j="length (\<pi>1@\<pi>2)-i"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac i e c ea eb ec wa)(*strict*)
        apply(force)
       apply(rename_tac i e c ea eb ec wa)(*strict*)
       apply(force)
      apply(rename_tac i e c ea eb ec wa)(*strict*)
      apply(force)
     apply(rename_tac i e c ea eb ec wa)(*strict*)
     apply(force)
    apply(rename_tac i e c ea eb ec wa)(*strict*)
    apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
   apply(rename_tac i e c ea eb ec wa)(*strict*)
   apply(rule_tac
      t="i + (length (\<pi>1 @ \<pi>2) - i)"
      and s="length (\<pi>1 @ \<pi>2)"
      in ssubst)
    apply(rename_tac i e c ea eb ec wa)(*strict*)
    apply(force)
   apply(rename_tac i e c ea eb ec wa)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c wa waa)(*strict*)
  apply(simp add: get_configuration_def derivation_append_def derivation_map_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac i e c wa waa ca)(*strict*)
  apply(erule_tac
      x="i-length \<pi>1"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac i e c wa waa ca)(*strict*)
   apply(force)
  apply(rename_tac i e c wa waa ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e c wa waa ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e wa waa ca cfg_confa)(*strict*)
  apply(rename_tac wx)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(subgoal_tac "maxTermPrefix (liftB v1 @ v2 @ v4) = v1@maxTermPrefix (v2 @ v4)")
   apply(rename_tac i e wa waa ca wx)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_shift)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (liftB v1 @ wx @ v4) = v1@maxTermPrefix (wx @ v4)")
   apply(rename_tac i e wa waa ca wx)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_shift)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (liftB v1 @ v3 @ v4) = v1@maxTermPrefix (v3 @ v4)")
   apply(rename_tac i e wa waa ca wx)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_shift)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(clarsimp)
  apply(thin_tac "maxTermPrefix (liftB v1 @ v2 @ v4) = v1 @ maxTermPrefix (v2 @ v4)")
  apply(thin_tac "maxTermPrefix (liftB v1 @ wx @ v4) = v1 @ maxTermPrefix (wx @ v4)")
  apply(thin_tac "maxTermPrefix (liftB v1 @ v3 @ v4) = v1 @ maxTermPrefix (v3 @ v4)")
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(subgoal_tac "prefix (liftB w) wx \<or> SSx" for SSx)
   apply(rename_tac i e wa waa ca wx)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e wa waa ca wx)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac i e wa waa ca wx)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac i e wa waa ca wx c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e wa waa ca wx c)(*strict*)
   prefer 2
   apply(rule liftB_append)
   apply(force)
  apply(rename_tac i e wa waa ca wx c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e w wa ca l1 l2)(*strict*)
  apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (i-length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i e w wa ca l1 l2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e w wa ca l1 l2 ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e w wa ca l1 l2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac i e w wa ca l1 l2 ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac i e w wa ca l1 l2 ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac i e w wa ca l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e w wa ca l1 l2 e2 c2 ea)(*strict*)
  apply(case_tac l2)
   apply(rename_tac i e w wa ca l1 l2 e2 c2 ea)(*strict*)
   apply(force)
  apply(rename_tac i e w wa ca l1 l2 e2 c2 ea a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e w wa ca l1 e2 c2 ea a list)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e w wa ca l1 e2 c2 ea a list l r)(*strict*)
  apply (metis liftB_with_nonterminal_inside)
  done

lemma AX_equal_length_production_of_multiple_terminal_hlp1: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB(\<alpha>@[b])@liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB(\<alpha>@[b])@liftA t2\<rparr>
  \<Longrightarrow> lastProducesX d1 \<pi>1 (\<alpha>@[b])
  \<Longrightarrow> lastProducesX d2 \<pi>2 (\<alpha>@[b])
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> \<pi>1 \<noteq> []
  \<Longrightarrow> length \<pi>1 < length \<pi>2
  \<Longrightarrow> Q"
  apply(subgoal_tac "\<pi>1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rename_tac \<pi>1 p1)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(subgoal_tac "\<pi>2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 p1)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 w' a')(*strict*)
  apply(rename_tac \<pi>2 p2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@[p1])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = liftB (\<alpha> @ [b]) @ liftA t1\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2=p1")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A1]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p1]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "w1=l'")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
   prefer 2
   apply (metis append_Nil2 maxTermPrefix_liftA maxTermPrefix_mixed_string maxTermPrefix_shift)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l')(*strict*)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l')(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' list)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1)(*strict*)
   prefer 2
   apply(rule_tac
      a="\<alpha>@[b]"
      and b="t1"
      and c="l'"
      in prefix_of_liftB_prefixes)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 c)(*strict*)
  apply(subgoal_tac "c=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 c)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 c)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1)(*strict*)
   apply(simp add: lastProducesX_def)
   apply(erule_tac
      x="length \<pi>1"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 w')(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(case_tac p1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 w' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac X1 r1)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
  apply(subgoal_tac "\<exists>B1. r1=[teB b,teA B1]")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
   prefer 2
   apply(subgoal_tac "LR1ProdFormSimp G")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = X1, prod_rhs = r1\<rparr>"
      in ballE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
   apply(clarsimp)
   apply(case_tac r1)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1)(*strict*)
    apply(case_tac w')
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1)(*strict*)
     apply(case_tac w1)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1)(*strict*)
      apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 a list)(*strict*)
    apply(case_tac w1)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' ba A B)(*strict*)
    apply(case_tac w')
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' ba A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' ba A B a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B list)(*strict*)
    apply(case_tac list)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B list)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B)(*strict*)
    apply(case_tac w')
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 a list ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B C)(*strict*)
   apply(case_tac w')
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B C)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' A B C a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 r1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 B1)(*strict*)
  apply(case_tac w')
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 B1)(*strict*)
   prefer 2
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 B1 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list)(*strict*)
   apply(case_tac list)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 w' X1 B1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1)(*strict*)
  apply(case_tac t1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list)(*strict*)
  apply(subgoal_tac "list=w1")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (Suc(length(\<pi>1))) = Some (pair e c)")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> (take(Suc(length \<pi>1))\<pi>2) c")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc(length(\<pi>1))"
      in cfgLM.trans_der_crop)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="(take(Suc(length \<pi>1))\<pi>2)"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c w1a w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e c w1a w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2)(*strict*)
  apply(subgoal_tac "prefix w1a (l'@[b])")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="d2"
      and i="Suc(length \<pi>1)"
      and j="Suc(length \<pi>2)-Suc(length \<pi>1)"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 ea eb ec)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "maxTermPrefix (liftB w1a @ liftA w2) = w1a")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 w)(*strict*)
    apply(subgoal_tac "maxTermPrefix (liftB l' @ teB b # liftA t2)= (l'@[b]) ")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 w)(*strict*)
     apply(simp add: prefix_def)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 w)(*strict*)
    apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA maxTermPrefix_drop_liftA maxTermPrefix_shift maxTermPrefix_term_string)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 w)(*strict*)
   apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA maxTermPrefix_drop_liftA maxTermPrefix_shift maxTermPrefix_term_string)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 c)(*strict*)
  apply(subgoal_tac "c=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 c)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 c)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w2)(*strict*)
   apply(simp add: lastProducesX_def)
   apply(erule_tac
      x="Suc(length \<pi>1)"
      in allE)+
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: prefix_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 X1 B1 e w1a w2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w2 w')(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w2 w')(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w')(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (Suc(length \<pi>1)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w')(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' ea eb ec)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length (\<pi>2@[p2])"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w')(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' e2 c2 l r)(*strict*)
   apply (metis liftB_with_nonterminal_inside)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w2 w' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' a list)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> (\<pi>2 @ [p2]) \<lparr>cfg_conf = liftB w1a @ liftB w' @ teB b # liftA t2\<rparr>")
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' a list)(*strict*)
  apply(rename_tac C w)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w)(*strict*)
  apply(case_tac A1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q ba)(*strict*)
   apply(clarsimp)
   apply(case_tac A2)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q ba qa baa)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_single_def)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="w'@[b]"
      and ?v2.0="w1a"
      and ?B2.0="C"
      and ?r2.0="w"
      and ?v1.0="w1a@w'@[b]"
      and ?B1.0="B1"
      and ?r1.0="w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G'"
      and G'="G"
      in cfgLM_positions_remain_compatible_prime)
                    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
                    apply(simp add: F2LR1inputx_def)
                   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
                   apply(simp add: F2LR1inputx_def)
                  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
                  apply(simp add: F2LR1inputx_def)
                 apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
                apply(simp add: F2LR1inputx_def)
               apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
               apply(force)
              apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
              apply(force)
             apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
             apply(force)
            apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
            apply(force)
           apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
      apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba ea eb)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w qa ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q ba q1 baa q2)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="w'@[b]"
      and ?v2.0="w1a"
      and ?w2.0="C#w"
      and ?v1.0="w1a@w'@[b]"
      and ?w1.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 ea eb)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2)(*strict*)
  apply(case_tac A2)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x2.0="[]"
      and ?x1.0="w'@[b]"
      and ?v1.0="w1a"
      and ?w1.0="C#w"
      and ?v2.0="w1a@w'@[b]"
      and ?w2.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d2.0="d1"
      and ?d1.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa ea eb)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q baa)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a)(*strict*)
  apply(simp add: cropTol3l2_single_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="w'@[b]"
      and ?v2.0="w1a"
      and ?w2.0="C#w"
      and ?v1.0="w1a@w'@[b]"
      and ?w1.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G'"
      and G'="G"
      in cfgLM_positions_remain_compatible_prime_prime)
                 apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
                apply(simp add: F2LR1inputx_def)
               apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
            apply(simp add: split_TSstructure_def)
           apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
      apply(clarsimp)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q2 q1a ba q2a eb)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q2 q1a ba q2a eb)(*strict*)
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a ea eb)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 X1 B1 e w1a w' C w q1 ba q2 q1a baa q2a)(*strict*)
  apply(force)
  done

theorem AX_equal_length_production_of_multiple_terminal: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=liftB(\<alpha>@[b])@liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB(\<alpha>@[b])@liftA t2\<rparr>
  \<Longrightarrow> lastProducesX d1 \<pi>1 (\<alpha>@[b])
  \<Longrightarrow> lastProducesX d2 \<pi>2 (\<alpha>@[b])
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> length \<pi>1 = length \<pi>2"
  apply(case_tac "length \<pi>1 < length \<pi>2")
   apply(clarsimp)
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in AX_equal_length_production_of_multiple_terminal_hlp1)
           apply(force)+
    apply(case_tac \<pi>1)
     apply(clarsimp)
     apply(simp add: cfgLM.trans_der_def)
     apply(clarsimp)
     apply(rename_tac ea)(*strict*)
     apply(case_tac \<alpha>)
      apply(rename_tac ea)(*strict*)
      apply(clarsimp)
     apply(rename_tac ea a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(force)
  apply(case_tac "length \<pi>2 < length \<pi>1")
   apply(clarsimp)
   apply(rule_tac
      ?d1.0="d2"
      and ?d2.0="d1"
      in AX_equal_length_production_of_multiple_terminal_hlp1)
           apply(force)+
    apply(case_tac \<pi>1)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac a list e)(*strict*)
    apply(case_tac \<alpha>)
     apply(rename_tac a list e)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list e aa lista)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(force)
  done

lemma prod_to_edge_equality_for_terminal_generation_multiple_terminals: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf = (liftB (\<alpha>@[b])) @ liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf = (liftB (\<alpha>@[b])) @ liftA t2\<rparr>
  \<Longrightarrow> length \<pi>1 = length \<pi>2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> lastProducesX d1 \<pi>1 (\<alpha>@[b])
  \<Longrightarrow> lastProducesX d2 \<pi>2 (\<alpha>@[b])
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2"
  apply(subgoal_tac "\<pi>1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rename_tac \<pi>1 p1)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(subgoal_tac "\<pi>2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac \<pi>1 p1)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(erule disjE)
   apply(rename_tac \<pi>1 p1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 w' a')(*strict*)
  apply(rename_tac \<pi>2 p2)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@[p1])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = liftB (\<alpha> @ [b]) @ liftA t1\<rparr>")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2=p1")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply(rule_tac
      t="length \<pi>2"
      and s="length \<pi>1"
      in ssubst)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
   apply (metis nth_append_beyond)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 c1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A1]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>1"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p1]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A1]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
  apply(subgoal_tac "w1=l'")
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
   prefer 2
   apply (metis initial_liftB_strings_coincide)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w1 w2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac w2)
   apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l')(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 w2 r l' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' list)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1)(*strict*)
  apply(case_tac p1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C1 r1)
  apply(rename_tac \<pi>1 p1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
  apply(simp add: lastProducesX_def)
  apply(erule_tac
      x="length \<pi>2"
      in allE)+
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(simp add: prefix_def)
  apply(subgoal_tac "\<exists>B1. r1=[teB b,teA B1]")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
   prefer 2
   apply(subgoal_tac "LR1ProdFormSimp G")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = C1, prod_rhs = r1\<rparr>"
      in ballE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
   apply(clarsimp)
   apply(case_tac r1)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1)(*strict*)
    apply(subgoal_tac "l'=\<alpha>@[b]")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B)(*strict*)
    apply(subgoal_tac "\<alpha>@[b] = l'@[ba]")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B)(*strict*)
    apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t1 = liftB (l'@[ba]) @ liftA (B#w1)")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B)(*strict*)
     prefer 2
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 ba A B)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B)(*strict*)
    apply(subgoal_tac "\<alpha>@[b] = l'")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B)(*strict*)
    apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t1 = liftB (l') @ liftA (B#w1)")
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B)(*strict*)
     prefer 2
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 a list ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B C)(*strict*)
   apply(subgoal_tac "\<alpha>@[b] = l'")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B C)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B C)(*strict*)
   apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t1 = liftB (l') @ liftA (B#C#w1)")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B C)(*strict*)
    prefer 2
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 A B C)(*strict*)
   apply (metis liftB_liftA_inj1)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 r1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 B1)(*strict*)
  apply(subgoal_tac "\<alpha>@[b]=l'@[b]")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 B1)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t1 = liftB (l'@[b]) @ liftA (B1#w1)")
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 B1)(*strict*)
    prefer 2
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 B1)(*strict*)
   apply (metis liftB_liftA_inj1)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 l' w1 C1 B1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(case_tac t1)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 list)(*strict*)
  apply(subgoal_tac "list=w1")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 list)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@[p1])"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
  apply(subgoal_tac "c2 = \<lparr>cfg_conf = liftB (\<alpha> @ [b]) @ liftA t2\<rparr>")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply (simp only: liftB_commutes_over_concat)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2=p2")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
   apply(rule_tac
      t="length \<pi>2"
      and s="length \<pi>1"
      in ssubst)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
   apply (metis nth_append_beyond)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a c1 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
  apply(subgoal_tac "(\<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = liftB w1 @ liftA w2) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2))")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
   prefer 2
   apply(simp add: split_TSstructure_def CFGtermLeft_def)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = [teA A2]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<pi>2"
      in allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      and v="[Some p2]"
      in get_labels_drop_tail)
    apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[A2]"
      in exI)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB_substring liftB_commutes_over_concat)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 r l')(*strict*)
  apply(subgoal_tac "w1a=l'")
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 r l')(*strict*)
   prefer 2
   apply (metis initial_liftB_strings_coincide)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w1a w2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac w2)
   apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w2 r l')(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a w2 r l' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a l' list)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a l' w2)(*strict*)
  apply(case_tac p2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a l' w2 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C2 r2)
  apply(rename_tac \<pi>1 \<pi>2 p2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
  apply(subgoal_tac "\<exists>B2. r2=[teB b,teA B2]")
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
   prefer 2
   apply(subgoal_tac "LR1ProdFormSimp G")
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
    prefer 2
    apply(simp add: split_TSstructure_def)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="\<lparr>prod_lhs = C2, prod_rhs = r2\<rparr>"
      in ballE)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
   apply(clarsimp)
   apply(case_tac r2)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2)(*strict*)
    apply(subgoal_tac "l'=\<alpha>@[b]")
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2)(*strict*)
     apply(subgoal_tac "t2=w2")
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2)(*strict*)
      apply(clarsimp)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a C2)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2)(*strict*)
     apply(rule liftA_inj)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 ba A B)(*strict*)
    apply(subgoal_tac "\<alpha>@[b] = l'@[ba]")
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 ba A B)(*strict*)
     apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 ba A B)(*strict*)
    apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t2 = liftB (l'@[ba]) @ liftA (B#w2)")
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 ba A B)(*strict*)
     prefer 2
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 ba A B)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 a list ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 a list ba A B)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B)(*strict*)
    apply(subgoal_tac "\<alpha>@[b] = l'")
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 A B)(*strict*)
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B)(*strict*)
    apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t2 = liftB (l') @ liftA (B#w2)")
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B)(*strict*)
     prefer 2
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B)(*strict*)
    apply (metis liftB_liftA_inj1)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 a list ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B C)(*strict*)
   apply(subgoal_tac "\<alpha>@[b] = l'")
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B C)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 A B C)(*strict*)
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B C)(*strict*)
   apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t2 = liftB (l') @ liftA (B#C#w2)")
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B C)(*strict*)
    prefer 2
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 A B C)(*strict*)
   apply (metis liftB_liftA_inj1)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 B2)(*strict*)
  apply(subgoal_tac "\<alpha>@[b]=l'@[b]")
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 B2)(*strict*)
   prefer 2
   apply(subgoal_tac "liftB (\<alpha> @ [b]) @ liftA t2 = liftB (l'@[b]) @ liftA (B2#w2)")
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 B2)(*strict*)
    prefer 2
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 B2)(*strict*)
   apply (metis liftB_liftA_inj1)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a l' w2 C2 B2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(clarsimp)
  apply(case_tac t2)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2)(*strict*)
   apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 list)(*strict*)
  apply(subgoal_tac "list=w2")
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 list)(*strict*)
   prefer 2
   apply(rule liftA_inj)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2)(*strict*)
  apply(case_tac A1)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q ba)(*strict*)
   apply(clarsimp)
   apply(case_tac A2)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q ba qa baa)(*strict*)
    apply(clarsimp)
    apply(simp add: cropTol3l2_single_def)
    apply(clarsimp)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
     prefer 2
     apply(unfold cfgLM.trans_der_def)
     apply(erule exE)+
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
     apply(fold cfgLM.trans_der_def)
     apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="\<alpha>@[b]"
      and ?B2.0="B2"
      and ?r2.0="w2"
      and ?v1.0="\<alpha>@[b]"
      and ?B1.0="B1"
      and ?r1.0="w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G'"
      and G'="G"
      in cfgLM_positions_remain_compatible_prime)
                    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
                    apply(simp add: F2LR1inputx_def)
                   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
                   apply(simp add: F2LR1inputx_def)
                  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
                  apply(simp add: F2LR1inputx_def)
                 apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
                apply(simp add: F2LR1inputx_def)
               apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
               apply(force)
              apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
              apply(force)
             apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
             apply(force)
            apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
            apply(force)
           apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
     prefer 2
     apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
         apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 qa ba)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q ba q1 baa q2)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="\<alpha>@[b]"
      and ?w2.0="B2#w2"
      and ?v1.0="\<alpha>@[b]"
      and ?w1.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2)(*strict*)
  apply(case_tac A2)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
   apply(clarsimp)
   apply(simp add: cropTol3l2_single_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="\<alpha>@[b]"
      and ?w1.0="B2#w2"
      and ?v1.0="\<alpha>@[b]"
      and ?w2.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d2.0="d1"
      and ?d1.0="d2"
      and G="G"
      and G'="G'"
      in cfgLM_positions_remain_compatible_l2l3)
               apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
            apply(simp add: F2LR1inputx_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
           apply(simp add: F2LR1inputx_def)
          apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
       apply (simp only: liftB_commutes_over_concat)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
      apply (simp only: liftB_commutes_over_concat)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa e ea)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q baa)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(clarsimp)
  apply(simp add: cropTol3l2_single_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      ?x1.0="[]"
      and ?x2.0="[]"
      and ?v2.0="\<alpha>@[b]"
      and ?w2.0="B2#w2"
      and ?v1.0="\<alpha>@[b]"
      and ?w1.0="B1#w1"
      and n="Suc(length \<pi>1)"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in cfgLM_positions_remain_compatible_prime_prime)
                 apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
                 apply(simp add: F2LR1inputx_def)
                 apply(force)
                apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
                apply(simp add: F2LR1inputx_def)
                apply(force)
               apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
               apply(simp add: F2LR1inputx_def)
              apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
              apply(simp add: F2LR1inputx_def)
             apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
             apply(simp add: F2LR1inputx_def)
            apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
            apply(simp add: split_TSstructure_def)
           apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
           apply(force)
          apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
          apply(force)
         apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
     apply (simp only: liftB_commutes_over_concat)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
    apply (simp only: liftB_commutes_over_concat)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a e ea)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in equal_F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1_to_equal_prod_to_edge)
       apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 e1 w1 C1 B1 e1a w2 C2 B2 q1 ba q2 q1a baa q2a)(*strict*)
  apply(force)
  done

lemma equal_split_prefix_hlp2_withMIP_simplified: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi>1 \<lparr>cfg_conf=e#liftA t1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi>2 \<lparr>cfg_conf=e#liftA t2\<rparr>
  \<Longrightarrow> cfgLM.trans_der G de \<lparr>cfg_conf=[e]\<rparr> \<pi>e \<lparr>cfg_conf=liftB \<alpha>e\<rparr>
  \<Longrightarrow> cfgLMMIP G d1' ((liftA nt1)) \<pi>1' (liftB (\<alpha>@[b])) (liftA tn1)
  \<Longrightarrow> cfgLMMIP G d2' ((liftA nt2)) \<pi>2' (liftB (\<alpha>@[b])) (liftA tn2)
  \<Longrightarrow> case e of teA A \<Rightarrow> left_degen G d1 \<and> left_degen G d2 | teB b \<Rightarrow> lastProduces d1 \<pi>1 \<and> lastProduces d2 \<pi>2
  \<Longrightarrow> nt1 = butn t1 n1
  \<Longrightarrow> nt2 = butn t2 n2
  \<Longrightarrow> cropTol3l2_single A1 = cropTol3l2_single A2
  \<Longrightarrow> \<pi>1' \<noteq> []
  \<Longrightarrow> \<pi>2' \<noteq> []
  \<Longrightarrow> map (prod_to_edge G') \<pi>1 = map (prod_to_edge G') \<pi>2
  \<and> drop_and_crop nt1 0 = drop_and_crop nt2 0"
  apply(subgoal_tac "n1<length t1")
   prefer 2
   apply(clarsimp)
   apply(case_tac "n1<length t1")
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "length t1 \<le> n1")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(simp add: butn_def)
   apply(simp add: cfgLMMIP_def)
   apply(clarsimp)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(clarsimp)
  apply(subgoal_tac "n2<length t2")
   prefer 2
   apply(clarsimp)
   apply(case_tac "n2<length t2")
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "length t2 \<le> n2")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(simp add: butn_def)
   apply(simp add: cfgLMMIP_def)
   apply(clarsimp)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(clarsimp)
  apply(subgoal_tac "length \<pi>1 = length \<pi>2")
   prefer 2
   apply(rule AX_equal_length_production_of_terminal_or_nonterminal)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in prod_to_edge_equality_for_terminal_and_nonterminal_generation)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(unfold cfgLMMIP_def)
   apply(erule conjE)+
   apply(fold cfgLMMIP_def)
   apply(rule_tac
      de="de"
      and d="d1'"
      in cfgLM_trans_der_biextend_with_lastProducesX)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: lastProducesX_def)
   apply(thin_tac "cfgLMMIyX G d2' (liftA (butn t2 n2)) \<pi>2'")
   apply(thin_tac "cfgLMMPX G d2' (liftA (butn t2 n2)) \<pi>2' (liftB (\<alpha> @ [b])) (liftA tn2)")
   apply(simp add: cfgLMMPX_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="take i \<pi>1'"
      in allE)
   apply(simp add: strict_prefix_def)
   apply(erule impE)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      x="drop i \<pi>1'"
      in exI)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac i ea eaa eb ec ed)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      g="d1'"
      and n="i"
      and m="length(\<pi>1')"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac i ea eaa eb ec ed)(*strict*)
      apply(force)
     apply(rename_tac i ea eaa eb ec ed)(*strict*)
     apply(force)
    apply(rename_tac i ea eaa eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac i ea c cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea cfg_conf)(*strict*)
   apply(rename_tac wx)
   apply(rename_tac i ea wx)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac i ea c)(*strict*)
   apply(erule_tac
      x="d1'"
      in allE)
   apply(erule_tac
      x="c"
      in allE)
   apply(subgoal_tac "cfgLM.trans_der G d1' \<lparr>cfg_conf = liftA (butn t1 n1)\<rparr> (take i \<pi>1') \<lparr>cfg_conf = liftB (\<alpha> @ [b]) @ c\<rparr>")
    apply(rename_tac i ea c)(*strict*)
    apply(force)
   apply(rename_tac i ea c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i ea c)(*strict*)
    prefer 2
    apply(rule_tac
      n="i"
      and d="d1'"
      in cfgLM.trans_der_crop)
        apply(rename_tac i ea c)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac i ea c)(*strict*)
       apply(force)
      apply(rename_tac i ea c)(*strict*)
      apply(force)
     apply(rename_tac i ea c)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac i ea c)(*strict*)
    apply(force)
   apply(rename_tac i ea c)(*strict*)
   apply(force)
  apply(erule exE)+
  apply(rename_tac d)(*strict*)
  apply(rename_tac de1')
  apply(rename_tac de1')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac de1')(*strict*)
   prefer 2
   apply(rule_tac
      w="X"
      and ?v1.0="[]"
      and ?v4.0="liftA(takeB n1 t1)"
      and ?d1.0="d1"
      and ?d2.0="de1'" for X
      in cfgLM_trans_der_concat_extend_with_lastProducesX)
       apply(rename_tac de1')(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac de1')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac de1')(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="e # liftA (butn t1 n1) @ liftA (takeB n1 t1)"
      and s="e # liftA t1"
      in ssubst)
      apply(rename_tac de1')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac de1')(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="liftA (butn t1 n1) @ liftA (takeB n1 t1)"
      and s="liftA (butn t1 n1 @ takeB n1 t1)"
      in ssubst)
      apply(rename_tac de1')(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac de1')(*strict*)
     apply(rule_tac
      f="liftA"
      in arg_cong)
     apply(simp add: butn_def takeB_def)
    apply(rename_tac de1')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac de1')(*strict*)
   apply(simp add: prefix_def)
   apply(rule_tac
      t="e # liftA (butn t1 n1) @ liftA (takeB n1 t1)"
      and s="e # liftA t1"
      in ssubst)
    apply(rename_tac de1')(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="liftA (butn t1 n1) @ liftA (takeB n1 t1)"
      and s="liftA (butn t1 n1 @ takeB n1 t1)"
      in ssubst)
     apply(rename_tac de1')(*strict*)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rename_tac de1')(*strict*)
    apply(rule_tac
      f="liftA"
      in arg_cong)
    apply(simp add: butn_def takeB_def)
   apply(rename_tac de1')(*strict*)
   apply(case_tac e)
    apply(rename_tac de1' a)(*strict*)
    apply(rule_tac
      t="e"
      and s="teA a"
      in ssubst)
     apply(rename_tac de1' a)(*strict*)
     apply(force)
    apply(rename_tac de1' a)(*strict*)
    apply(rule_tac
      t="maxTermPrefix (teA a # liftA t1)"
      and s="[]"
      in ssubst)
     apply(rename_tac de1' a)(*strict*)
     apply(rule maxTermPrefix_terminal_front)
    apply(rename_tac de1' a)(*strict*)
    apply(force)
   apply(rename_tac de1' ba)(*strict*)
   apply(rule_tac
      t="e"
      and s="teB ba"
      in ssubst)
    apply(rename_tac de1' ba)(*strict*)
    apply(force)
   apply(rename_tac de1' ba)(*strict*)
   apply(rule_tac
      t="maxTermPrefix (teB ba # liftA t1)"
      and s="[ba]"
      in ssubst)
    apply(rename_tac de1' ba)(*strict*)
    apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
   apply(rename_tac de1' ba)(*strict*)
   apply(case_tac "\<alpha>e@\<alpha>=[] \<and> b=ba")
    apply(rename_tac de1' ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1')(*strict*)
    apply(case_tac \<pi>e)
     apply(rename_tac de1')(*strict*)
     apply(clarsimp)
     apply(simp add: cfgLM.trans_der_def)
     apply(clarsimp)
    apply(rename_tac de1' a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac de1' a list)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and d="de"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
       apply(rename_tac de1' a list)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac de1' a list)(*strict*)
      apply(force)
     apply(rename_tac de1' a list)(*strict*)
     apply(force)
    apply(rename_tac de1' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' a list e ci')(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac de1' a list e ci' l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac de1' a list e ci' l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' a list e ci' l r aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' ba c)(*strict*)
   apply(case_tac \<alpha>e)
    apply(rename_tac de1' ba c)(*strict*)
    apply(clarsimp)
    apply(case_tac \<alpha>)
     apply(rename_tac de1' ba c)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' ba c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' ba c a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac de1')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac de1')(*strict*)
   prefer 2
   apply(unfold cfgLMMIP_def)
   apply(erule conjE)+
   apply(fold cfgLMMIP_def)
   apply(rule_tac
      de="de"
      and d="d2'"
      in cfgLM_trans_der_biextend_with_lastProducesX)
      apply(rename_tac de1')(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac de1')(*strict*)
     apply(force)
    apply(rename_tac de1')(*strict*)
    apply(force)
   apply(rename_tac de1')(*strict*)
   apply(simp add: lastProducesX_def)
   apply(thin_tac "cfgLMMIyX G d1' (liftA (butn t1 n1)) \<pi>1'")
   apply(thin_tac "cfgLMMPX G d1' (liftA (butn t1 n1)) \<pi>1' (liftB (\<alpha> @ [b])) (liftA tn1)")
   apply(simp add: cfgLMMPX_def)
   apply(clarsimp)
   apply(rename_tac de1' i)(*strict*)
   apply(erule_tac
      x="take i \<pi>2'"
      in allE)
   apply(simp add: strict_prefix_def)
   apply(erule impE)
    apply(rename_tac de1' i)(*strict*)
    apply(rule_tac
      x="drop i \<pi>2'"
      in exI)
    apply(force)
   apply(rename_tac de1' i)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac de1' i)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac de1' i ea eaa eb ec ed ee ef)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      g="d2'"
      and n="i"
      and m="length(\<pi>2')"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac de1' i ea eaa eb ec ed ee ef)(*strict*)
      apply(force)
     apply(rename_tac de1' i ea eaa eb ec ed ee ef)(*strict*)
     apply(force)
    apply(rename_tac de1' i ea eaa eb ec ed ee ef)(*strict*)
    apply(force)
   apply(rename_tac de1' i)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' i ea c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac de1' i ea c cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' i ea cfg_confa)(*strict*)
   apply(rename_tac wx)
   apply(rename_tac de1' i ea wx)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac de1' i ea c)(*strict*)
   apply(erule_tac
      x="d2'"
      in allE)
   apply(erule_tac
      x="c"
      in allE)
   apply(subgoal_tac "cfgLM.trans_der G d2' \<lparr>cfg_conf = liftA (butn t2 n2)\<rparr> (take i \<pi>2') \<lparr>cfg_conf = liftB (\<alpha> @ [b]) @ c\<rparr>")
    apply(rename_tac de1' i ea c)(*strict*)
    apply(force)
   apply(rename_tac de1' i ea c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac de1' i ea c)(*strict*)
    prefer 2
    apply(rule_tac
      n="i"
      and d="d2'"
      in cfgLM.trans_der_crop)
        apply(rename_tac de1' i ea c)(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac de1' i ea c)(*strict*)
       apply(force)
      apply(rename_tac de1' i ea c)(*strict*)
      apply(force)
     apply(rename_tac de1' i ea c)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac de1' i ea c)(*strict*)
    apply(force)
   apply(rename_tac de1' i ea c)(*strict*)
   apply(force)
  apply(rename_tac de1')(*strict*)
  apply(erule exE)+
  apply(rename_tac de1' d)(*strict*)
  apply(rename_tac de2')
  apply(rename_tac de1' de2')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac de1' de2')(*strict*)
   prefer 2
   apply(rule_tac
      w="X"
      and ?v1.0="[]"
      and ?v4.0="liftA(takeB n2 t2)"
      and ?d1.0="d2"
      and ?d2.0="de2'" for X
      in cfgLM_trans_der_concat_extend_with_lastProducesX)
       apply(rename_tac de1' de2')(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac de1' de2')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac de1' de2')(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="e # liftA (butn t2 n2) @ liftA (takeB n2 t2)"
      and s="e # liftA t2"
      in ssubst)
      apply(rename_tac de1' de2')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac de1' de2')(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="liftA (butn t2 n2) @ liftA (takeB n2 t2)"
      and s="liftA (butn t2 n2 @ takeB n2 t2)"
      in ssubst)
      apply(rename_tac de1' de2')(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
     apply(rename_tac de1' de2')(*strict*)
     apply(rule_tac
      f="liftA"
      in arg_cong)
     apply(simp add: butn_def takeB_def)
    apply(rename_tac de1' de2')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac de1' de2')(*strict*)
   apply(simp add: prefix_def)
   apply(rule_tac
      t="e # liftA (butn t2 n2) @ liftA (takeB n2 t2)"
      and s="e # liftA t2"
      in ssubst)
    apply(rename_tac de1' de2')(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="liftA (butn t2 n2) @ liftA (takeB n2 t2)"
      and s="liftA (butn t2 n2 @ takeB n2 t2)"
      in ssubst)
     apply(rename_tac de1' de2')(*strict*)
     apply(simp (no_asm) add: liftA_commutes_over_concat)
    apply(rename_tac de1' de2')(*strict*)
    apply(rule_tac
      f="liftA"
      in arg_cong)
    apply(simp add: butn_def takeB_def)
   apply(rename_tac de1' de2')(*strict*)
   apply(case_tac e)
    apply(rename_tac de1' de2' a)(*strict*)
    apply(rule_tac
      t="e"
      and s="teA a"
      in ssubst)
     apply(rename_tac de1' de2' a)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' a)(*strict*)
    apply(rule_tac
      t="maxTermPrefix (teA a # liftA t2)"
      and s="[]"
      in ssubst)
     apply(rename_tac de1' de2' a)(*strict*)
     apply(rule maxTermPrefix_terminal_front)
    apply(rename_tac de1' de2' a)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' ba)(*strict*)
   apply(rule_tac
      t="e"
      and s="teB ba"
      in ssubst)
    apply(rename_tac de1' de2' ba)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' ba)(*strict*)
   apply(rule_tac
      t="maxTermPrefix (teB ba # liftA t2)"
      and s="[ba]"
      in ssubst)
    apply(rename_tac de1' de2' ba)(*strict*)
    apply (metis maxTermPrefix_pull_out maxTermPrefix_liftA)
   apply(rename_tac de1' de2' ba)(*strict*)
   apply(case_tac "\<alpha>e@\<alpha>=[] \<and> b=ba")
    apply(rename_tac de1' de2' ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2')(*strict*)
    apply(case_tac \<pi>e)
     apply(rename_tac de1' de2')(*strict*)
     apply(clarsimp)
     apply(simp add: cfgLM.trans_der_def)
     apply(clarsimp)
    apply(rename_tac de1' de2' a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac de1' de2' a list)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and d="de"
      and i="0"
      and kleene_starT="True"
      and END="False"
      in cfgLM.trans_der_step_detail)
       apply(rename_tac de1' de2' a list)(*strict*)
       apply(simp add: split_TSstructure_def)
      apply(rename_tac de1' de2' a list)(*strict*)
      apply(force)
     apply(rename_tac de1' de2' a list)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' a list e ci')(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' a list e ci' l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac de1' de2' a list e ci' l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' a list e ci' l r aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' de2' ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' de2' ba c)(*strict*)
   apply(case_tac \<alpha>e)
    apply(rename_tac de1' de2' ba c)(*strict*)
    apply(clarsimp)
    apply(case_tac \<alpha>)
     apply(rename_tac de1' de2' ba c)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' ba c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' de2' ba c a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac de1' de2')(*strict*)
  apply(subgoal_tac "length (\<pi>1@\<pi>e@\<pi>1') = length(\<pi>2@\<pi>e@\<pi>2')")
   apply(rename_tac de1' de2')(*strict*)
   prefer 2
   apply(rule_tac
      ?t2.0="tn2@ (takeB n2 t2)"
      and ?A1.0="A1"
      and ?t1.0="tn1@ (takeB n1 t1)"
      and \<alpha>="\<alpha>e@\<alpha>"
      and b="b"
      and ?d1.0="derivation_append d1 (derivation_map de1' (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (takeB n1 t1)\<rparr>)) (length \<pi>1)"
      and ?d2.0="derivation_append d2 (derivation_map de2' (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (takeB n2 t2)\<rparr>)) (length \<pi>2)"
      in AX_equal_length_production_of_multiple_terminal)
         apply(rename_tac de1' de2')(*strict*)
         apply(force)
        apply(rename_tac de1' de2')(*strict*)
        apply(force)
       apply(rename_tac de1' de2')(*strict*)
       apply(simp (no_asm) add: liftA_commutes_over_concat)
       apply(force)
      apply(rename_tac de1' de2')(*strict*)
      apply(simp (no_asm) add: liftA_commutes_over_concat)
      apply(force)
     apply(rename_tac de1' de2')(*strict*)
     apply(force)
    apply(rename_tac de1' de2')(*strict*)
    apply(force)
   apply(rename_tac de1' de2')(*strict*)
   apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(clarsimp)
  apply(rename_tac de1' de2')(*strict*)
  apply(subgoal_tac "map (prod_to_edge G') (\<pi>1@\<pi>e@\<pi>1') = map (prod_to_edge G') (\<pi>2@\<pi>e@\<pi>2')")
   apply(rename_tac de1' de2')(*strict*)
   prefer 2
   apply(simp only: cfgLMMIP_def)
   apply(erule conjE)+
   apply(rule_tac
      ?t2.0="tn2@ (takeB n2 t2)"
      and ?A1.0="A1"
      and ?t1.0="tn1@ (takeB n1 t1)"
      and \<alpha>="\<alpha>e@\<alpha>"
      and b="b"
      and ?d1.0="derivation_append d1 (derivation_map de1' (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (takeB n1 t1)\<rparr>)) (length \<pi>1)"
      and ?d2.0="derivation_append d2 (derivation_map de2' (\<lambda>v. \<lparr>cfg_conf = liftB [] @ cfg_conf v @ liftA (takeB n2 t2)\<rparr>)) (length \<pi>2)"
      in prod_to_edge_equality_for_terminal_generation_multiple_terminals)
          apply(rename_tac de1' de2')(*strict*)
          apply(force)
         apply(rename_tac de1' de2')(*strict*)
         apply(force)
        apply(rename_tac de1' de2')(*strict*)
        apply(simp (no_asm) add: liftA_commutes_over_concat)
        apply(force)
       apply(rename_tac de1' de2')(*strict*)
       apply(simp (no_asm) add: liftA_commutes_over_concat)
      apply(rename_tac de1' de2')(*strict*)
      apply(force)
     apply(rename_tac de1' de2')(*strict*)
     apply(force)
    apply(rename_tac de1' de2')(*strict*)
    apply(force)
   apply(rename_tac de1' de2')(*strict*)
   apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(clarsimp)
  apply(rename_tac de1' de2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G de1' \<lparr>cfg_conf = e # liftA (butn t1 n1)\<rparr> (\<pi>e @ \<pi>1') \<lparr>cfg_conf = liftB (\<alpha>e @ \<alpha> @ [b]) @ liftA tn1\<rparr>")
  apply(rename_tac de1' de2')(*strict*)
  apply(thin_tac "lastProducesX de1' (\<pi>e @ \<pi>1') (\<alpha>e @ \<alpha> @ [b])")
  apply(thin_tac "cfgLM.trans_der G de2' \<lparr>cfg_conf = e # liftA (butn t2 n2)\<rparr> (\<pi>e @ \<pi>2') \<lparr>cfg_conf = liftB (\<alpha>e @ \<alpha> @ [b]) @ liftA tn2\<rparr>")
  apply(rename_tac de1' de2')(*strict*)
  apply(thin_tac "lastProducesX de2' (\<pi>e @ \<pi>2') (\<alpha>e @ \<alpha> @ [b])")
  apply(subgoal_tac "only_l3_nonterminals (butlast t1)")
   apply(rename_tac de1' de2')(*strict*)
   prefer 2
   apply(case_tac A1)
    apply(rename_tac de1' de2' q ba)(*strict*)
    prefer 2
    apply(rename_tac de1' de2' q1 ba q2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac de1' de2' q1 ba q2)(*strict*)
     prefer 2
     apply(rule_tac
      \<pi>="\<pi>1"
      and c'="\<lparr>cfg_conf = e # liftA t1\<rparr>"
      and d="d1"
      in only_l3_nonterminals_reachable)
          apply(rename_tac de1' de2' q1 ba q2)(*strict*)
          apply(simp add: F2LR1inputx_def)
          apply(force)
         apply(rename_tac de1' de2' q1 ba q2)(*strict*)
         apply(simp add: F2LR1inputx_def)
         apply(force)
        apply(rename_tac de1' de2' q1 ba q2)(*strict*)
        apply(simp add: F2LR1inputx_def)
       apply(rename_tac de1' de2' q1 ba q2)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(simp add: F2LR1inputx_def)
      apply(rename_tac de1' de2' q1 ba q2)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac de1' de2' q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA)(*strict*)
    apply(case_tac xA)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q baa)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(subgoal_tac "t1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(erule disjE)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa a')(*strict*)
    apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
    apply(force)
   apply(rename_tac de1' de2' q ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac de1' de2' q ba)(*strict*)
    prefer 2
    apply(rule_tac
      ?w2.0="case e of teA A \<Rightarrow> [] | teB b \<Rightarrow> [b]"
      and ?v2.0="(case e of teA A \<Rightarrow> [A] | teB b \<Rightarrow> [])@t1"
      and d="d1"
      and ?w1.0="[]"
      and ?v1.0="[(cons_l2 q ba)]"
      in F_SDPDA_TO_CFG_STD__l3_l2_separation_ALT_preserved)
       apply(rename_tac de1' de2' q ba)(*strict*)
       apply(force)
      apply(rename_tac de1' de2' q ba)(*strict*)
      apply(force)
     apply(rename_tac de1' de2' q ba)(*strict*)
     apply(case_tac e)
      apply(rename_tac de1' de2' q ba a)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac de1' de2' q ba baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba)(*strict*)
    apply(simp add: l3_l2_separation_ALT_def)
   apply(rename_tac de1' de2' q ba)(*strict*)
   apply(case_tac e)
    apply(rename_tac de1' de2' q ba a)(*strict*)
    apply(clarsimp)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(subgoal_tac "t1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(erule disjE)
     apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA a')(*strict*)
    apply(simp add: l3_l2_separation_ALT_def)
    apply(clarsimp)
    apply(case_tac a')
     apply(rename_tac de1' de2' q ba a w1 w2 xA a' qa baa)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q ba a w1 w2 xA a' q1 baa q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 xA a' qa baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa)(*strict*)
    apply(case_tac xA)
     apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa qb bb)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa q1 bb q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa qb bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(erule_tac
      x="cons_l2 qb bb"
      in ballE)
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(subgoal_tac "cons_l2 qb bb \<in> set (butlast (w1 @ cons_l2 qb bb # w2 @ [cons_l2 qa baa]))")
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(rule_tac
      t="butlast (w1 @ cons_l2 qb bb # w2 @ [cons_l2 qa baa])"
      in ssubst)
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa)(*strict*)
   apply(clarsimp)
   apply(simp add: only_l3_nonterminals_def l3_l2_separation_ALT_def)
   apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 xA)(*strict*)
   apply(case_tac xA)
    apply(rename_tac de1' de2' q ba baa w1 w2 xA qa bb)(*strict*)
    prefer 2
    apply(rename_tac de1' de2' q ba baa w1 w2 xA q1 bb q2)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa w1 w2 xA qa bb)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
   apply(subgoal_tac "t1=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
   apply(erule_tac
      P="t1 = []"
      in disjE)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
   apply(subgoal_tac "Ball (set (butlast ((w1 @ cons_l2 qa bb # w2) @ [a']))) (case_DT_l2_l3_nonterminals (\<lambda>q A. False) (\<lambda>q1 b q2. True)) \<and> (case last ((w1 @ cons_l2 qa bb # w2) @ [a']) of cons_l2 qa b \<Rightarrow> True | cons_l3 q A q' \<Rightarrow> False)")
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
    prefer 2
    apply(case_tac "w1 @ cons_l2 qa bb # w2 @ [a']")
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
   apply(clarsimp)
   apply(case_tac a')
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' qb bc)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(erule_tac
      x="cons_l2 qa bb"
      in ballE)
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(subgoal_tac "cons_l2 qa bb \<in> set (butlast (w1 @ cons_l2 qa bb # w2 @ [cons_l2 qb bc]))")
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(rule_tac
      t="butlast (w1 @ cons_l2 qa bb # w2 @ [cons_l2 qb bc])"
      in ssubst)
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' q1 bc q2)(*strict*)
   apply(clarsimp)
  apply(rename_tac de1' de2')(*strict*)
  apply(subgoal_tac "only_l3_nonterminals (butlast t2)")
   apply(rename_tac de1' de2')(*strict*)
   prefer 2
   apply(case_tac A2)
    apply(rename_tac de1' de2' q ba)(*strict*)
    prefer 2
    apply(rename_tac de1' de2' q1 ba q2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac de1' de2' q1 ba q2)(*strict*)
     prefer 2
     apply(rule_tac
      \<pi>="\<pi>2"
      and c'="\<lparr>cfg_conf = e # liftA t2\<rparr>"
      and d="d2"
      in only_l3_nonterminals_reachable)
          apply(rename_tac de1' de2' q1 ba q2)(*strict*)
          apply(simp add: F2LR1inputx_def)
          apply(force)
         apply(rename_tac de1' de2' q1 ba q2)(*strict*)
         apply(simp add: F2LR1inputx_def)
         apply(force)
        apply(rename_tac de1' de2' q1 ba q2)(*strict*)
        apply(simp add: F2LR1inputx_def)
       apply(rename_tac de1' de2' q1 ba q2)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(simp add: F2LR1inputx_def)
      apply(rename_tac de1' de2' q1 ba q2)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac de1' de2' q1 ba q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q1 ba q2)(*strict*)
    apply(clarsimp)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA)(*strict*)
    apply(case_tac xA)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q baa)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q1a baa q2a)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 xA q baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(subgoal_tac "t2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(erule disjE)
     apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q1 ba q2 w1 w2 q baa a')(*strict*)
    apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
    apply(force)
   apply(rename_tac de1' de2' q ba)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac de1' de2' q ba)(*strict*)
    prefer 2
    apply(rule_tac
      ?w2.0="case e of teA A \<Rightarrow> [] | teB b \<Rightarrow> [b]"
      and ?v2.0="(case e of teA A \<Rightarrow> [A] | teB b \<Rightarrow> [])@t2"
      and d="d2"
      and ?w1.0="[]"
      and ?v1.0="[(cons_l2 q ba)]"
      in F_SDPDA_TO_CFG_STD__l3_l2_separation_ALT_preserved)
       apply(rename_tac de1' de2' q ba)(*strict*)
       apply(force)
      apply(rename_tac de1' de2' q ba)(*strict*)
      apply(force)
     apply(rename_tac de1' de2' q ba)(*strict*)
     apply(case_tac e)
      apply(rename_tac de1' de2' q ba a)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac de1' de2' q ba baa)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba)(*strict*)
    apply(simp add: l3_l2_separation_ALT_def)
   apply(rename_tac de1' de2' q ba)(*strict*)
   apply(case_tac e)
    apply(rename_tac de1' de2' q ba a)(*strict*)
    apply(clarsimp)
    apply(simp add: only_l3_nonterminals_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(subgoal_tac "t2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(erule disjE)
     apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA a')(*strict*)
    apply(simp add: l3_l2_separation_ALT_def)
    apply(clarsimp)
    apply(case_tac a')
     apply(rename_tac de1' de2' q ba a w1 w2 xA a' qa baa)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q ba a w1 w2 xA a' q1 baa q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 xA a' qa baa)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa)(*strict*)
    apply(case_tac xA)
     apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa qb bb)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa q1 bb q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 xA qa baa qb bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(erule_tac
      x="cons_l2 qb bb"
      in ballE)
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(subgoal_tac "cons_l2 qb bb \<in> set (butlast (w1 @ cons_l2 qb bb # w2 @ [cons_l2 qa baa]))")
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(rule_tac
      t="butlast (w1 @ cons_l2 qb bb # w2 @ [cons_l2 qa baa])"
      in ssubst)
     apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac de1' de2' q ba a w1 w2 qa baa qb bb)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac de1' de2' q ba baa)(*strict*)
    apply(simp add: only_l3_nonterminals_def l3_l2_separation_ALT_def)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 xA)(*strict*)
    apply(case_tac xA)
     apply(rename_tac de1' de2' q ba baa w1 w2 xA qa bb)(*strict*)
     prefer 2
     apply(rename_tac de1' de2' q ba baa w1 w2 xA q1 bb q2)(*strict*)
     apply(force)
    apply(rename_tac de1' de2' q ba baa w1 w2 xA qa bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
    apply(subgoal_tac "t2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
    apply(erule disjE)
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb)(*strict*)
    apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
    apply(subgoal_tac "Ball (set (butlast ((w1 @ cons_l2 qa bb # w2) @ [a']))) (case_DT_l2_l3_nonterminals (\<lambda>q A. False) (\<lambda>q1 b q2. True)) \<and> (case last ((w1 @ cons_l2 qa bb # w2) @ [a']) of cons_l2 qa b \<Rightarrow> True | cons_l3 q A q' \<Rightarrow> False)")
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
     prefer 2
     apply(case_tac "w1 @ cons_l2 qa bb # w2 @ [a']")
      apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
      apply(force)
     apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a')(*strict*)
  apply(clarsimp)
  apply(case_tac a')
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' qb bc)(*strict*)
   apply(clarsimp)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
   apply(erule_tac
    x="cons_l2 qa bb"
    in ballE)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
   apply(subgoal_tac "cons_l2 qa bb \<in> set (butlast (w1 @ cons_l2 qa bb # w2 @ [cons_l2 qb bc]))")
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(force)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
   apply(rule_tac
    t="butlast (w1 @ cons_l2 qa bb # w2 @ [cons_l2 qb bc])"
    in ssubst)
    apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac de1' de2' q ba baa w1 w2 qa bb qb bc)(*strict*)
   apply(force)
  apply(rename_tac de1' de2' q ba baa w1 w2 qa bb a' q1 bc q2)(*strict*)
  apply(clarsimp)
  apply(rename_tac de1' de2' q ba baa)(*strict*)
  apply(simp add: only_l3_nonterminals_def)
  apply(rename_tac de1' de2')(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac de1' de2')(*strict*)
  prefer 2
  apply(rule_tac
    ?d1'="d1'"
    and ?d2'="d2'"
    in compatible_cfgLMMIP_from_compatible_source)
       apply(rename_tac de1' de2')(*strict*)
       apply(force)
      apply(rename_tac de1' de2')(*strict*)
      apply(force)
     apply(rename_tac de1' de2')(*strict*)
     apply(force)
    apply(rename_tac de1' de2')(*strict*)
    apply(force)
   apply(rename_tac de1' de2')(*strict*)
   apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(rule only_l3_nonterminals_butlast_butn)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(rule only_l3_nonterminals_butlast_butn)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(simp add: drop_and_crop_def butn_def)
  apply(rule_tac
    t="min (length t1) (length t1 - n1)"
    and s="length t1 - n1"
    in ssubst)
  apply(rename_tac de1' de2')(*strict*)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(rule_tac
    t="min (length t1 - n1) (length t1 - n1)"
    and s="length t1 - n1"
    in ssubst)
  apply(rename_tac de1' de2')(*strict*)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(rule_tac
    t="min (length t2) (length t2 - n2)"
    and s="length t2 - n2"
    in ssubst)
  apply(rename_tac de1' de2')(*strict*)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(rule_tac
    t="min (length t2 - n2) (length t2 - n2)"
    and s="length t2 - n2"
    in ssubst)
  apply(rename_tac de1' de2')(*strict*)
  apply(force)
  apply(rename_tac de1' de2')(*strict*)
  apply(force)
  done

hide_fact AX_equal_length_production_of_multiple_terminal
hide_fact AX_equal_length_production_of_multiple_terminal_hlp1
hide_fact cfgLM_trans_der_biextend_with_lastProducesX
hide_fact cfgLM_trans_der_concat_extend_with_lastProducesX
hide_fact no_shorter_production_of_terminal_or_nonterminal
hide_fact prod_to_edge_equality_for_terminal_generation
hide_fact prod_to_edge_equality_for_terminal_generation_multiple_terminals
hide_fact state_stack_compatible_nonterminals_generate_nonterminal_with_unique_length
hide_fact state_stack_compatible_nonterminals_generate_terminal_with_unique_length
  (* important AX_equal_length_production_of_terminal_or_nonterminal *)
  (* important compatibel_derivation_compatible_first_nonterminal_at_end *)
  (* important equal_split_prefix_hlp2_withMIP_simplified *)
  (* important lastProduces_intro *)
  (* important prod_to_edge_equality_for_terminal_and_nonterminal_generation *)

end

