section {*operations\_on\_discrete\_event\_systems*}
theory
  operations_on_discrete_event_systems

imports
  fixed_point_iterator

begin

definition Enforce_Valid_DES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Valid_DES C \<equiv>
  let Aum = Sup{A. A \<subseteq> des_langUM C \<and> A = prefix_closure A}
  in DES Aum (Aum \<inter> des_langM C)"

lemma Enforce_Valid_DES_makes_DES: "
  IsDES (Enforce_Valid_DES D)"
  apply(simp add: Enforce_Valid_DES_def IsDES_def)
  apply(case_tac D)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(rename_tac LUM LM)
  apply(rename_tac LUM LM)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac LUM LM)(*strict*)
   apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def)
  apply(rename_tac LUM LM)(*strict*)
  apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def)
  apply(rename_tac LUM)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac LUM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac LUM x xa c)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(force)
  apply(rename_tac LUM)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM x X)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule_tac
      x="x"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="X"
      in exI)
  apply(force)
  done

lemma Enforce_Valid_DES_is_decreasing: "
  Enforce_Valid_DES D \<le> D"
  apply(simp add: Enforce_Valid_DES_def)
  apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def)
  apply(clarsimp)
  apply(rename_tac x X)(*strict*)
  apply(case_tac D)
  apply(rename_tac x X fun1 fun2)(*strict*)
  apply(rename_tac LUM LM)
  apply(rename_tac x X LUM LM)(*strict*)
  apply(clarsimp)
  apply(rename_tac x X LUM)(*strict*)
  apply(force)
  done

lemma Enforce_Valid_DES_is_supremal: "
  Enforce_Valid_DES D = Sup{C. IsDES C \<and> C \<le> D}"
  apply(rule order_antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule Enforce_Valid_DES_makes_DES)
   apply(rule Enforce_Valid_DES_is_decreasing)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: Enforce_Valid_DES_def)
  apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def)
  apply(clarsimp)
  apply(case_tac x)
  apply(rename_tac x fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac x LUM1 LM1)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1)(*strict*)
  apply(case_tac D)
  apply(rename_tac LUM1 LM1 fun1 fun2)(*strict*)
  apply(rename_tac LUM2 LM2)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(simp add: IsDES_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
   prefer 2
   apply(subgoal_tac "LM1 \<subseteq> LUM1")
    apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
    apply(rule_tac
      B="LUM1"
      in subset_trans)
     apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
     apply(blast)
    apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(rule Sup_upper)
  apply(clarsimp)
  done

corollary Enforce_Valid_DES_Sound: "
  SAT = {A. A \<le> C \<and> IsDES A}
  \<Longrightarrow> RES = Enforce_Valid_DES C
  \<Longrightarrow> RES = Sup SAT \<and> RES \<in> SAT"
  apply (metis (full_types) Collect_conj_eq Enforce_Valid_DES_is_decreasing Enforce_Valid_DES_is_supremal Enforce_Valid_DES_makes_DES Int_Collect inf.commute mem_Collect_eq)
  done

lemma Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES_hlp1: "
  \<Union>{A. A \<subseteq> LUM \<and> A = prefix_closure A} = LUM
  \<Longrightarrow> prefix_closure LUM = LUM"
  apply(rule_tac
      t="LUM"
      and s="\<Union>{A. A \<subseteq> LUM \<and> A = prefix_closure A}"
      in ssubst)
   apply(force)
  apply(rule sym)
  apply(rule preservePrec)
  apply(rename_tac B)(*strict*)
  apply(force)
  done

lemma Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES: "
  Characteristic_Fixed_Point_Iterator Enforce_Valid_DES UNIVmap IsDES IsDES"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule Enforce_Valid_DES_is_decreasing)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X LUM LM)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(simp add: IsDES_def Enforce_Valid_DES_def Let_def des_langUM_def des_langM_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac LUM LM)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac LUM LM)(*strict*)
      apply(clarsimp)
      apply(rename_tac LUM LM x X)(*strict*)
      apply(force)
     apply(rename_tac LUM LM)(*strict*)
     apply(clarsimp)
     apply(rename_tac LUM LM x)(*strict*)
     apply(force)
    apply(rename_tac LUM LM)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac LUM LM)(*strict*)
     apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM x)(*strict*)
    apply(rule_tac
      x="LUM"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      A="LM"
      in set_mp)
     apply(rename_tac LUM LM x)(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
    apply(rename_tac LUM LM x)(*strict*)
    apply(force)
   apply(rename_tac X LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM)(*strict*)
   apply(simp add: IsDES_def Enforce_Valid_DES_def Let_def des_langUM_def des_langM_def)
   apply(clarsimp)
   apply(subgoal_tac "prefix_closure LUM = LUM")
    apply(rename_tac LUM LM)(*strict*)
    apply(rule conjI)
     apply(rename_tac LUM LM)(*strict*)
     apply(clarsimp)
     apply(rename_tac LUM LM x)(*strict*)
     apply(rule_tac
      A="LUM"
      in set_mp)
      apply(rename_tac LUM LM x)(*strict*)
      apply(force)
     apply(rename_tac LUM LM x)(*strict*)
     apply(rule_tac
      A="LM"
      in set_mp)
      apply(rename_tac LUM LM x)(*strict*)
      apply(force)
     apply(rename_tac LUM LM x)(*strict*)
     apply(force)
    apply(rename_tac LUM LM)(*strict*)
    apply(force)
   apply(rename_tac LUM LM)(*strict*)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES_hlp1)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule Enforce_Valid_DES_makes_DES)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(case_tac X)
  apply(rename_tac X Y fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac X Y LUM1 LM1)(*strict*)
  apply(case_tac Y)
  apply(rename_tac X Y LUM1 LM1 fun1 fun2)(*strict*)
  apply(rename_tac LUM2 LM2)
  apply(rename_tac X Y LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(simp add: less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Enforce_Valid_DES_def Let_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 x X)(*strict*)
   apply(rule_tac
      x="X"
      in exI)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 x X xa)(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 x X)(*strict*)
   apply(rule_tac
      x="X"
      in exI)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 x X xa)(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2 x X)(*strict*)
  apply(force)
  done

theorem Fixed_Point_Iterator_Enforce_Valid_DES: "
  Fixed_Point_Iterator Enforce_Valid_DES top (Collect IsDES) (Collect IsDES)"
  apply (metis Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1 Collect_cong UNIVmap_def iso_tuple_UNIV_I top_empty_eq top_set_def)
  done

definition Enforce_Specification_Satisfaction :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Specification_Satisfaction S C \<equiv>
  inf S C"

corollary Enforce_Specification_Satisfaction_Sound: "
  IsDES S
  \<Longrightarrow> IsDES C
  \<Longrightarrow> SAT = {A. A \<le> C \<and> A \<le> S \<and> IsDES A}
  \<Longrightarrow> RES = Enforce_Specification_Satisfaction S C
  \<Longrightarrow> RES = Sup SAT \<and> RES \<in> SAT"
  apply(rule propSym)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(simp add: Enforce_Specification_Satisfaction_def)
   apply(case_tac C)
   apply(rename_tac set1 set2)(*strict*)
   apply(rename_tac Cum Cm)
   apply(rename_tac Cum Cm)(*strict*)
   apply(case_tac S)
   apply(rename_tac Cum Cm set1 set2)(*strict*)
   apply(rename_tac Sum Sm)
   apply(rename_tac Cum Cm Sum Sm)(*strict*)
   apply(simp add: Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
   apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  apply(rule antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(case_tac C)
  apply(rename_tac x set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac x Cum Cm)(*strict*)
  apply(case_tac S)
  apply(rename_tac x Cum Cm set1 set2)(*strict*)
  apply(rename_tac Sum Sm)
  apply(rename_tac x Cum Cm Sum Sm)(*strict*)
  apply(simp add: Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
  apply(case_tac x)
  apply(rename_tac x Cum Cm Sum Sm set1 set2)(*strict*)
  apply(rename_tac Xum Xm)
  apply(rename_tac x Cum Cm Sum Sm Xum Xm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Cum Cm Sum Sm Xum Xm)(*strict*)
  apply(simp add: Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def inf_DES_ext_def infDES_def)
  done

lemma Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction: "
  IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (Enforce_Specification_Satisfaction S) IsDES (predicate_AND IsDES (DES_specification_satisfied S)) (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def inf_DES_ext_def infDES_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: DES_specification_satisfied_def Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def inf_DES_ext_def infDES_def)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac S)
    apply(rename_tac LUM LM Sum Sm)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def DES_specification_satisfied_def Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def inf_DES_ext_def infDES_def)
   apply(clarsimp)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM)(*strict*)
   apply(case_tac S)
   apply(rename_tac LUM LM XSUM XSPM)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: DES_specification_satisfied_def)
   apply(rule context_conjI)
    apply(rename_tac X)(*strict*)
    apply(simp add: DES_nonblockingness_def DES_specification_satisfied_def Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def inf_DES_ext_def infDES_def)
    apply(clarsimp)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac S)
    apply(rename_tac LUM LM XSUM XSPM)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac LUM LM XSUM XSPM)(*strict*)
     apply(rule_tac
      t="XSUM"
      and s="prefix_closure XSUM"
      in ssubst)
      apply(rename_tac LUM LM XSUM XSPM)(*strict*)
      apply(force)
     apply(rename_tac LUM LM XSUM XSPM)(*strict*)
     apply(force)
    apply(rename_tac LUM LM XSUM XSPM)(*strict*)
    apply(rule conjI)
     apply(rename_tac LUM LM XSUM XSPM)(*strict*)
     apply(rule_tac
      t="LUM"
      and s="prefix_closure LUM"
      in ssubst)
      apply(rename_tac LUM LM XSUM XSPM)(*strict*)
      apply(force)
     apply(rename_tac LUM LM XSUM XSPM)(*strict*)
     apply(force)
    apply(rename_tac LUM LM XSUM XSPM)(*strict*)
    apply(rule prefix_closure_closed_sets_closed_under_intersection)
     apply(rename_tac LUM LM XSUM XSPM)(*strict*)
     apply(force)
    apply(rename_tac LUM LM XSUM XSPM)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(simp add: DES_nonblockingness_def DES_specification_satisfied_def Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def inf_DES_ext_def infDES_def)
  apply(simp add: DES_nonblockingness_def DES_specification_satisfied_def Enforce_Specification_Satisfaction_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def inf_DES_ext_def infDES_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(case_tac X)
  apply(rename_tac X Y fun1 fun2)(*strict*)
  apply(rename_tac LUM LM)
  apply(rename_tac X Y LUM LM)(*strict*)
  apply(clarsimp)
  apply(rename_tac Y LUM LM)(*strict*)
  apply(case_tac S)
  apply(rename_tac Y LUM LM fun1 fun2)(*strict*)
  apply(rename_tac XSUM XSPM)
  apply(rename_tac Y LUM LM XSUM XSPM)(*strict*)
  apply(clarsimp)
  apply(case_tac Y)
  apply(rename_tac Y LUM LM XSUM XSPM fun1 fun2)(*strict*)
  apply(rename_tac YUM YM)
  apply(rename_tac Y LUM LM XSUM XSPM YUM YM)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM LM XSUM XSPM YUM YM)(*strict*)
  apply(force)
  done

lemma Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3: "
  Set1 = Collect Prop1
  \<Longrightarrow> Set2 = Collect Prop2
  \<Longrightarrow> Set3 = Collect Prop3
  \<Longrightarrow> Fixed_Point_Iterator F Set1 Set2 Set3 = Characteristic_Fixed_Point_Iterator F Prop1 Prop2 Prop3"
  apply(clarsimp)
  apply (metis Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1)
  done

theorem Fixed_Point_Iterator_Enforce_Specification_Satisfaction: "
  IsDES S
  \<Longrightarrow> Fixed_Point_Iterator
  (Enforce_Specification_Satisfaction S)
  {C. IsDES C}
  {C. IsDES C \<and> DES_specification_satisfied S C}
  {C. IsDES C \<and> DES_specification_satisfied S C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule_tac
      S="S"
      in Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

definition Enforce_Nonblockingness_DES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Nonblockingness_DES C \<equiv>
  DES (prefix_closure (des_langM C)) (des_langM C)"

lemma Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES: "
  Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: Enforce_Nonblockingness_DES_def)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM)(*strict*)
   apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
   apply(rule_tac
      B="prefix_closure LUM"
      in subset_trans)
    apply(rename_tac LUM LM)(*strict*)
    apply(rule prefix_closure_preserves_subseteq)
    apply(force)
   apply(rename_tac LUM LM)(*strict*)
   apply(force)
  apply(rule conjI)
   defer
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac X)(*strict*)
    apply(simp add: DES_nonblockingness_def Enforce_Nonblockingness_DES_def IsDES_def)
    apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def nonblockingness_language_def)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM1 LM1)
    apply(rename_tac X LUM1 LM1)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1)(*strict*)
    apply(rule conjI)
     apply(rename_tac LUM1 LM1)(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
     apply(force)
    apply(rename_tac LUM1 LM1)(*strict*)
    apply(rule sym)
    apply(rule prefix_closure_idempotent)
   apply(simp add: DES_nonblockingness_def Enforce_Nonblockingness_DES_def IsDES_def)
   apply(clarsimp)
   apply(rename_tac X x)(*strict*)
   apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
   apply(case_tac X)
   apply(rename_tac X x set1 set2)(*strict*)
   apply(case_tac x)
   apply(rename_tac X x set1 set2 set1a set2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac set1 set2 set1a set2a xa)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def)
   apply(simp add: Enforce_Nonblockingness_DES_def)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(clarsimp)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(rename_tac LUM1 LM1)
   apply(rename_tac LUM1 LM1)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac LUM1 LM1)(*strict*)
    apply(rule_tac
      B="prefix_closure LUM1"
      in subset_trans)
     apply(rename_tac LUM1 LM1)(*strict*)
     apply(rule prefix_closure_preserves_subseteq)
     apply(simp add: IsDES_def)
    apply(rename_tac LUM1 LM1)(*strict*)
    apply(simp add: IsDES_def)
   apply(rename_tac LUM1 LM1)(*strict*)
   apply(simp add: IsDES_def)
   apply(rename_tac X)(*strict*)
   apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def nonblockingness_language_def)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(simp add: DES_nonblockingness_def)
  apply(simp add: Enforce_Nonblockingness_DES_def)
  apply(case_tac X)
  apply(rename_tac X fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac X LUM1 LM1)(*strict*)
  apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def nonblockingness_language_def)
  done

theorem Fixed_Point_Iterator_Enforce_Nonblockingness_DES: "
  Fixed_Point_Iterator Enforce_Nonblockingness_DES
  {C. IsDES C}
  {C. IsDES C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_nonblockingness C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Enforce_Nonblockingness_DES_term: "
  DES_nonblockingness x
  \<Longrightarrow> IsDES x
  \<Longrightarrow> x=Enforce_Nonblockingness_DES x"
  apply(simp add: Enforce_Nonblockingness_DES_def DES_nonblockingness_def IsDES_def)
  apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def nonblockingness_language_def)
  apply(case_tac x)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac fun1 fun2 x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac fun1 fun2 x c)(*strict*)
  apply(force)
  done

lemma Enforce_Nonblockingness_DES_mono: "
  x\<le>y
  \<Longrightarrow> Enforce_Nonblockingness_DES x\<le>Enforce_Nonblockingness_DES y"
  apply(simp add: Enforce_Nonblockingness_DES_def)
  apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def)
  apply(case_tac x)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac y)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac fun1 fun2 fun1a fun2a x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(force)
  done

corollary Enforce_Nonblockingness_DES_Sound: "
  IsDES C
  \<Longrightarrow> SAT = {A. A \<le> C \<and> IsDES A \<and> DES_nonblockingness A}
  \<Longrightarrow> RES = Enforce_Nonblockingness_DES C
  \<Longrightarrow> RES = Sup SAT \<and> RES \<in> SAT"
  apply(rule propSym)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def Enforce_Nonblockingness_DES_def nonblockingness_language_def)
   apply(case_tac C)
   apply(rename_tac set1 set2)(*strict*)
   apply(rename_tac Cum Cm)
   apply(rename_tac Cum Cm)(*strict*)
   apply(clarsimp)
   apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def)
   apply (metis prefix_closure_idempotent prefix_closure_preserves_subseteq prefix_closure_subset)
  apply(rule antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(case_tac C)
  apply(rename_tac x set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac x Cum Cm)(*strict*)
  apply(clarsimp)
  apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def DES_nonblockingness_def Enforce_Nonblockingness_DES_def nonblockingness_language_def)
  apply(case_tac x)
  apply(rename_tac x Cum Cm set1 set2)(*strict*)
  apply(rename_tac Xum Xm)
  apply(rename_tac x Cum Cm Xum Xm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Cum Cm Xum Xm xa)(*strict*)
  apply (metis contra_subsetD prefix_closure_preserves_subseteq)
  done

definition Enforce_Star_Controllable_Subset :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Star_Controllable_Subset \<Sigma>UC Pum C \<equiv>
  let Aum = star_controllable_subset (des_langUM C) \<Sigma>UC Pum
  in DES Aum (Aum \<inter> des_langM C)"

lemma Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset_hlp1: "
  w' \<in> prefix_closure {w @ [a]}
  \<Longrightarrow> w' \<noteq> w @ [a]
  \<Longrightarrow> w' \<notin> prefix_closure {w}
  \<Longrightarrow> Q"
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac w')
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c aa list)(*strict*)
  apply (metis prefix_def prefixAndNotStrictPrefixIsEQI)
  done

lemma Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
    (Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P))
    IsDES
    (predicate_AND IsDES (DES_controllability \<Sigma>UC P))
    (predicate_AND IsDES (DES_controllability \<Sigma>UC P))"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: star_controllable_subset_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: star_controllable_subset_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def controllable_language_def)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac P)
    apply(rename_tac LUM LM fun1 fun2)(*strict*)
    apply(rename_tac PUM PM)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac LUM LM PUM PM)(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(simp add: controllable_sublanguage_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w')(*strict*)
     apply(simp add: controllable_word_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(rule DES_apply_controllability)
           apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
           apply(force)+
      apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
      apply(clarsimp)
      apply(rename_tac LUM LM PUM PM x w' u xa)(*strict*)
      apply(simp add: kleene_star_def)
      apply(force)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(subgoal_tac "LM\<subseteq> LUM")
     apply(rename_tac LUM LM PUM PM)(*strict*)
     prefer 2
     apply(simp add: kleene_star_def DES_nonblockingness_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(simp add: kleene_star_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def Enforce_Star_Controllable_Subset_def DES_controllability_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def controllable_language_def)
   apply(clarsimp)
   apply(rename_tac X x)(*strict*)
   apply(case_tac X)
   apply(rename_tac X x fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X x LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac x LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac x LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac x LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(simp add: star_controllable_subset_def append_alphabet_def append_language_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(subgoal_tac "w \<in> {w \<in> LUM. controllable_sublanguage (prefix_closure {w}) (kleene_star \<Sigma>UC) PUM LUM}")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(thin_tac "{w \<in> LUM. controllable_sublanguage (prefix_closure {w}) (kleene_star \<Sigma>UC) PUM LUM} = LUM")
    apply(clarsimp)
    apply(simp add: controllable_sublanguage_def)
    apply(simp add: controllable_word_def)
    apply(erule_tac
      x="w"
      in ballE)
     apply(rename_tac LUM LM PUM PM w a)(*strict*)
     apply(simp add: kleene_star_def prefix_closure_def prefix_def append_language_def alphabet_to_language_def)
     apply(clarsimp)
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: DES_controllability_def)
   apply(rule context_conjI)
    apply(rename_tac X)(*strict*)
    apply(simp add: star_controllable_subset_def DES_nonblockingness_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
    apply(clarsimp)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac P)
    apply(rename_tac LUM LM fun1 fun2)(*strict*)
    apply(rename_tac PUM PM)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(rule order_antisym)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x c)(*strict*)
     apply(rule conjI)
      apply(rename_tac LUM LM PUM PM x c)(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM x c)(*strict*)
     apply(simp add: controllable_sublanguage_def)
     apply(clarsimp)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(rule_tac
      x="x"
      in exI)
    apply(rule conjI)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(simp add: controllable_sublanguage_def)
   apply(rename_tac X)(*strict*)
   apply(simp add: star_controllable_subset_def DES_nonblockingness_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def controllable_language_def)
   apply(clarsimp)
   apply(rename_tac X x)(*strict*)
   apply(case_tac X)
   apply(rename_tac X x fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X x LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac x LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac x LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac x LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(subgoal_tac "w \<in> {w \<in> LUM. controllable_sublanguage (prefix_closure {w}) (kleene_star \<Sigma>UC) PUM LUM}")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(simp add: controllable_sublanguage_def)
    apply(erule_tac
      x="w"
      in ballE)
     apply(rename_tac LUM LM PUM PM w a)(*strict*)
     apply(simp add: controllable_word_def kleene_star_def)
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(simp add: prefix_closure_def prefix_def kleene_star_def)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a w')(*strict*)
   apply(case_tac "w'\<noteq>w@[a]")
    apply(rename_tac LUM LM PUM PM w a w')(*strict*)
    apply(erule_tac
      x="w'"
      in ballE)
     apply(rename_tac LUM LM PUM PM w a w')(*strict*)
     prefer 2
     apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset_hlp1)
       apply(rename_tac LUM LM PUM PM w a w')(*strict*)
       apply(force)
      apply(rename_tac LUM LM PUM PM w a w')(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM w a w')(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM w a w')(*strict*)
    apply(force)
   apply(rename_tac LUM LM PUM PM w a w')(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(erule_tac
      x="w"
      in ballE)
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    prefer 2
    apply(simp add: prefix_closure_def prefix_def)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(simp add: controllable_word_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(simp add: star_controllable_subset_def DES_nonblockingness_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac X Y fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac X Y LUM1 LM1)(*strict*)
  apply(clarsimp)
  apply(rename_tac Y LUM1 LM1)(*strict*)
  apply(case_tac Y)
  apply(rename_tac Y LUM1 LM1 fun1 fun2)(*strict*)
  apply(rename_tac LUM2 LM2)
  apply(rename_tac Y LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(case_tac P)
  apply(rename_tac LUM1 LM1 LUM2 LM2 fun1 fun2)(*strict*)
  apply(rename_tac PUM2 PM2)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(erule_tac
      x="u"
      in allE)
    apply(clarsimp)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(erule_tac
      x="u"
      in allE)
    apply(clarsimp)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
  apply(force)
  done

theorem Fixed_Point_Iterator_Enforce_Star_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
    (Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P))
    {C. IsDES C}
    {C. IsDES C \<and> DES_controllability \<Sigma>UC P C}
    {C. IsDES C \<and> DES_controllability \<Sigma>UC P C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

corollary Enforce_Star_Controllable_Subset_Sound: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> SAT = {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A}
  \<Longrightarrow> RES = Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P) C
  \<Longrightarrow> RES = Sup SAT \<and> RES \<in> SAT"
  apply(rule propSym)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(rule conjI)
    apply(simp add: Enforce_Star_Controllable_Subset_def Let_def)
    apply(simp add: star_controllable_subset_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: Enforce_Star_Controllable_Subset_def Let_def)
    apply(simp add: IsDES_def star_controllable_subset_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
    apply(case_tac C)
    apply(rename_tac set1 set2)(*strict*)
    apply(rename_tac Cum Cm)
    apply(rename_tac Cum Cm)(*strict*)
    apply(clarsimp)
    apply(rule antisym)
     apply(rename_tac Cum Cm)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac Cum Cm x)(*strict*)
     apply(simp add: prefix_closure_def)
     apply(rule_tac
      x="x"
      in exI)
     apply(clarsimp)
     apply(simp add: prefix_def)
    apply(rename_tac Cum Cm)(*strict*)
    apply(clarsimp)
    apply(rename_tac Cum Cm x)(*strict*)
    apply(simp add: controllable_sublanguage_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac Cum Cm x c)(*strict*)
    apply(rule conjI)
     apply(rename_tac Cum Cm x c)(*strict*)
     apply (metis (mono_tags, lifting) mem_Collect_eq)
    apply(rename_tac Cum Cm x c)(*strict*)
    apply(clarsimp)
   apply(simp add: DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def des_langUM_def)
   apply(rule star_controllable_language_implies_controllable_language)
   apply(rule star_controllable_subset_FP_implies_star_controllable_language)
    apply(rule star_controllable_subset_prefix_closed)
    apply(simp add: IsDES_def)
    apply(case_tac C)
    apply(rename_tac set1 set2)(*strict*)
    apply(rename_tac Cum Cm)
    apply(rename_tac Cum Cm)(*strict*)
    apply(clarsimp)
   apply(rule star_controllable_subset_idempotent)
    apply(simp add: IsDES_def)
    apply(clarsimp)
    apply(simp add: des_langUM_def)
   apply(simp add: IsDES_def)
   apply(clarsimp)
   apply(simp add: des_langUM_def)
  apply(rule antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(force)
  done

definition Enforce_Controllable_Subset :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Controllable_Subset \<Sigma>UC Pum C \<equiv>
  let Aum = controllable_subset (des_langUM C) \<Sigma>UC Pum
  in DES Aum (Aum \<inter> des_langM C)"

lemma Characteristic_Fixed_Point_Iterator_Enforce_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (Enforce_Controllable_Subset \<Sigma>UC (des_langUM P)) IsDES (predicate_AND IsDES (DES_controllability \<Sigma>UC P)) IsDES"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: controllable_subset_def Enforce_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: controllable_subset_def DES_controllability_def Enforce_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def controllable_language_def)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac P)
    apply(rename_tac LUM LM fun1 fun2)(*strict*)
    apply(rename_tac PUM PM)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac LUM LM PUM PM)(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(simp add: controllable_sublanguage_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w')(*strict*)
     apply(simp add: controllable_word_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(rule DES_apply_controllability)
           apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
           apply(force)+
      apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
      apply(simp add: alphabet_to_language_def)
      apply(force)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(force)+
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(simp add: DES_nonblockingness_def DES_controllability_def Enforce_Star_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def DES_controllability_def Enforce_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def controllable_language_def)
   apply(clarsimp)
   apply(rename_tac X x)(*strict*)
   apply(case_tac X)
   apply(rename_tac X x fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X x LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac x LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac x LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac x LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(subgoal_tac "w \<in> {w \<in> LUM. controllable_sublanguage (prefix_closure {w}) (alphabet_to_language \<Sigma>UC) PUM LUM}")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(clarsimp)
    apply(simp add: controllable_sublanguage_def)
    apply(simp add: controllable_word_def alphabet_to_language_def)
    apply(erule_tac
      x="w"
      in ballE)
     apply(rename_tac LUM LM PUM PM w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(simp add: prefix_closure_def prefix_def alphabet_to_language_def)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(simp add: controllable_subset_def alphabet_to_language_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: controllable_subset_def DES_nonblockingness_def DES_controllability_def Enforce_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
   apply(clarsimp)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x c)(*strict*)
    apply(rule conjI)
     apply(rename_tac LUM LM PUM PM x c)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM x c)(*strict*)
    apply(simp add: controllable_sublanguage_def)
    apply(clarsimp)
   apply(rename_tac LUM LM PUM PM)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule conjI)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(force)
   apply(rename_tac LUM LM PUM PM x)(*strict*)
   apply(simp add: controllable_sublanguage_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(simp add: controllable_subset_def DES_nonblockingness_def DES_controllability_def Enforce_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
  apply(clarsimp)
  apply(case_tac X)
  apply(rename_tac X Y fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac X Y LUM1 LM1)(*strict*)
  apply(clarsimp)
  apply(rename_tac Y LUM1 LM1)(*strict*)
  apply(case_tac Y)
  apply(rename_tac Y LUM1 LM1 fun1 fun2)(*strict*)
  apply(rename_tac LUM2 LM2)
  apply(rename_tac Y LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(case_tac P)
  apply(rename_tac LUM1 LM1 LUM2 LM2 fun1 fun2)(*strict*)
  apply(rename_tac PUM2 PM2)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def alphabet_to_language_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' v)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def alphabet_to_language_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' v)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
  apply(force)
  done

theorem Fixed_Point_Iterator_Enforce_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
  (Enforce_Controllable_Subset \<Sigma>UC (des_langUM P))
  {C. IsDES C}
  {C. IsDES C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Controllable_Subset)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

corollary Enforce_Controllable_Subset_Sound: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> SAT1 = {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A}
  \<Longrightarrow> SAT2 = {A. A \<le> C \<and> IsDES A}
  \<Longrightarrow> RES = Enforce_Controllable_Subset \<Sigma>UC (des_langUM P) C
  \<Longrightarrow> RES \<ge> Sup SAT1 \<and> RES \<in> SAT2"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Characteristic_Fixed_Point_Iterator_Enforce_Controllable_Subset)
   apply(force)
  apply(rule context_conjI)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(force)
  apply(clarsimp)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

definition Enforce_Marked_Controllable_Subset :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C \<equiv>
  let Am = controllable_subset (des_langUM C) \<Sigma>UC Pum \<inter> des_langM C;
      Aum = {w. w \<in> des_langUM C
        \<and> controllable_sublanguage ((prefix_closure {w})-{w}) (alphabet_to_language \<Sigma>UC) Pum (des_langUM C)}
  in DES Aum Am"

definition Enforce_Marked_Controllable_Subset_Alt :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "Enforce_Marked_Controllable_Subset_Alt \<Sigma>UC Pum C \<equiv>
  DES 
  {w' \<in> des_langUM C. \<forall>w u. strict_prefix w w' \<longrightarrow> u \<in> \<Sigma>UC \<longrightarrow> w @ [u] \<in> Pum \<longrightarrow> w @ [u] \<in> des_langUM C}
  {w' \<in> des_langM C. \<forall>w u. prefix w w' \<longrightarrow> u \<in> \<Sigma>UC \<longrightarrow> w @ [u] \<in> Pum \<longrightarrow> w @ [u] \<in> des_langUM C}"

lemma Enforce_Marked_Controllable_Subset_Alt__vs__Enforce_Marked_Controllable_Subset: "
  IsDES C
  \<Longrightarrow> Enforce_Marked_Controllable_Subset_Alt \<Sigma>UC Pum C = Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C"
  apply(simp add: Enforce_Marked_Controllable_Subset_Alt_def Enforce_Marked_Controllable_Subset_def Let_def)
  apply(rule propSym)
  apply(rule conjI) 
   apply(rule antisym)
    apply(simp add: controllable_subset_def controllable_word_def controllable_sublanguage_def prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def)
    apply(rule conjI)
     apply(clarsimp)  
     apply(rule conjI)
      apply(simp add: IsDES_def)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: controllable_subset_def controllable_word_def controllable_sublanguage_def prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def)
   apply(clarsimp)
  apply(rule antisym)
   apply(clarsimp)
   apply(simp add: controllable_word_def controllable_sublanguage_def prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def)
   apply(clarsimp)
   apply (metis append_Nil2 prefix_def strict_prefix_def) 
  apply(clarsimp)
  apply(simp add: strict_prefix_def controllable_word_def controllable_sublanguage_def prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def)
  apply(erule_tac x="w" in ballE)
   apply(clarsimp)
  apply(clarsimp)
  apply (metis prefix_append)
  done

corollary Enforce_Controllable_Subset_smaller_than_Enforce_Marked_Controllable_Subset: "
  Enforce_Controllable_Subset \<Sigma>UC Pum C \<le> Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C"
  apply(simp add: Enforce_Marked_Controllable_Subset_def Enforce_Controllable_Subset_def Let_def)
  apply(simp add: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: controllable_subset_def controllable_sublanguage_def)
  done

lemma Enforce_Controllable_Subset1: "
  \<Sigma>UC = {u}
  \<Longrightarrow> Pum = {[],[a],[a,u]}
  \<Longrightarrow> C = DES {[],[a]} {[]}
  \<Longrightarrow> Enforce_Controllable_Subset \<Sigma>UC Pum C = DES {[]} {[]}"
  apply(simp add: Enforce_Marked_Controllable_Subset_def Enforce_Controllable_Subset_def Let_def)
  apply(simp only: controllable_subset_def)
  apply(simp only: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def controllable_subset_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(clarsimp)
   apply(simp add: prefix_closure_def prefix_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(simp add: prefix_closure_def prefix_def)
  done

lemma Enforce_Marked_Controllable_Subset1: "
  \<Sigma>UC = {u}
  \<Longrightarrow> Pum = {[],[a],[a,u]}
  \<Longrightarrow> C = DES {[],[a]} {[]}
  \<Longrightarrow> Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C = C"
  apply(simp add: Enforce_Marked_Controllable_Subset_def Enforce_Controllable_Subset_def Let_def)
  apply(simp only: controllable_subset_def)
  apply(simp only: less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def controllable_subset_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule antisym)
    apply(clarsimp)
   apply(simp add: prefix_closure_def prefix_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(simp add: prefix_closure_def prefix_def)
  done

corollary Enforce_Controllable_Subset_strictly_smaller_than_Enforce_Marked_Controllable_Subset: "
  \<Sigma>UC = {u}
  \<Longrightarrow> Pum = {[],[a],[a,u]}
  \<Longrightarrow> C = DES {[],[a]} {[]}
  \<Longrightarrow> Enforce_Controllable_Subset \<Sigma>UC Pum C = DES {[]} {[]}
  \<and> Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C = C"
  apply(rule conjI)
   apply(rule Enforce_Controllable_Subset1)
     apply(force)
    apply(force)
   apply(force)
  apply(rule Enforce_Marked_Controllable_Subset1)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P))
  (predicate_AND IsDES DES_nonblockingness)
  (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P)))
  IsDES"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(simp add: controllable_sublanguage_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def controllable_language_def)
    apply(case_tac X)
    apply(rename_tac X fun1 fun2)(*strict*)
    apply(rename_tac LUM LM)
    apply(rename_tac X LUM LM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM)(*strict*)
    apply(case_tac P)
    apply(rename_tac LUM LM fun1 fun2)(*strict*)
    apply(rename_tac PUM PM)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(rule context_conjI)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac LUM LM PUM PM)(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(simp add: controllable_sublanguage_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w')(*strict*)
     apply(simp add: controllable_word_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(simp add: alphabet_to_language_def)
     apply(clarsimp)
     apply(rename_tac LUM LM PUM PM x w' v)(*strict*)
     apply(subgoal_tac "w' @ [v] \<in> LUM")
      apply(rename_tac LUM LM PUM PM x w' v)(*strict*)
      apply(force)
     apply(rename_tac LUM LM PUM PM x w' v)(*strict*)
     apply(rule DES_apply_controllability)
           apply(rename_tac LUM LM PUM PM x w' v)(*strict*)
           apply(force)+
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac LUM LM PUM PM)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(simp (no_asm) add: controllable_subset_def controllable_sublanguage_def)
    apply(rule conjI)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(simp add: IsDES_def)
     apply (metis DES.case contra_subsetD des_langM_def des_langUM_def)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x w')(*strict*)
    apply(simp (no_asm) add: controllable_word_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(subgoal_tac "w'\<in> LUM")
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     prefer 2
     apply(simp add: DES_nonblockingness_def DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
     apply(simp add: IsDES_def prefix_closure_def prefix_def)
     apply(blast)
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(subgoal_tac "w'\<in> {w \<in> LUM. controllable_sublanguage ((prefix_closure {w}) - {w}) (alphabet_to_language \<Sigma>UC) PUM LUM}")
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     prefer 2
     apply(blast)
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(thin_tac "{w \<in> LUM. controllable_sublanguage ((prefix_closure {w}) - {w}) (alphabet_to_language \<Sigma>UC) PUM LUM}=LUM")
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(clarsimp)
    apply(case_tac "controllable_word w' (alphabet_to_language \<Sigma>UC) PUM LUM")
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(simp add: controllable_word_def)
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(rule_tac
      A="append_alphabet LUM \<Sigma>UC \<inter> PUM"
      in set_mp)
     apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
    apply(simp add: append_alphabet_def alphabet_to_language_def append_language_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_nonblockingness_def DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def controllable_language_def)
   apply(clarsimp)
   apply(rename_tac X x)(*strict*)
   apply(case_tac X)
   apply(rename_tac X x fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X x LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac x LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac x LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac x LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(simp add: append_language_def append_alphabet_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(case_tac "\<not> controllable_word w (alphabet_to_language \<Sigma>UC) PUM LUM")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(simp add: controllable_word_def)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(subgoal_tac "controllable_word w (alphabet_to_language \<Sigma>UC) PUM LUM")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(force)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(subgoal_tac "\<exists>v. w @ v \<in> LM")
    apply(rename_tac LUM LM PUM PM w a)(*strict*)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM w a v)(*strict*)
    apply(subgoal_tac "w@v \<in> {w \<in> LM. controllable_sublanguage (prefix_closure {w}) (alphabet_to_language \<Sigma>UC) PUM LUM}")
     apply(rename_tac LUM LM PUM PM w a v)(*strict*)
     prefer 2
     apply(simp add: controllable_subset_def)
     apply(force)
    apply(rename_tac LUM LM PUM PM w a v)(*strict*)
    apply(thin_tac "{w \<in> LUM. controllable_sublanguage (prefix_closure {w} - {w}) \<langle>\<Sigma>UC\<rangle> PUM LUM} = LUM")
    apply(clarsimp)
    apply(simp add: controllable_sublanguage_def)
    apply(erule_tac
      x="w"
      in ballE)
     apply(rename_tac LUM LM PUM PM w a v)(*strict*)
     prefer 2
     apply(simp add: prefix_closure_def prefix_def)
    apply(rename_tac LUM LM PUM PM w a v)(*strict*)
    apply(force)
   apply(rename_tac LUM LM PUM PM w a)(*strict*)
   apply(simp add: prefix_closure_def prefix_def nonblockingness_language_def)
   apply(force)
  apply(rule conjI)
   apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "IsDES X")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(simp add: DES_nonblockingness_def)
    apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
   apply(rename_tac X)(*strict*)
   apply(case_tac X)
   apply(rename_tac X fun1 fun2)(*strict*)
   apply(rename_tac LUM LM)
   apply(rename_tac X LUM LM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM)(*strict*)
   apply(case_tac P)
   apply(rename_tac LUM LM fun1 fun2)(*strict*)
   apply(rename_tac PUM PM)
   apply(rename_tac LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(rule conjI)
     apply(rename_tac LUM LM PUM PM x)(*strict*)
     apply(simp add: DES_nonblockingness_def)
     apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
     apply(force)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(simp add: controllable_subset_def controllable_sublanguage_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM w c)(*strict*)
    apply(erule_tac
      x="w"
      in ballE)
     apply(rename_tac LUM LM PUM PM w c)(*strict*)
     apply(force)
    apply(rename_tac LUM LM PUM PM w c)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
   apply(rename_tac LUM LM PUM PM)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac LUM LM PUM PM)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(rule_tac
      x="x"
      in exI)
    apply(clarsimp)
   apply(rename_tac LUM LM PUM PM)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM LM PUM PM x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac LUM LM PUM PM x c)(*strict*)
    apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
    apply(simp add: prefix_closure_def prefix_def)
    apply(blast)
   apply(rename_tac LUM LM PUM PM x)(*strict*)
   apply(simp (no_asm) add: controllable_sublanguage_def)
   apply(simp (no_asm) add: controllable_word_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM x w' u)(*strict*)
   apply(simp add: prefix_closure_def)
   apply(clarsimp)
   apply(rename_tac LUM LM PUM PM x w' u v)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM LM PUM PM x w' u v)(*strict*)
    apply(simp add: controllable_word_def)
   apply(rename_tac LUM LM PUM PM x w' u v)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def prefix_closure_def)
   apply(force)
  apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(subgoal_tac "IsDES X")
   apply(rename_tac X Y)(*strict*)
   prefer 2
   apply(simp add: DES_nonblockingness_def)
   apply(simp add: DES_controllability_def Enforce_Marked_Controllable_Subset_def Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
  apply(rename_tac X Y)(*strict*)
  apply(case_tac X)
  apply(rename_tac X Y fun1 fun2)(*strict*)
  apply(rename_tac LUM1 LM1)
  apply(rename_tac X Y LUM1 LM1)(*strict*)
  apply(clarsimp)
  apply(rename_tac Y LUM1 LM1)(*strict*)
  apply(case_tac Y)
  apply(rename_tac Y LUM1 LM1 fun1 fun2)(*strict*)
  apply(rename_tac LUM2 LM2)
  apply(rename_tac Y LUM1 LM1 LUM2 LM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2)(*strict*)
  apply(case_tac P)
  apply(rename_tac LUM1 LM1 LUM2 LM2 fun1 fun2)(*strict*)
  apply(rename_tac PUM2 PM2)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(erule_tac
      x="u"
      in ballE)
     apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(simp add: controllable_subset_def)
  apply(rule conjI)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(erule_tac
      x="w'"
      in ballE)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
    apply(simp add: controllable_word_def)
    apply(clarsimp)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(erule_tac
      x="u"
      in ballE)
     apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w' u)(*strict*)
    apply(force)
   apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x w')(*strict*)
   apply(force)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2)(*strict*)
  apply(clarsimp)
  apply(rename_tac LUM1 LM1 LUM2 LM2 PUM2 PM2 x)(*strict*)
  apply (metis contra_subsetD)
  done

theorem Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
  (Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P))
  {C. IsDES C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Enforce_Nonblockingness_DES__on__Enforce_Marked_Controllable_Subset__smaller_than__Enforce_Controllable_Subset: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> Enforce_Nonblockingness_DES (Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C) \<le> Enforce_Controllable_Subset \<Sigma>UC Pum C"
  apply(simp add: Enforce_Nonblockingness_DES_def Enforce_Marked_Controllable_Subset_def Enforce_Controllable_Subset_def des_langM_def Let_def des_langUM_def DES_nonblockingness_def nonblockingness_language_def controllable_subset_def IsDES_def less_eq_DES_ext_def lesseqDES_def)
  apply(case_tac C)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Cum Cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Cum Cm x)(*strict*)
  apply(subgoal_tac "Cum = prefix_closure Cm")
   apply(rename_tac Cum Cm x)(*strict*)
   prefer 2
   apply(rule antisym)
    apply(rename_tac Cum Cm x)(*strict*)
    apply(force)
   apply(rename_tac Cum Cm x)(*strict*)
   apply(clarsimp)
   apply(rename_tac Cum Cm x xa)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac Cum Cm x)(*strict*)
  apply(clarsimp)
  apply(rename_tac Cm x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac Cm x c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac Cm x c ca)(*strict*)
   apply(force)
  apply(rename_tac Cm x c ca)(*strict*)
  apply(simp add: controllable_sublanguage_def)
  apply(clarsimp)
  done

corollary Enforce_Controllable_Subset_equal_to_Enforce_Marked_Controllable_Subset_up_to_Enforce_Nonblockingness_DES: "
  IsDES C
  \<Longrightarrow> Enforce_Nonblockingness_DES (Enforce_Controllable_Subset \<Sigma>UC Pum C)
  = Enforce_Nonblockingness_DES (Enforce_Marked_Controllable_Subset \<Sigma>UC Pum C)"
  apply(simp add: Enforce_Nonblockingness_DES_def Enforce_Marked_Controllable_Subset_def Enforce_Controllable_Subset_def des_langM_def Let_def des_langUM_def DES_nonblockingness_def nonblockingness_language_def controllable_subset_def IsDES_def less_eq_DES_ext_def lesseqDES_def)
  done


definition DES_marked_controllability :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> bool" where
  "DES_marked_controllability \<Sigma>UC P C \<equiv>
  \<forall>w' w u.
    w' \<in> des_langM C
    \<longrightarrow> prefix w w'
    \<longrightarrow> u \<in> \<Sigma>UC
    \<longrightarrow> w @ [u]  \<in> des_langUM P
    \<longrightarrow> w @ [u]  \<in> des_langUM C"

theorem DES_marked_controllability__vs__DES_controllability: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> DES_marked_controllability \<Sigma>UC P C \<longleftrightarrow> DES_controllability \<Sigma>UC P C"
  apply(rule antisym)
   apply(simp add: prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_marked_controllability_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def)
   apply(clarsimp)
   apply(subgoal_tac "a \<in>  {w. \<exists>v. v \<in> des_langM C \<and> w \<sqsubseteq> v}")
    prefer 2
    apply(force)
   apply(clarsimp)
  apply(simp add: prefix_closure_def nonblockingness_language_def DES_nonblockingness_def DES_marked_controllability_def DES_controllability_def alphabet_to_language_def controllable_language_def append_alphabet_def append_language_def) 
  apply(clarsimp)
  apply(subgoal_tac "w @[u] \<in> {w. \<exists>a\<in>des_langUM C. \<exists>b. (\<exists>v\<in>\<Sigma>UC. b = [v]) \<and> w = a @ b}")
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="w" in bexI)
   apply(clarsimp)
  apply(simp add: IsDES_def)
  apply(metis contra_subsetD prefixExists prefix_def)
  done


corollary Enforce_Marked_Controllable_Subset_Sound: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> SAT1 = {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}
  \<Longrightarrow> SAT2 = {A. A \<le> C \<and> IsDES A}
  \<Longrightarrow> RES = Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C
  \<Longrightarrow> RES \<ge> Sup SAT1 \<and> RES \<in> SAT2"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(force)
  done

theorem Enforce_Marked_Controllable_Subset_Sound2: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> SAT1 = {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}
  \<Longrightarrow> SAT2 = {A. A \<le> C \<and> IsDES A}
  \<Longrightarrow> RES = Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C
  \<Longrightarrow> (RES = Sup SAT1 \<or> (C > RES \<and> RES > Sup SAT1)) \<and> RES \<in> SAT2"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Enforce_Marked_Controllable_Subset_Sound)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(case_tac "RES = Sup SAT1")
   apply(force)
  apply(rule disjI2)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "Sup {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}
    < Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C")
   prefer 2
   apply(force)
  apply(thin_tac "Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C \<noteq>
    Sup {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}")
  apply(thin_tac "Sup {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}
    \<le> Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C")
  apply(case_tac "Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C = C")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "Sup {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A}
    \<ge> Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P) C")
   apply(force)
  apply(clarsimp)
  apply(thin_tac "Sup {A. A \<le> C \<and> IsDES A \<and> DES_controllability \<Sigma>UC P A \<and> DES_nonblockingness A} < C")
  apply(rule Sup_upper)
  apply(clarsimp)
  apply(subgoal_tac "DES_marked_controllability \<Sigma>UC P C")
   apply (metis DES_marked_controllability__vs__DES_controllability)
  apply(simp add: DES_marked_controllability_def Enforce_Marked_Controllable_Subset_def DES_nonblockingness_def nonblockingness_language_def)
  apply(clarsimp)
  apply(case_tac C)
  apply(rename_tac Cum Cm)
  apply(clarsimp)
  apply(case_tac "w=w'")
   prefer 2
   apply(subgoal_tac "w' \<in> Cum")
    prefer 2
    apply(simp add: IsDES_def)
    apply (metis contra_subsetD)
   apply(subgoal_tac "controllable_sublanguage (prefix_closure {w'} - {w'}) \<langle>\<Sigma>UC\<rangle> (des_langUM P) Cum")
    prefer 2
    apply(force)
   apply(thin_tac "{w \<in> Cum.
        controllable_sublanguage (prefix_closure {w} - {w}) \<langle>\<Sigma>UC\<rangle> (des_langUM P) Cum} =
       Cum")
   apply(simp add: controllable_sublanguage_def)
   apply(erule_tac x="w" in ballE)
    apply(simp add: controllable_word_def alphabet_to_language_def)
   apply(simp add: prefix_closure_def)
  apply(clarsimp)
  apply(thin_tac "{w \<in> Cum.
        controllable_sublanguage (prefix_closure {w} - {w}) \<langle>\<Sigma>UC\<rangle> (des_langUM P) Cum} =
       Cum")
  apply(subgoal_tac "w'\<in>controllable_subset Cum \<Sigma>UC (des_langUM P)")
   prefer 2
   apply(force)
  apply(simp add: controllable_subset_def)
  apply(clarsimp)
  apply(simp add: controllable_sublanguage_def)
  apply(erule_tac x="w'" in ballE)
   apply(simp add: controllable_word_def alphabet_to_language_def)
  apply(simp add: prefix_closure_def)
  done

end
