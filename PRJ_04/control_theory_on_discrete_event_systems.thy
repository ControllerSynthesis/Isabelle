section {*control\_theory\_on\_discrete\_event\_systems*}
theory control_theory_on_discrete_event_systems

imports
  control_theory_on_languages

begin

lemma infDES_preserves_IsDES: "
  IsDES A
  \<Longrightarrow> IsDES B
  \<Longrightarrow> IsDES (infDES A B)"
  apply(simp add: IsDES_def)
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def)
  apply(case_tac A)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac B)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule conjI)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac fun1 fun2 fun1a fun2a x)(*strict*)
   apply(force)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(rule conjI)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac fun1 fun2 fun1a fun2a x)(*strict*)
   apply(force)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac fun1 fun2 fun1a fun2a x c)(*strict*)
    apply(force)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(force)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(force)
  done

lemma DES_apply_controllability: "
  IsDES (DES PUM PM)
  \<Longrightarrow> IsDES (DES LUM LM)
  \<Longrightarrow> append_alphabet LUM SigmaUC \<inter> PUM \<subseteq> LUM
  \<Longrightarrow> x \<in> LUM
  \<Longrightarrow> w' \<in> prefix_closure {x}
  \<Longrightarrow> set u \<subseteq> SigmaUC
  \<Longrightarrow> w' @ u \<in> PUM
  \<Longrightarrow> w' @ u \<in> LUM"
  apply(induct u rule: rev_induct)
   apply(clarsimp)
   apply(rule_tac
      A="prefix_closure {x}"
      in set_mp)
    apply(rule_tac
      t="LUM"
      and s="prefix_closure LUM"
      in ssubst)
     apply(simp add: Let_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def IsDES_def)
    apply(rule prefix_closure_preserves_subseteq)
    apply(force)
   apply(force)
  apply(rename_tac xa xs)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="append_alphabet LUM SigmaUC \<inter> PUM"
      in set_mp)
   apply(rename_tac xa xs)(*strict*)
   apply(force)
  apply(rename_tac xa xs)(*strict*)
  apply(thin_tac "append_alphabet LUM SigmaUC \<inter> PUM \<subseteq> LUM")
  apply(clarsimp)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(erule meta_impE)
   apply(rename_tac xa xs)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa xs)(*strict*)
  apply(simp add: IsDES_def)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x xs c)(*strict*)
  apply(force)
  done

definition DES_controllability :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> bool" where
  "DES_controllability \<Sigma>UC P C \<equiv>
  controllable_language (des_langUM C) \<Sigma>UC (des_langUM P)"

definition DES_specification_satisfied :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> bool" where
  "DES_specification_satisfied S C \<equiv>
  C \<le> S"

definition DES_nonblockingness :: "
  '\<Sigma> DES
  \<Rightarrow> bool" where
  "DES_nonblockingness C \<equiv>
  nonblockingness_language (des_langUM C) (des_langM C)"

lemma DES_specification_satisfied_from_DES_nonblockingness_and_marked_satisfaction: "
  IsDES S
  \<Longrightarrow> des_langM C \<subseteq> des_langM S
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> DES_specification_satisfied S C"
  apply(case_tac C)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Cum Cm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Cum Cm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Cum Cm SPECum Sm)(*strict*)
  apply(simp add: DES_specification_satisfied_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac Cum Cm SPECum Sm x)(*strict*)
  apply(force)
  done

lemma Sup_Cont_contained: "
  (\<And>X. X\<in> A \<Longrightarrow> DES_controllability SigmaUC P X)
  \<Longrightarrow> DES_controllability SigmaUC P (Sup A)"
  apply(simp add: DES_controllability_def)
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def append_alphabet_def append_language_def alphabet_to_language_def controllable_language_def)
  apply(clarsimp)
  apply(rename_tac a v s)(*strict*)
  apply(case_tac P)
  apply(rename_tac a v s fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v s fun1)(*strict*)
  apply(erule_tac
      x="a"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a v s fun1 fun1a fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v s fun1a fun2)(*strict*)
  apply(force)
  done

lemma Sup_BF_contained: "
  (\<And>X. X\<in> A \<Longrightarrow> DES_nonblockingness X)
  \<Longrightarrow> DES_nonblockingness (Sup A)"
  apply(simp add: DES_nonblockingness_def)
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def append_alphabet_def nonblockingness_language_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x="xa"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac xa)
  apply(rename_tac x xa fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x fun1 fun2)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(force)
  done

lemma Sup_Spec_contained: "
  (\<And>X. X\<in> A \<Longrightarrow> DES_specification_satisfied S X)
  \<Longrightarrow> DES_specification_satisfied S (Sup A)"
  apply(simp add: DES_specification_satisfied_def)
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def append_alphabet_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      in meta_allE)
   apply(clarsimp)
   apply(case_tac xa)
   apply(rename_tac x xa fun1 fun2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x fun1 fun2)(*strict*)
   apply(case_tac S)
   apply(rename_tac x fun1 fun2 fun1a fun2a)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x="xa"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac xa)
  apply(rename_tac x xa fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x fun1 fun2)(*strict*)
  apply(case_tac S)
  apply(rename_tac x fun1 fun2 fun1a fun2a)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma Sup_Plant_subset: "
  (\<And>X. X\<in> A \<Longrightarrow> X \<le> (P::'a DES))
  \<Longrightarrow> Sup A \<le> P"
  apply(fold DES_specification_satisfied_def)
  apply(rule Sup_Spec_contained)
  apply(rename_tac X)(*strict*)
  apply(force)
  done

lemma DES_controllability_coinfimum: "
  IsDES P
  \<Longrightarrow> DES_controllability \<Sigma>UC P (inf C P)
  \<Longrightarrow> DES_controllability \<Sigma>UC P C"
  apply(simp add: DES_controllability_def controllable_language_def des_langUM_def des_langM_def infDES_def inf_DES_ext_def lesseqDES_def IsDES_def prefix_closure_def less_eq_DES_ext_def)
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Pum Pm Cum x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac Pum Pm Cum a v)(*strict*)
  apply(rule_tac
      A="{w. \<exists>a\<in> Cum \<inter> Pum. \<exists>b. (\<exists>v\<in> \<Sigma>UC. b = [v]) \<and> w = a @ b} \<inter> Pum"
      in set_mp)
   apply(rename_tac Pum Pm Cum a v)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Cum a v)(*strict*)
  apply(simp (no_asm))
  apply(rule conjI)
   apply(rename_tac Pum Pm Cum a v)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm Cum a v)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac Pum Pm Cum a v)(*strict*)
   apply(blast)
  apply(rename_tac Pum Pm Cum a v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="{w. \<exists>v. v \<in> Pum \<and> w \<sqsubseteq> v}"
      in set_mp)
   apply(rename_tac Pum Pm Cum a v)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Cum a v)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  done

lemma DES_controllability_infimum: "
  DES_controllability \<Sigma>UC P C
  \<Longrightarrow> DES_controllability \<Sigma>UC P (inf C P)"
  apply(simp add: DES_controllability_def controllable_language_def des_langUM_def des_langM_def infDES_def inf_DES_ext_def lesseqDES_def IsDES_def prefix_closure_def less_eq_DES_ext_def)
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Pum Cum x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac Pum Cum a v)(*strict*)
  apply(rule_tac
      A="{w. \<exists>a\<in> Cum. \<exists>b. (\<exists>v\<in> \<Sigma>UC. b = [v]) \<and> w = a @ b} \<inter> Pum"
      in set_mp)
   apply(rename_tac Pum Cum a v)(*strict*)
   apply(force)
  apply(rename_tac Pum Cum a v)(*strict*)
  apply(simp (no_asm))
  apply(rule conjI)
   apply(rename_tac Pum Cum a v)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac Pum Cum a v)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac Pum Cum a v)(*strict*)
   apply(blast)
  apply(rename_tac Pum Cum a v)(*strict*)
  apply(clarsimp)
  done

corollary DES_controllability_coincides_on_controller_and_closed_loop: "
  IsDES P
  \<Longrightarrow> DES_controllability \<Sigma>UC P C \<longleftrightarrow> DES_controllability \<Sigma>UC P (inf C P)"
  apply(rule antisym)
   apply(clarsimp)
   apply(metis DES_controllability_infimum)
  apply(clarsimp)
  apply(metis DES_controllability_coinfimum)
  done

lemma DES_nonblockingness_infimum: "
  C \<le> P
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> DES_nonblockingness (inf C P)"
  apply(simp add: nonblockingness_language_def DES_nonblockingness_def des_langUM_def des_langM_def infDES_def inf_DES_ext_def lesseqDES_def IsDES_def prefix_closure_def less_eq_DES_ext_def)
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Pum Pm Cum Cm x)(*strict*)
  apply(blast)
  done

lemma Sup_DES_contained: "
  (\<And>X. X\<in> A \<Longrightarrow> IsDES X)
  \<Longrightarrow> IsDES (Sup A)"
  apply(simp add: IsDES_def prefix_closure_def prefix_def)
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      in meta_allE)
   apply(clarsimp)
   apply(case_tac xa)
   apply(rename_tac x xa fun1 fun2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x fun1 fun2)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x xa c)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(force)
  done

lemma SCP_Controller_Least_Restrictive_Direct_contained: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Sup {X. IsDES X
              \<and> DES_controllability SigmaUC P X
              \<and> DES_nonblockingness X
              \<and> X \<le> inf P S}
      \<in> {C. IsDES C
            \<and> DES_controllability SigmaUC P C
            \<and> DES_nonblockingness C
            \<and> DES_specification_satisfied (inf P S) C}"
  apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_DES_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_Cont_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_BF_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule Sup_Spec_contained)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(simp add: DES_specification_satisfied_def)
  done

lemma SCP_Controller_Least_Restrictive_Direct_contained2: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Sup {X. IsDES X
              \<and> DES_controllability SigmaUC P X
              \<and> DES_nonblockingness X
              \<and> X \<le> S}
      \<in> {C. IsDES C
            \<and> DES_controllability SigmaUC P C
            \<and> DES_nonblockingness C
            \<and> DES_specification_satisfied S C}"
  apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_DES_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_Cont_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_BF_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule Sup_Spec_contained)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(simp add: DES_specification_satisfied_def)
  done

definition SCP_Controller_Satisfactory :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Satisfactory P S \<Sigma>UC \<equiv>
  {C. IsDES C
    \<and> DES_specification_satisfied S (inf C P)
    \<and> DES_nonblockingness (inf C P)
    \<and> DES_controllability \<Sigma>UC P C}"

definition SCP_Closed_Loop_Satisfactory :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Closed_Loop_Satisfactory P S \<Sigma>UC \<equiv>
  {inf C P| C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}"

definition SCP_Controller_Least_Restrictive :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Least_Restrictive P S \<Sigma>UC \<equiv>
  {C. IsDES C
  \<and> DES_controllability \<Sigma>UC P C
  \<and> inf C P = Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC)
  \<and> inf C P \<in> SCP_Closed_Loop_Satisfactory P S \<Sigma>UC}"

lemma SCP_Closed_Loop_Satisfactory_implies_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> IsDES C
  \<Longrightarrow> inf C P \<in> SCP_Closed_Loop_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Satisfactory_def SCP_Closed_Loop_Satisfactory_def)
  apply(clarsimp)
  apply(rename_tac Ca)(*strict*)
  apply(rule_tac
      t="DES_controllability \<Sigma>UC P C"
      and s="DES_controllability \<Sigma>UC P (inf C P)"
      in ssubst)
   apply(rename_tac Ca)(*strict*)
   apply (rule DES_controllability_coincides_on_controller_and_closed_loop)
   apply(blast)
  apply(rename_tac Ca)(*strict*)
  apply(rule_tac
      t="DES_controllability \<Sigma>UC P (inf C P)"
      and s="DES_controllability \<Sigma>UC P (inf Ca P)"
      in ssubst)
   apply(rename_tac Ca)(*strict*)
   apply(force)
  apply(rename_tac Ca)(*strict*)
  apply (metis DES_controllability_infimum)
  done

definition SCP_Controller_Least_Restrictive_Simplified :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Least_Restrictive_Simplified P S \<Sigma>UC \<equiv>
  {C. IsDES C
  \<and> inf C P = Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC)}"

definition SCP_Closed_Loop_Satisfactory_Direct :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Closed_Loop_Satisfactory_Direct P S \<Sigma>UC \<equiv>
  {CL. IsDES CL
      \<and> CL \<le> P
      \<and> DES_controllability \<Sigma>UC P CL
      \<and> DES_nonblockingness CL
      \<and> DES_specification_satisfied S CL}"

definition SCP_Controller_Least_Restrictive_Direct :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC \<equiv>
  {C. IsDES C
  \<and> inf C P = Sup (SCP_Closed_Loop_Satisfactory_Direct P S \<Sigma>UC)}"

lemma SCP_Closed_Loop_Satisfactory_Direct_supremum_contained: "
  Sup (SCP_Closed_Loop_Satisfactory_Direct P S \<Sigma>UC) \<in> SCP_Closed_Loop_Satisfactory_Direct P S \<Sigma>UC"
  apply(unfold SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_DES_contained)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_Cont_contained)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_BF_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule Sup_Spec_contained)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  done

lemma SCP_Closed_Loop_Satisfactory_smaller_than_plant: "
  Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC) \<le> P"
  apply(simp add: SCP_Closed_Loop_Satisfactory_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma SCP_Closed_Loop_Satisfactory_supremum_contained: "
  IsDES P
  \<Longrightarrow> Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC) \<in> SCP_Closed_Loop_Satisfactory P S \<Sigma>UC"
  apply(subgoal_tac "Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC) \<le> P")
   prefer 2
   apply(rule SCP_Closed_Loop_Satisfactory_smaller_than_plant)
  apply(unfold SCP_Closed_Loop_Satisfactory_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (Sup {inf C P |C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}) P = Sup {inf C P |C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}")
   prefer 2
   apply (metis SCP_Closed_Loop_Satisfactory_def inf.absorb2 inf.commute)
  apply(rule_tac
      x="Sup {inf C P |C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}"
      in exI)
  apply(clarsimp)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(rule conjI)
   apply(rule Sup_DES_contained)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(rename_tac C)(*strict*)
   apply(simp add: inf_DES_ext_def)
   apply(rule infDES_preserves_IsDES)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule Sup_Spec_contained)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_BF_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rule Sup_Cont_contained)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(rename_tac C)(*strict*)
  apply (metis DES_controllability_infimum)
  done

corollary SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Simplified P S \<Sigma>UC = SCP_Controller_Least_Restrictive P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Least_Restrictive_Simplified_def SCP_Controller_Least_Restrictive_def)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rename_tac x)(*strict*)
   apply(rule SCP_Closed_Loop_Satisfactory_supremum_contained)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Controller_Satisfactory_def)
  apply(clarsimp)
  apply(rename_tac x C)(*strict*)
  apply (metis DES_controllability_coincides_on_controller_and_closed_loop)
  done

corollary SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Simplified P S \<Sigma>UC = SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Simplified_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Closed_Loop_Satisfactory_Direct_def)
   apply(subgoal_tac "inf x P \<in> {inf C P |C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "X" for X)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      and S="S"
      in SCP_Closed_Loop_Satisfactory_supremum_contained)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Closed_Loop_Satisfactory_Direct_def)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x C)(*strict*)
   apply(rule antisym)
    apply(rename_tac x C)(*strict*)
    apply(rule Sup_upper)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac x C)(*strict*)
     apply (metis infDES_preserves_IsDES inf_DES_ext_def)
    apply(rename_tac x C)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def)
    apply (metis DES_controllability_infimum)
   apply(rename_tac x C)(*strict*)
   apply(rule Sup_least)
   apply(rename_tac x C xa)(*strict*)
   apply(rule_tac
      t="inf C P"
      and s="Sup {inf C P |C. C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC}"
      in ssubst)
    apply(rename_tac x C xa)(*strict*)
    apply(force)
   apply(rename_tac x C xa)(*strict*)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule_tac
      x="xa"
      in exI)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x C xa)(*strict*)
    apply (metis inf.absorb2 inf.commute)
   apply(rename_tac x C xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac x C xa)(*strict*)
    apply (metis inf.absorb2 inf.commute)
   apply(rename_tac x C xa)(*strict*)
   apply (metis inf.absorb2 inf.commute)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(subgoal_tac "inf x P \<in> {C. IsDES C \<and> C \<le> P \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C \<and> DES_specification_satisfied S C}")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      and S="S"
      in SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
   apply(rename_tac x)(*strict*)
   apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(rename_tac x)(*strict*)
  apply(rule antisym)
   apply(rename_tac x)(*strict*)
   apply(rule Sup_upper)
   apply(rule_tac
      t="Sup {C. IsDES C \<and> C \<le> P \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C \<and> DES_specification_satisfied S C}"
      and s="inf x P"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp (no_asm))
   apply(rule_tac
      x="x"
      in exI)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply (metis DES_controllability_coinfimum)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="Sup {C. IsDES C \<and> C \<le> P \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C \<and> DES_specification_satisfied S C}"
      and s="inf x P"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule Sup_least)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x C)(*strict*)
  apply(rule Sup_upper)
  apply(clarsimp)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(rule conjI)
   apply(rename_tac x C)(*strict*)
   apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  apply(rename_tac x C)(*strict*)
  apply (metis DES_controllability_infimum)
  done

corollary SCP_Controller_Least_Restrictive_Direct_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(case_tac P)
  apply(rename_tac C set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac C Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(subgoal_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (DES SPECum Sm) CL}"
      in ssubst)
    apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac
      t="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (DES SPECum Sm) C}"
      and s="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> C \<le> (DES SPECum Sm)}"
      in ssubst)
    apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
    apply(rule antisym)
     apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
     apply(clarsimp)
     apply(rename_tac x)(*strict*)
     apply(simp add: DES_specification_satisfied_def)
    apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(simp add: DES_specification_satisfied_def)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   apply(fold SCP_Closed_Loop_Satisfactory_Direct_def)[1]
   apply(rule SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(clarsimp)
  apply(simp add: SCP_Controller_Satisfactory_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(rule DES_controllability_coinfimum)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(force)
  done

definition SCP_Controller_Least_Restrictive_Adapted_Specification :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC \<equiv>
  SCP_Controller_Least_Restrictive_Direct P (inf P S) \<Sigma>UC"

corollary SCP_Controller_Least_Restrictive_Adapted_Specification_is_equal_to_SCP_Controller_Least_Restrictive_Direct: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC = SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(rule_tac
      t="{CL. IsDES CL \<and> CL \<le> P \<and> DES_controllability \<Sigma>UC P CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf P S) CL}"
      and s="{CL. IsDES CL \<and> CL \<le> P \<and> DES_controllability \<Sigma>UC P CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied S CL}"
      in ssubst)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: DES_specification_satisfied_def)
   apply(simp add: DES_specification_satisfied_def)
   apply(clarsimp)
  apply(force)
  done

corollary SCP_Controller_Least_Restrictive__with_adapted_specification_is_equal_to__SCP_Controller_Least_Restrictive: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive P (inf P S) \<Sigma>UC = SCP_Controller_Least_Restrictive P S \<Sigma>UC"
  apply(rule_tac t="SCP_Controller_Least_Restrictive P (inf P S) \<Sigma>UC" and s="SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC" in ssubst)
   prefer 2
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_equal_to_SCP_Controller_Least_Restrictive_Direct SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct)
  apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def)
  apply (metis SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct)
  done

lemma SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule subset_trans)
   prefer 2
   apply(rule SCP_Controller_Least_Restrictive_Direct_SCP_Controller_Satisfactory)
   apply(force)
  apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_equal_to_SCP_Controller_Least_Restrictive_Direct order_refl)
  done

definition SCP_Uspace :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set set" where
  "SCP_Uspace \<Sigma>UC Pum Sm \<equiv>
  {A. A \<subseteq> prefix_closure Sm
      \<and> controllable_language A \<Sigma>UC Pum
      \<and> A = prefix_closure A
      \<and> A \<subseteq> prefix_closure (Sm \<inter> A)}"

definition SCP_Uu :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_Uu \<Sigma>UC Pum Sm \<equiv>
  \<Union> SCP_Uspace \<Sigma>UC Pum Sm"

definition SCP_Um :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_Um \<Sigma>UC Pum Sm \<equiv>
  Sm \<inter> SCP_Uu \<Sigma>UC Pum Sm"

definition SCP_Usol :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Usol P S \<Sigma>UC \<equiv>
  {C. IsDES C
  \<and> inf C P = DES
   (SCP_Uu \<Sigma>UC (des_langUM P) (des_langM S))
   (SCP_Um \<Sigma>UC (des_langUM P) (des_langM S))}"

definition SCP_UPu :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_UPu \<Sigma>UC Pum Pm Sm \<equiv>
  \<Union> SCP_Uspace \<Sigma>UC Pum (Pm \<inter> Sm)"

definition SCP_UPm :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_UPm \<Sigma>UC Pum Pm Sm \<equiv>
  Sm \<inter> Pm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm"

definition SCP_UPsol :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_UPsol P S \<Sigma>UC \<equiv>
  {C. C = DES
    (SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))
    (SCP_UPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))}"

definition SCP_Unmarked_Supremum_with_Precomputation :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Unmarked_Supremum_with_Precomputation P S \<Sigma>UC \<equiv>
  {DES Cum (des_langM S \<inter> des_langM P \<inter> Cum)| Cum.
    Cum = Sup {Aum. Aum \<subseteq> prefix_closure (des_langM P \<inter> des_langM S)
      \<and> controllable_language Aum \<Sigma>UC (des_langUM P)
      \<and> Aum = prefix_closure Aum
      \<and> Aum \<subseteq> prefix_closure (des_langM P \<inter> des_langM S \<inter> Aum)}}"

lemma SCP_Unmarked_Supremum1X_is_equal_to_SCP_Unmarked_Supremum2_hlp: "
  (\<And>x. x \<in> X \<Longrightarrow> prefix_closure x = x \<and> x \<subseteq> A)
  \<Longrightarrow> x \<in> X
  \<Longrightarrow> x \<subseteq> prefix_closure (A \<inter> Sup X)"
  apply (metis Sup_upper inf.absorb2 prefixSubsetnonblockingness_language2 subset_refl)
  done

corollary SCP_Unmarked_Supremum_with_Precomputation_equals_SCP_UPsol: "
  SCP_Unmarked_Supremum_with_Precomputation P S \<Sigma>UC = SCP_UPsol P S \<Sigma>UC"
  apply(simp add: SCP_Unmarked_Supremum_with_Precomputation_def SCP_UPsol_def Let_def SCP_UPu_def SCP_UPm_def SCP_Uspace_def)
  done

definition SCP_Mspace :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set set" where
  "SCP_Mspace \<Sigma>UC Pum Sm \<equiv>
  {A. controllable_language (prefix_closure A) \<Sigma>UC Pum
      \<and> A \<subseteq> Sm}"

definition SCP_Mm :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_Mm \<Sigma>UC Pum Sm \<equiv>
  \<Union> SCP_Mspace \<Sigma>UC Pum Sm"

definition SCP_Mu :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_Mu \<Sigma>UC Pum Sm \<equiv>
  prefix_closure (SCP_Mm \<Sigma>UC Pum Sm)"

definition SCP_Msol :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Msol P S \<Sigma>UC \<equiv>
  {C. IsDES C
   \<and> inf C P = DES
    (SCP_Mu \<Sigma>UC (des_langUM P) (des_langM S))
    (SCP_Mm \<Sigma>UC (des_langUM P) (des_langM S))}"

definition SCP_MPm :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_MPm \<Sigma>UC Pum Pm Sm \<equiv>
  \<Union> SCP_Mspace \<Sigma>UC Pum (Pm \<inter> Sm)"

definition SCP_MPu :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "SCP_MPu \<Sigma>UC Pum Pm Sm \<equiv>
  prefix_closure (SCP_MPm \<Sigma>UC Pum Pm Sm)"

definition SCP_MPsol :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_MPsol P S \<Sigma>UC \<equiv>
  {C. C = DES
    (SCP_MPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))
    (SCP_MPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))}"

definition SCP_Marked_Supremum_with_Precomputation :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Marked_Supremum_with_Precomputation P S \<Sigma>UC \<equiv>
  {DES (prefix_closure Cm) Cm| Cm.
    Cm = Sup {Am.
                controllable_language (prefix_closure Am) \<Sigma>UC (des_langUM P)
              \<and> Am \<subseteq> des_langM P
              \<and> Am \<subseteq> des_langM S}}"

corollary SCP_Marked_Supremum_with_Precomputation_equals_SCP_MPsol: "
  SCP_Marked_Supremum_with_Precomputation P S \<Sigma>UC = SCP_MPsol P S \<Sigma>UC"
  apply(simp add: SCP_Marked_Supremum_with_Precomputation_def SCP_MPsol_def Let_def SCP_MPu_def SCP_MPm_def SCP_Mspace_def)
  done

lemma SCP_UPu_pc: "
  SCP_UPu \<Sigma>UC L Lm B = prefix_closure (SCP_UPu \<Sigma>UC L Lm B)"
  apply(simp add: SCP_UPu_def)
  apply(rule preservePrec)
  apply(rename_tac Ba)(*strict*)
  apply(simp add: SCP_Uspace_def)
  done

lemma SCP_UPu_nb2: "
  SCP_UPu \<Sigma>UC L Lm B \<subseteq> prefix_closure (Lm \<inter> B \<inter> SCP_UPu \<Sigma>UC L Lm B)"
  apply(simp add: SCP_UPu_def)
  apply(rule preservePrecNonBlock)
  apply(rename_tac Ba)(*strict*)
  apply(simp add: SCP_Uspace_def)
  done

lemma LsupcontSIUM: "
  (append_alphabet (prefix_closure (\<Union> SCP_Uspace \<Sigma>UC L (Lm\<inter>B))) \<Sigma>UC) \<inter> L
  \<subseteq> prefix_closure (\<Union> SCP_Uspace \<Sigma>UC L (Lm\<inter>B))"
  apply(rule preserve_controllable_language)
  apply(rename_tac Ba)(*strict*)
  apply(simp add: SCP_Uspace_def controllable_language_def)
  done

lemma SCP_UPu_cont: "
  controllable_language (SCP_UPu \<Sigma>UC L Lm B) \<Sigma>UC L"
  apply(rule_tac
      s="prefix_closure(SCP_UPu \<Sigma>UC L Lm B)"
      and P="\<lambda>x. (controllable_language x \<Sigma>UC L)"
      in ssubst)
   defer
   apply(simp add: controllable_language_def SCP_UPu_def)
   apply(rule LsupcontSIUM)
  apply(rule SCP_UPu_pc)
  done

lemma LsupcontUM: "
  (append_alphabet (prefix_closure (\<Union> SCP_Uspace \<Sigma>UC L B)) \<Sigma>UC) \<inter> L
  \<subseteq> prefix_closure (\<Union> SCP_Uspace \<Sigma>UC L B)"
  apply(rule preserve_controllable_language)
  apply(rename_tac Ba)(*strict*)
  apply(simp add: SCP_Uspace_def controllable_language_def)
  done

lemma LsupcontM: "
  (append_alphabet (prefix_closure (\<Union> SCP_Mspace \<Sigma>UC L B)) \<Sigma>UC) \<inter> L
  \<subseteq> prefix_closure (\<Union> SCP_Mspace \<Sigma>UC L B)"
  apply(rule preserve_controllable_language)
  apply(rename_tac Ba)(*strict*)
  apply(simp add: SCP_Mspace_def controllable_language_def)
  done

lemma SCP_Uu_nb2: "
  nonblockingness_language (SCP_Uu \<Sigma>UC L B) B"
  apply(unfold SCP_Uu_def)
  apply(simp add: SCP_Uspace_def)
  apply(unfold nonblockingness_language_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(simp)
  done

lemma WellDefSolutionMRes: "
  Sup (SCP_Mspace \<Sigma>UC L B) \<in> SCP_Mspace \<Sigma>UC L B"
  apply(subgoal_tac "controllable_language (prefix_closure (\<Union>(SCP_Mspace \<Sigma>UC L B))) \<Sigma>UC L")
   prefer 2
   apply(simp add: controllable_language_def)
   apply(rule LsupcontM)
  apply(subgoal_tac "\<Union>(SCP_Mspace \<Sigma>UC L B) \<subseteq> B")
   prefer 2
   apply(simp add: SCP_Mspace_def)
   apply(blast)
  apply(simp add: SCP_Mspace_def)
  done

lemma WellDefSolutionUMRes: "
  Sup (SCP_Uspace \<Sigma>UC L B) \<in> SCP_Uspace \<Sigma>UC L B"
  apply(subgoal_tac "\<Union>SCP_Uspace \<Sigma>UC L B \<subseteq> prefix_closure B")
   prefer 2
   apply (simp add: SCP_Uspace_def prefix_def prefix_closure_def)
   apply(blast)
  apply(subgoal_tac "\<Union>SCP_Uspace \<Sigma>UC L B = prefix_closure (\<Union>SCP_Uspace \<Sigma>UC L B)")
   prefer 2
   apply(rule preservePrec)
   apply(rename_tac Ba)(*strict*)
   apply(simp add: SCP_Uspace_def)
  apply(subgoal_tac "controllable_language (\<Union>SCP_Uspace \<Sigma>UC L B) \<Sigma>UC L")
   prefer 2
   apply(simp add: controllable_language_def)
   apply(rule_tac
      t="\<Union>SCP_Uspace \<Sigma>UC L B"
      and s="prefix_closure (\<Union>SCP_Uspace \<Sigma>UC L B)"
      and P="\<lambda> x . (append_alphabet x \<Sigma>UC) \<inter> L \<subseteq> x"
      in ssubst)
    apply(simp)
   apply(rule LsupcontUM)
  apply(subgoal_tac "\<Union>SCP_Uspace \<Sigma>UC L B \<subseteq> prefix_closure (B \<inter> \<Union>SCP_Uspace \<Sigma>UC L B)")
   prefer 2
   apply(simp add: SCP_Uspace_def)
   apply(rule preservePrecNonBlock)
   apply(rename_tac Ba)(*strict*)
   apply(blast)
  apply (simp add: SCP_Uspace_def)
  done

lemma SCP_UPu_2_SCP_Uu: "
  Lm \<subseteq> L
  \<Longrightarrow> SCP_Uu \<Sigma>UC L (Lm \<inter> B) = SCP_UPu \<Sigma>UC L Lm B"
  apply(simp add: SCP_UPu_def SCP_Uu_def)
  done

corollary SCP_Msol_in_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Msol P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(simp add: IsDES_def SCP_Msol_def SCP_Controller_Satisfactory_def SCP_Mu_def SCP_Mm_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac C)(*strict*)
   apply(simp add: SCP_Mspace_def)
   apply(simp add: prefix_closure_def DES_specification_satisfied_def lesseqDES_def less_eq_DES_ext_def infDES_def inf_DES_ext_def)
   apply(simp add: DES_specification_satisfied_def DES_nonblockingness_def DES_controllability_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def infDES_def inf_DES_ext_def)
   apply(force)
  apply(rename_tac C)(*strict*)
  apply(simp add: SCP_Mspace_def)
  apply(subgoal_tac "\<Union>{A. ((controllable_language (prefix_closure A) \<Sigma>UC (des_langUM P)) \<and> (A \<subseteq> (des_langM S)))} \<in> {A. ((controllable_language (prefix_closure A) \<Sigma>UC (des_langUM P)) \<and> (A \<subseteq> (des_langM S)))}")
   apply(rename_tac C)(*strict*)
   prefer 2
   apply(fold SCP_Mspace_def)
   apply(rule WellDefSolutionMRes)
  apply(rename_tac C)(*strict*)
  apply(rule conjI)
   apply(rename_tac C)(*strict*)
   apply(simp add: prefix_closure_def DES_specification_satisfied_def DES_nonblockingness_def DES_controllability_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def infDES_def inf_DES_ext_def nonblockingness_language_def)
  apply(rename_tac C)(*strict*)
  apply(rule DES_controllability_coinfimum)
   apply(rename_tac C)(*strict*)
   apply(simp add: IsDES_def)
  apply(rename_tac C)(*strict*)
  apply(simp add: SCP_Mspace_def prefix_closure_def DES_specification_satisfied_def DES_nonblockingness_def DES_controllability_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def Let_def infDES_def inf_DES_ext_def nonblockingness_language_def)
  done

lemma UMRes_equals_MRes____SCP_Um_equals_SCP_Mm_subset1: "
  SCP_Um \<Sigma>UC L B \<subseteq> SCP_Mm \<Sigma>UC L B"
  apply(simp add: SCP_Um_def SCP_Mm_def SCP_Uu_def SCP_Mu_def)
  apply(rule_tac
      P="\<lambda>A. controllable_language (prefix_closure A) \<Sigma>UC L \<and> A \<subseteq> B"
      in supProveSubset)
   apply(simp add: SCP_Mspace_def)
  apply(rule conjI)
   apply(simp only: SCP_Uspace_def)
   apply(rule_tac
      P="\<lambda>A. A \<subseteq> prefix_closure B \<and> controllable_language A \<Sigma>UC L \<and> A = prefix_closure A \<and> A \<subseteq> prefix_closure (B \<inter> A)"
      in helpLem)
   apply(blast)
  apply(blast)
  done

lemma UMRes_equals_MRes____SCP_Um_equals_SCP_Mm_subset2: "
  SCP_Um \<Sigma>UC L B \<supseteq> SCP_Mm \<Sigma>UC L B"
  apply(simp add: SCP_Um_def SCP_Mm_def SCP_Uu_def SCP_Mu_def)
  apply(simp add: SCP_Mspace_def)
  apply(simp add: SCP_Uspace_def)
  apply(rule conjI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x X)(*strict*)
  apply(rule_tac
      x="prefix_closure X"
      in exI)
  apply(rule conjI)
   apply(rename_tac x X)(*strict*)
   apply(rule prefix_closure_preserves_subseteq)
   apply(blast)
  apply(rename_tac x X)(*strict*)
  apply(rule conjI)
   apply(rename_tac x X)(*strict*)
   apply(blast)
  apply(rename_tac x X)(*strict*)
  apply(rule conjI)
   apply(rename_tac x X)(*strict*)
   apply(rule prefix_closure_idempotent)
  apply(rename_tac x X)(*strict*)
  apply(rule conjI)
   apply(rename_tac x X)(*strict*)
   apply(rule prefix_closure_preserves_subseteq)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac x X)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac x X)(*strict*)
  apply(force)
  done

lemma UMRes_equals_MRes____SCP_Um_equals_SCP_Mm: "
  SCP_Um \<Sigma>UC L B = SCP_Mm \<Sigma>UC L B"
  apply(rule order_antisym)
   apply(metis UMRes_equals_MRes____SCP_Um_equals_SCP_Mm_subset1)
  apply(metis UMRes_equals_MRes____SCP_Um_equals_SCP_Mm_subset2)
  done

lemma UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu_subset1: "
  SCP_Uu \<Sigma>UC L B \<subseteq> SCP_Mu \<Sigma>UC L B"
  apply(simp only: SCP_Mu_def)
  apply(rule_tac
      A="SCP_Uu \<Sigma>UC L B"
      and B="prefix_closure (B \<inter> SCP_Uu \<Sigma>UC L B)"
      and C="prefix_closure (SCP_Mm \<Sigma>UC L B)"
      in subset_trans)
   apply(simp add: SCP_Uu_def)
   apply(rule preservePrecNonBlock)
   apply(rename_tac Ba)(*strict*)
   apply(simp add: SCP_Uspace_def)
  apply(rule prefix_closure_preserves_subseteq)
  apply(simp add: SCP_Mm_def)
  apply(rule_tac
      P="\<lambda>A. controllable_language (prefix_closure A) \<Sigma>UC L \<and> A \<subseteq> B"
      in supProveSubset)
   apply(simp add: SCP_Mspace_def)
  apply(rule conjI)
   apply(simp add: SCP_Uu_def)
   apply(simp only: SCP_Uspace_def)
   apply(rule_tac
      P="\<lambda>A. A \<subseteq> prefix_closure B \<and> controllable_language A \<Sigma>UC L \<and> A = prefix_closure A \<and> A \<subseteq> prefix_closure (B \<inter> A)"
      in helpLem)
   apply(blast)
  apply(blast)
  done

lemma UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu_subset2: "
  SCP_Uu \<Sigma>UC L B \<supseteq> SCP_Mu \<Sigma>UC L B"
  apply(simp add: SCP_Uu_def SCP_Mu_def SCP_Mm_def)
  apply(simp add: SCP_Uspace_def)
  apply(rule_tac
      P="\<lambda>A. A \<subseteq> prefix_closure B \<and> controllable_language A \<Sigma>UC L \<and> A = prefix_closure A \<and> A \<subseteq> prefix_closure (B \<inter> A)"
      in supProveSubset)
   apply(blast)
  apply(rule conjI)
   apply(rule prefix_closure_preserves_subseteq)
   apply(simp add: SCP_Mspace_def)
   apply(blast)
  apply(rule conjI)
   apply(simp only: controllable_language_def)
   apply(rule preserve_controllable_language)
   apply(rename_tac Ba)(*strict*)
   apply(simp add: controllable_language_def SCP_Mspace_def)
  apply(rule conjI)
   apply(rule prefix_closure_idempotent)
  apply(simp add: prefix_closure_def prefix_def SCP_Mspace_def)
  apply(clarsimp)
  apply(rename_tac x xa c)(*strict*)
  apply(rule_tac
      x="x@c"
      in exI)
  apply(force)
  done

lemma UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu: "
  SCP_Uu \<Sigma>UC L B = SCP_Mu \<Sigma>UC L B"
  apply(rule order_antisym)
   apply(metis UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu_subset1)
  apply(metis UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu_subset2)
  done

lemma UMRes_equals_MRes: "
  SCP_Um \<Sigma>UC L B = SCP_Mm \<Sigma>UC L B
  \<and> SCP_Uu \<Sigma>UC L B = SCP_Mu \<Sigma>UC L B"
  apply(rule conjI)
   apply(rule UMRes_equals_MRes____SCP_Um_equals_SCP_Mm)
  apply(rule UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu)
  done

corollary SCP_Usol_eq_SCP_Msol: "
  SCP_Usol P S \<Sigma>UC = SCP_Msol P S \<Sigma>UC"
  apply(simp add: SCP_Usol_def SCP_Msol_def infDES_def inf_DES_ext_def)
  apply(subgoal_tac "SCP_Um \<Sigma>UC (des_langUM P) (des_langM S) = SCP_Mm \<Sigma>UC (des_langUM P) (des_langM S) \<and> SCP_Uu \<Sigma>UC (des_langUM P) (des_langM S) = SCP_Mu \<Sigma>UC (des_langUM P) (des_langM S)")
   apply(blast)
  apply(rule UMRes_equals_MRes)
  done

lemma SCP_Usol_in_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Usol P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply (metis SCP_Msol_in_SCP_Controller_Satisfactory SCP_Usol_eq_SCP_Msol)
  done

lemma SIUMRes_makes_DES: "
  C= DES (SCP_UPu \<Sigma>UC Pum Pm Sm) (SCP_UPm \<Sigma>UC Pum Pm Sm)
  \<Longrightarrow> IsDES C"
  apply(simp add: IsDES_def)
  apply(rule conjI)
   apply(simp add: SCP_UPm_def)
  apply(rule sym)
  apply(rule SCP_UPu_pc)
  done

lemma SCP_UPsol_eq_SCP_Usol_hlp2_2: "
  SCP_UPu \<Sigma>UC Pum Pm Sm \<subseteq> SCP_Uu \<Sigma>UC Pum Sm"
  apply(simp add: SCP_Uu_def SCP_Uspace_def)
  apply(rule Sup_upper)
  apply(simp)
  apply(rule conjI)
   apply(simp add: SCP_UPu_def SCP_Uspace_def)
   apply(clarsimp)
   apply(rename_tac x X)(*strict*)
   apply(rule_tac
      A="prefix_closure (Pm \<inter> Sm \<inter> X)"
      in set_mp)
    apply(rename_tac x X)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(blast)
   apply(rename_tac x X)(*strict*)
   apply(rule_tac
      A="X"
      in set_mp)
    apply(rename_tac x X)(*strict*)
    apply(blast)
   apply(rename_tac x X)(*strict*)
   apply(blast)
  apply(rule conjI)
   apply(rule SCP_UPu_cont)
  apply(rule conjI)
   apply(rule SCP_UPu_pc)
  apply(subgoal_tac "((SCP_UPu \<Sigma>UC Pum Pm Sm) \<subseteq> (prefix_closure ((Pm \<inter> Sm) \<inter> (SCP_UPu \<Sigma>UC Pum Pm Sm))))")
   prefer 2
   apply(rule SCP_UPu_nb2)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x\<in> (prefix_closure ((Pm \<inter> Sm) \<inter> (SCP_UPu \<Sigma>UC Pum Pm Sm)))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_closure_def)
  apply(erule exE)
  apply(rename_tac x v)(*strict*)
  apply(force)
  done

lemma SCP_UPuInPum: "
  Pm \<subseteq> prefix_closure Pum
  \<Longrightarrow> Pum = prefix_closure Pum
  \<Longrightarrow> SCP_UPu \<Sigma>UC Pum Pm Sm \<subseteq> Pum"
  apply(simp add: SCP_UPu_def SCP_Uspace_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "prefix_closure (Pm \<inter> Sm) \<subseteq> Pum")
   apply(rename_tac x xa)(*strict*)
   apply(blast)
  apply(rename_tac x xa)(*strict*)
  apply(rule_tac
      P="\<lambda>x. ((prefix_closure (Pm \<inter> Sm)) \<subseteq> x)"
      and s="prefix_closure Pum"
      in ssubst)
   apply(rename_tac x xa)(*strict*)
   apply(blast)
  apply(rename_tac x xa)(*strict*)
  apply(rule prefix_closure_preserves_subseteq)
  apply(blast)
  done

lemma SCP_UPsol_eq_SCP_Usol_hlp1: "
  IsDES CI
  \<Longrightarrow> CI = DES CIum CIm
  \<Longrightarrow> IsDES CU
  \<Longrightarrow> CU = DES CUum CUm
  \<Longrightarrow> IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> CI \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> CU \<in> SCP_Usol P S \<Sigma>UC
  \<Longrightarrow> CIum \<inter> Pum = CUum \<inter> Pum
  \<Longrightarrow> CIm \<inter> Pm = CUm \<inter> Pm"
  apply(simp add: SCP_Usol_def SCP_UPsol_def SCP_UPm_def SCP_Um_def)
  apply(clarify)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rule_tac
      P="\<lambda>x. Sm \<inter> Pm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pm = Sm \<inter> x"
      and s="SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pum"
      in ssubst)
   apply(blast)
  apply(subgoal_tac "Sm \<inter> Pm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pm = Sm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pum")
   apply(blast)
  apply(subgoal_tac "(Sm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm) \<inter> Pm = (Sm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm) \<inter> Pum")
   apply(blast)
  apply(rule equalityI)
   defer
   apply(blast)
  apply(simp add: IsDES_def)
  apply(force)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp1: "
  a \<inter> Pum \<subseteq> SCP_UPu \<Sigma>UC Pum Pm Sm
  \<Longrightarrow> b \<subseteq> a
  \<Longrightarrow> Pm \<subseteq> Pum
  \<Longrightarrow> b \<inter> Pm \<subseteq> SCP_UPu \<Sigma>UC Pum Pm Sm"
  apply(rule_tac
      A="b \<inter> Pm"
      and B="a \<inter> Pum"
      and C="(SCP_UPu \<Sigma>UC Pum Pm Sm)"
      in subset_trans)
   apply(simp add: IsDES_def)
   apply(blast)
  apply(simp)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2: "
  b \<inter> Pm \<subseteq> Sm
  \<Longrightarrow> a \<inter> Pum \<subseteq> prefix_closure (b \<inter> Pm)
  \<Longrightarrow> Pum = prefix_closure Pum
  \<Longrightarrow> a = prefix_closure a
  \<Longrightarrow> Pm \<subseteq> Pum
  \<Longrightarrow> b \<subseteq> a
  \<Longrightarrow> controllable_language (a \<inter> Pum) \<Sigma>UC Pum
  \<Longrightarrow> a \<inter> Pum \<subseteq> SCP_UPu \<Sigma>UC Pum Pm Sm"
  apply(simp add: SCP_UPu_def)
  apply(rule Sup_upper)
  apply(simp add: SCP_Uspace_def)
  apply(rule conjI)
   apply(rule_tac
      a="a"
      and b="b"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_1)
    apply(simp)+
  apply(rule conjI)
   apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_2)
    apply(simp)+
  apply(rule_tac
      a="a"
      and b="b"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_3)
       apply(simp+)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_hlp1: "
  SCP_UPm \<Sigma>UC Pum Pm Sm \<inter> Pm \<subseteq> Sm"
  apply(simp add: SCP_UPm_def)
  apply(blast)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_hlp2_1: "
  SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pum
  \<subseteq> prefix_closure (Sm \<inter> SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pm)"
  apply(rule_tac
      B="SCP_UPu \<Sigma>UC Pum Pm Sm"
      in subset_trans)
   apply(blast)
  apply(rule_tac
      B="prefix_closure((Pm\<inter> Sm)\<inter>(SCP_UPu \<Sigma>UC Pum Pm Sm))"
      in subset_trans)
   apply(rule SCP_UPu_nb2)
  apply(rule prefix_closure_preserves_subseteq)
  apply(blast)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_hlp2: "
  SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pum
  \<subseteq> prefix_closure (SCP_UPm \<Sigma>UC Pum Pm Sm \<inter> Pm)"
  apply(simp add: SCP_UPm_def)
  apply(rule_tac
      B="prefix_closure (Sm \<inter> (SCP_UPu \<Sigma>UC Pum Pm Sm) \<inter> Pm)"
      in subset_trans)
   apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_hlp2_1)
  apply(rule prefix_closure_preserves_subseteq)
  apply(simp add: IsDES_def)
  apply(force)
  done

lemma SCP_UPu_computes_SCP_UPsol: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> A = SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)
  \<Longrightarrow> B = (des_langM S) \<inter> (des_langM P) \<inter> (SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))
  \<Longrightarrow> (DES A B) \<in> SCP_UPsol P S \<Sigma>UC"
  apply(simp add: SCP_UPsol_def)
  apply(simp add: SCP_UPm_def)
  done

corollary SCP_UPsol_in_SCP_Controller_Satisfactory: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_UPsol P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(subgoal_tac "IsDES C")
   apply(rename_tac C)(*strict*)
   prefer 2
   apply(rule SIUMRes_makes_DES)
   apply(simp add: SCP_UPsol_def)
  apply(rename_tac C)(*strict*)
  apply(case_tac S)
  apply(rename_tac C set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac C SPECum Sm)(*strict*)
  apply(case_tac P)
  apply(rename_tac C SPECum Sm set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_def SCP_UPsol_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(subgoal_tac "DES_nonblockingness (DES (SCP_UPu \<Sigma>UC Pum Pm Sm \<inter> Pum) (SCP_UPm \<Sigma>UC Pum Pm Sm \<inter> Pm))")
   apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
   prefer 2
   apply(simp add: DES_nonblockingness_def nonblockingness_language_def des_langUM_def des_langM_def)
   apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_hlp2)
  apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
  apply(rule conjI)
   apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
   apply(rule DES_specification_satisfied_from_DES_nonblockingness_and_marked_satisfaction)
     apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
     apply(force)
    apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
    apply(simp add: des_langM_def)
    apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_hlp1)
   apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
   apply(force)
  apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
  apply(rule conjI)
   apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
   apply(force)
  apply(rename_tac C SPECum Sm Pum Pm)(*strict*)
  apply(simp add: DES_controllability_def des_langUM_def)
  apply(rule SCP_UPu_cont)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_hlp1: "
  IsDES C
  \<Longrightarrow> C = DES Cum Cm
  \<Longrightarrow> IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> Cum \<subseteq> Pum"
  apply(simp add: SCP_UPsol_def)
  apply(simp add: SCP_UPu_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(erule conjE)+
  apply(simp add: SCP_Uspace_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(rule_tac
      A="(prefix_closure (Pm \<inter> Sm))"
      in set_mp)
   apply(rename_tac x xa)(*strict*)
   apply(rule_tac
      B="(prefix_closure Pum)"
      in subset_trans)
    apply(rename_tac x xa)(*strict*)
    apply(rule prefix_closure_preserves_subseteq)
    apply(simp add: IsDES_def)
    apply(blast)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: IsDES_def)
  apply(rename_tac x xa)(*strict*)
  apply(blast)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_hlp2: "
  IsDES C
  \<Longrightarrow> C = DES Cum Cm
  \<Longrightarrow> IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> Cm \<subseteq> Pm"
  apply(simp add: SCP_UPsol_def)
  apply(simp add: SCP_UPm_def SCP_UPu_def)
  apply(blast)
  done

lemma SCP_MPu_pc: "
  SCP_MPu \<Sigma>UC L Lm B = prefix_closure (SCP_MPu \<Sigma>UC L Lm B)"
  apply(simp add: SCP_MPu_def)
  apply (metis prefix_closure_idempotent)
  done

corollary SCP_MPsol_equals_SCP_UPsol: "
  SCP_MPsol P S \<Sigma>UC = SCP_UPsol P S \<Sigma>UC"
  apply(subgoal_tac "\<And>C. (C \<in> SCP_MPsol P S \<Sigma>UC) = (C \<in> SCP_UPsol P S \<Sigma>UC)")
   apply(force)
  apply(rename_tac C)(*strict*)
  apply(simp add: SCP_MPsol_def SCP_UPsol_def)
  apply(case_tac C)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Cum Cm)(*strict*)
  apply(subgoal_tac "SCP_MPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S) = SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)")
   apply(rename_tac Cum Cm)(*strict*)
   apply(subgoal_tac "SCP_MPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S) = SCP_UPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)")
    apply(rename_tac Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Cum Cm)(*strict*)
   apply(thin_tac "SCP_MPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S) = SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)")
   apply(rename_tac Cum Cm)(*strict*)
   apply(simp add: SCP_MPm_def SCP_UPm_def SCP_UPu_def)
   apply (metis Int_commute SCP_Mm_def SCP_Mu_def SCP_Um_def SCP_Uu_def UMRes_equals_MRes UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu)
  apply(rename_tac Cum Cm)(*strict*)
  apply(simp add: SCP_MPm_def SCP_UPm_def SCP_UPu_def)
  apply (metis SCP_Mm_def SCP_Mu_def SCP_MPm_def SCP_MPu_def SCP_Uu_def UMRes_equals_MRes____SCP_Uu_equals_SCP_Mu)
  done

definition SCP_Controller_Satisfactory_Maximal_Closed_Loop :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC \<equiv>
  {C. \<forall>C'.
  C' \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<longrightarrow> inf C' P \<le> inf C P}"

lemma useSCP_Controller_Satisfactory_Maximal_Closed_Loop: "
  IsDES C
  \<Longrightarrow> IsDES C'
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C' \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> inf C' P \<le> inf C P"
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  done

corollary SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop: "
  IsDES P
  \<Longrightarrow> SCP_UPsol P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(case_tac P)
  apply(rename_tac C set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac C Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(clarsimp)
  apply(rename_tac C')(*strict*)
  apply(simp add: SCP_UPsol_def SCP_UPm_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(case_tac C')
  apply(rename_tac C' fun1 fun2)(*strict*)
  apply(clarsimp)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(rename_tac C'um C'm)
  apply(rename_tac C'um C'm)(*strict*)
  apply(subgoal_tac "C'um \<inter> Pum \<subseteq> SCP_UPu \<Sigma>UC Pum Pm Sm")
   apply(rename_tac C'um C'm)(*strict*)
   apply(rule conjI)
    apply(rename_tac C'um C'm)(*strict*)
    apply(force)
   apply(rename_tac C'um C'm)(*strict*)
   apply(rule conjI)
    apply(rename_tac C'um C'm)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def DES_specification_satisfied_def)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C'um C'm)(*strict*)
   apply(rule_tac
      a="C'um"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp1)
     apply(rename_tac C'um C'm)(*strict*)
     apply(force)
    apply(rename_tac C'um C'm)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C'um C'm)(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rename_tac C'um C'm)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rule_tac
      a="C'um"
      and b="C'm"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2)
        apply(rename_tac C'um C'm)(*strict*)
        apply(simp add: IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def DES_specification_satisfied_def DES_nonblockingness_def nonblockingness_language_def DES_controllability_def)+
  apply(rename_tac Pum Pm SPECum Sm C'um C'm)(*strict*)
  apply(rule controllable_language_infimum)
  apply(force)
  done

lemma SCP_UPsol_smallerThan_SCP_Usol: "
  IsDES CI
  \<Longrightarrow> CI = DES CIum CIm
  \<Longrightarrow> IsDES CU
  \<Longrightarrow> CU = DES CUum CUm
  \<Longrightarrow> IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> CI \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> CU \<in> SCP_Usol P S \<Sigma>UC
  \<Longrightarrow> CIum \<inter> Pum \<subseteq> CUum \<inter> Pum
  \<and> CIm \<inter> Pm \<subseteq> CUm \<inter> Pm"
  apply(subgoal_tac "CUum \<inter> Pum \<subseteq> CIum \<inter> Pum \<and> CUm \<inter> Pm \<subseteq> CIm \<inter> Pm")
   apply(subgoal_tac "CIum \<inter> Pum = CUum \<inter> Pum")
    apply(rule conjI)
     apply(blast)
    apply(subgoal_tac "CIm \<inter> Pm = CUm \<inter> Pm")
     apply(blast)
    apply(rule_tac
      CI="CI"
      and \<Sigma>UC="\<Sigma>UC"
      and CIum="CIum"
      and CU="CU"
      and P="P"
      and S="S"
      and SPECum="SPECum"
      and Sm="Sm"
      and CUum="CUum"
      in SCP_UPsol_eq_SCP_Usol_hlp1)
              apply(blast)
             apply(blast)
            apply(blast)
           apply(blast)
          apply(blast)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(clarsimp)
   apply(simp add: SCP_Usol_def SCP_UPsol_def)
   apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rule_tac
      P="\<lambda>x. x = SCP_Uu \<Sigma>UC Pum Sm"
      and s="SCP_UPu \<Sigma>UC Pum Pm Sm"
      in ssubst)
    apply(subgoal_tac "SCP_UPu \<Sigma>UC Pum Pm Sm \<subseteq> Pum")
     apply(blast)
    apply(rule SCP_UPuInPum)
     apply(simp add: IsDES_def)
    apply(simp add: IsDES_def)
   apply(rule equalityI)
    apply(rule_tac SCP_UPsol_eq_SCP_Usol_hlp2_2)
   apply(blast)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and C'="CU"
      and C="CI"
      and S="S"
      in useSCP_Controller_Satisfactory_Maximal_Closed_Loop)
      apply(force)
     apply(force)
    prefer 3
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
    apply(rule_tac
      P="P"
      and S="S"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
    apply(force)
   apply(force)
  apply(rule_tac
      A="SCP_Usol P S \<Sigma>UC"
      in set_mp)
   apply(rule_tac
      P="P"
      and S="S"
      in SCP_Usol_in_SCP_Controller_Satisfactory)
    apply(force)
   apply(force)
  apply(force)
  done

lemma SCP_UPsol_eq_SCP_Usol: "
  IsDES CI
  \<Longrightarrow> CI = DES CIum CIm
  \<Longrightarrow> IsDES CU
  \<Longrightarrow> CU = DES CUum CUm
  \<Longrightarrow> IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> CI \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> CU \<in> SCP_Usol P S \<Sigma>UC
  \<Longrightarrow> inf CI P = inf CU P"
  apply(subgoal_tac "(CIum \<inter> Pum \<subseteq> CUum \<inter> Pum) \<and> (CIm \<inter> Pm \<subseteq> CUm \<inter> Pm)")
   prefer 2
   apply(rule_tac
      CI="CI"
      and P="P"
      and S="S"
      and CU="CU"
      in SCP_UPsol_smallerThan_SCP_Usol)
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
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      C'="CU"
      and P="P"
      and S="S"
      in useSCP_Controller_Satisfactory_Maximal_Closed_Loop)
      apply(force)
     apply(force)
    apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
     apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
     apply(force)
    apply(force)
   apply(rule_tac
      A="SCP_Usol P S \<Sigma>UC"
      in set_mp)
    apply(rule SCP_Usol_in_SCP_Controller_Satisfactory)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)+
  apply(subgoal_tac "CIum \<inter> Pum = CUum \<inter> Pum")
   prefer 2
   apply(blast)
  apply(rule conjI)
   apply(blast)
  apply(blast)
  done

corollary SCP_Usol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Usol P S \<Sigma>UC \<subseteq> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(subgoal_tac "IsDES C")
   apply(rename_tac C)(*strict*)
   prefer 2
   apply(simp add: SCP_Usol_def)
  apply(rename_tac C)(*strict*)
  apply(case_tac C)
  apply(rename_tac C set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac C Cum Cm)(*strict*)
  apply(case_tac P)
  apply(rename_tac C Cum Cm set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C Cum Cm Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac C Cum Cm Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "\<exists>xum xm. IsDES (DES xum xm) \<and> (DES xum xm) \<in> SCP_UPsol P S \<Sigma>UC")
   apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      x="SCP_UPu \<Sigma>UC Pum Pm Sm"
      in exI)
   apply(rule_tac
      x="SCP_UPm \<Sigma>UC Pum Pm Sm"
      in exI)
   apply(rule conjI)
    apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
    apply(simp add: IsDES_def)
    apply(rule conjI)
     apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
     apply(simp add: SCP_UPm_def)
    apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
    apply(rule sym)
    apply(rule SCP_UPu_pc)
   apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(simp add: SCP_UPsol_def)
  apply(rename_tac C Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(erule exE)
  apply(erule exE)
  apply(rename_tac xum xm)(*strict*)
  apply(subgoal_tac "(DES xum xm) \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC")
   apply(rename_tac xum xm)(*strict*)
   prefer 2
   apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
    apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
    apply(rename_tac xum xm)(*strict*)
    apply(force)
   apply(rename_tac xum xm)(*strict*)
   apply(force)
  apply(rename_tac xum xm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac xum xm)(*strict*)
   prefer 2
   apply(rule_tac
      CU="C"
      and CI="DES xum xm"
      and P="P"
      and S="S"
      in SCP_UPsol_eq_SCP_Usol)
            apply(rename_tac xum xm)(*strict*)
            apply(force)
           apply(rename_tac xum xm)(*strict*)
           apply(force)
          apply(rename_tac xum xm)(*strict*)
          apply(force)
         apply(rename_tac xum xm)(*strict*)
         apply(force)
        apply(rename_tac xum xm)(*strict*)
        apply(force)
       apply(rename_tac xum xm)(*strict*)
       apply(force)
      apply(rename_tac xum xm)(*strict*)
      apply(force)
     apply(rename_tac xum xm)(*strict*)
     apply(force)
    apply(rename_tac xum xm)(*strict*)
    apply(force)
   apply(rename_tac xum xm)(*strict*)
   apply(force)
  apply(rename_tac xum xm)(*strict*)
  apply(simp only: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(force)
  done

lemma SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop: "
  IsDES P
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<Longrightarrow> IsDES C
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(clarsimp)
  apply(rename_tac C')(*strict*)
  apply(rule_tac
      t="Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}"
      and s="inf C (DES Pum Pm)"
      in ssubst)
   apply(rename_tac C')(*strict*)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(simp (no_asm) add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(subgoal_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}"
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(rule_tac
      t="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}"
      and s="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> C \<le> (inf (DES Pum Pm) (DES SPECum Sm))}"
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(rule antisym)
     apply(rename_tac C')(*strict*)
     apply(clarsimp)
     apply(rename_tac C' x)(*strict*)
     apply(simp add: DES_specification_satisfied_def)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(rename_tac C')(*strict*)
    apply(simp add: DES_specification_satisfied_def)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C')(*strict*)
   apply(fold SCP_Closed_Loop_Satisfactory_Direct_def)[1]
   apply(rule SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(thin_tac "inf C (DES Pum Pm) = Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}")
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) \<in> SCP_Closed_Loop_Satisfactory_Direct (DES Pum Pm) (inf (DES Pum Pm) (DES SPECum Sm)) \<Sigma>UC")
   apply(rename_tac C')(*strict*)
   apply(clarsimp)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(case_tac C)
    apply(rename_tac C' fun1 fun2)(*strict*)
    apply(rename_tac Cum Cm)
    apply(rename_tac C' Cum Cm)(*strict*)
    apply(case_tac C')
    apply(rename_tac C' Cum Cm fun1 fun2)(*strict*)
    apply(rename_tac C'um C'm)
    apply(rename_tac C' Cum Cm C'um C'm)(*strict*)
    apply(clarsimp)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def DES_controllability_def DES_nonblockingness_def DES_specification_satisfied_def controllable_language_def)
    apply(simp add: IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def nonblockingness_language_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis Int_commute le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply (metis prefix_closure_intersection3)
   apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
   apply(rule conjI)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(rule DES_controllability_infimum)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def DES_controllability_def DES_nonblockingness_def DES_specification_satisfied_def controllable_language_def)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<le> inf C (DES Pum Pm)")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}"
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) = Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}")
   apply(rename_tac C')(*strict*)
   apply(rule Sup_upper)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C (DES Pum Pm) = Sup {CL. IsDES CL \<and> CL \<le> DES Pum Pm \<and> DES_controllability \<Sigma>UC (DES Pum Pm) CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) CL}")
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
  apply(rename_tac C')(*strict*)
  apply(clarsimp)
  apply(case_tac C')
  apply(rename_tac C' fun1 fun2)(*strict*)
  apply(rename_tac C'um C'm)
  apply(rename_tac C' C'um C'm)(*strict*)
  apply(clarsimp)
  apply(rename_tac C'um C'm)(*strict*)
  apply(case_tac C)
  apply(rename_tac C'um C'm fun1 fun2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  done

corollary SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop: "
  IsDES P
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC \<subseteq>
  SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(case_tac P)
  apply(rename_tac C set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac C Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "IsDES C \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC")
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule context_conjI)
    apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def)
   apply(rule_tac
      A="SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
      in set_mp)
    apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
    apply(rule_tac
      P="P"
      and S="S"
      in SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory)
    apply(force)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(rule_tac
      P="P"
      and S="S"
      in SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
     apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac C Pum Pm SPECum Sm)(*strict*)
  apply(force)
  done

lemma SCP_Controller_Satisfactory_Maximal_Closed_Loop_closed_under_intersection_with_plant: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> IsDES C
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C' = inf C P
  \<Longrightarrow> IsDES C'
  \<and> C' \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C' \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(case_tac C')
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac C)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(rename_tac C1um C1m C2um C2m)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(rule conjI)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(simp add: IsDES_def sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(clarsimp)
   apply(rename_tac C2um C2m)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac C2um C2m)(*strict*)
    apply(clarsimp)
    apply(rename_tac C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C2um C2m)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac C2um C2m)(*strict*)
    apply(clarsimp)
    apply(rename_tac C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C2um C2m)(*strict*)
   apply (metis SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_2)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(rule conjI)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(rule conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply (metis infDES_preserves_IsDES inf_DES_ext_def)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(rule DES_controllability_infimum)
   apply(force)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  done

definition SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC \<equiv>
  {C. \<forall>C'.
  C' \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<longrightarrow> C' \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<longrightarrow> C' < C
  \<longrightarrow> inf C' P < inf C P}"

corollary SCP_Controller_Satisfactory_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller: "
  IsDES P
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<le> P
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(clarsimp)
  apply(rename_tac C')(*strict*)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(case_tac C)
  apply(rename_tac C' fun1 fun2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac C' Cum Cm)(*strict*)
  apply(case_tac P)
  apply(rename_tac C' Cum Cm fun1 fun2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac C' Cum Cm Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac C' Cum Cm Pum Pm fun1 fun2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac C' Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(case_tac C')
  apply(rename_tac C' Cum Cm Pum Pm SPECum Sm fun1 fun2)(*strict*)
  apply(rename_tac C'um C'm)
  apply(rename_tac C' Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
  apply(rule conjI)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
   apply (metis Int_absorb1 Int_commute subset_trans)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
  apply(rule conjI)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
   apply (metis Int_absorb1 Int_commute subset_trans)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm C'um C'm)(*strict*)
  apply (metis Int_absorb1 Int_commute subset_trans)
  done

theorem SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm SPECum Sm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(rule SCP_Controller_Satisfactory_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(rule SCP_UPsol_in_SCP_Controller_Satisfactory)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rule conjI)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(rule_tac
      P="P"
      and S="S"
      and C="C"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_hlp1)
         apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(rule_tac
      P="P"
      and S="S"
      and C="C"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_hlp2)
        apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(force)
  done

lemma SCP_UPsol_Is_Optimal: "
  IsDES C
  \<Longrightarrow> IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(case_tac C)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Cum Cm)(*strict*)
  apply(case_tac P)
  apply(rename_tac Cum Cm set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Cum Cm Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Cum Cm Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(rule conjI)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and C="C"
      and P="P"
      and S="S"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
      apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
      apply(blast)
     apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
     apply(blast)
    apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
    apply(blast)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(rule conjI)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
    apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
    apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
    apply(blast)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(blast)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(rule_tac
      A="SCP_UPsol P S \<Sigma>UC"
      in set_mp)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac SCP_UPsol_in_SCP_Controller_Satisfactory)
    apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
    apply(blast)
   apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
   apply(blast)
  apply(rename_tac Cum Cm Pum Pm SPECum Sm)(*strict*)
  apply(blast)
  done

lemma Sound_Language_Computation: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> C = DES (SCP_UPu \<Sigma>UC Pum Pm Sm) (SCP_UPm \<Sigma>UC Pum Pm Sm)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule context_conjI)
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and C="C"
      and Pum="Pum"
      and Pm="Pm"
      and Sm="Sm"
      in SIUMRes_makes_DES)
   apply(force)
  apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and C="C"
      and P="P"
      and S="S"
      in SCP_UPsol_Is_Optimal)
     apply(blast)
    apply(blast)
   apply(force)
  apply(simp add: SCP_UPsol_def)
  done

lemma Sound_Language_Computation2: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> C = DES (SCP_MPu \<Sigma>UC Pum Pm Sm) (SCP_MPm \<Sigma>UC Pum Pm Sm)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(rule Sound_Language_Computation)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="DES Pum Pm"
      and S="DES SPECum Sm"
      and \<Sigma>UC="\<Sigma>UC"
      in SCP_MPsol_equals_SCP_UPsol)
  apply(simp add: SCP_MPsol_def SCP_UPsol_def)
  done

lemma unique_SMSOL_hlp: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> IsDES C1
  \<Longrightarrow> IsDES C2
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C1 < C2
  \<Longrightarrow> Q"
  apply(thin_tac "C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC")
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(erule_tac
      x="C1"
      in allE)+
  apply(erule impE)+
   apply(force)
  apply(erule impE)+
   apply(force)
  apply(thin_tac "C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop (DES Pum Pm) (DES SPECum Sm) \<Sigma>UC")
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(erule_tac
      x="C2"
      in allE)+
  apply(erule impE)+
   apply(force)
  apply(simp add: SCP_Controller_Satisfactory_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(case_tac C1)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac C2)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac C1um C1m C2um C2m)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(force)
  done

lemma sup_of_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_solutions_is_SCP_Controller_Satisfactory_Maximal_Closed_Loop_solution: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> IsDES C1
  \<Longrightarrow> IsDES C2
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C3 = sup C1 C2
  \<Longrightarrow> IsDES C3
  \<and> C3 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C3 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC"
  apply(case_tac C1)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac C2)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(rename_tac C1um C1m C2um C2m)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(rule conjI)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(simp add: IsDES_def sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(clarsimp)
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(clarsimp)
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply (metis prefix_closure_preserves_union)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(rule conjI)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def IsDES_def DES_specification_satisfied_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac C1um C1m C2um C2m)(*strict*)
     apply(force)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(rule conjI)
     apply(rename_tac C1um C1m C2um C2m)(*strict*)
     apply(force)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(rule prefix_closedness_closed_under_union)
     apply(rename_tac C1um C1m C2um C2m)(*strict*)
     apply(force)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def IsDES_def DES_specification_satisfied_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac C1um C1m C2um C2m)(*strict*)
     apply(force)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    apply(simp add: DES_nonblockingness_def nonblockingness_language_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(erule disjE)
     apply(rename_tac C1um C1m C2um C2m x)(*strict*)
     apply(force)
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(simp add: des_langUM_def DES_controllability_def controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
   apply(clarsimp)
   apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
   apply(erule disjE)
    apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
    apply(blast)
   apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
   apply(subgoal_tac "v@[s]\<in> C2um")
    apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
   apply(rule_tac
      A="{w. \<exists>v\<in> C2um \<inter> Pum. \<exists>s\<in> \<Sigma>UC. w = v @ [s]} \<inter> Pum"
      in set_mp)
    apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
    apply(blast)
   apply(rename_tac C1um C1m C2um C2m v s)(*strict*)
   apply(force)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(rename_tac C1um C1m C2um C2m C')(*strict*)
  apply(erule_tac
      x="C'"
      in allE)+
  apply(clarsimp)
  apply(case_tac C')
  apply(rename_tac C1um C1m C2um C2m C' fun1 fun2)(*strict*)
  apply(rename_tac C'1 C'2)
  apply(rename_tac C1um C1m C2um C2m C' C'1 C'2)(*strict*)
  apply(clarsimp)
  apply(rename_tac C1um C1m C2um C2m C'1 C'2)(*strict*)
  apply(force)
  done

theorem SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_smaller_than_plant: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> IsDES C
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C \<le> P"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      C="C"
      and P="P"
      and S="S"
      in SCP_Controller_Satisfactory_Maximal_Closed_Loop_closed_under_intersection_with_plant)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(erule_tac
      x="inf C (DES Pum Pm)"
      in allE)
  apply(erule impE)
   apply(force)
  apply(erule impE)
   apply(force)
  apply(case_tac "C \<le> DES Pum Pm")
   apply(force)
  apply(erule impE)
   apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(clarsimp)
   apply(case_tac C)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(rename_tac C1 C2)
   apply(rename_tac C1 C2)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(subgoal_tac "False")
   apply(force)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  done

theorem unique_SMSOL: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> IsDES C1
  \<Longrightarrow> IsDES C2
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C1 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC
  \<Longrightarrow> C1 = C2"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac "C1<C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac
      P="P"
      and ?C1.0="C1"
      and ?C2.0="C2"
      and S="S"
      in unique_SMSOL_hlp)
               apply(rename_tac Pum Pm SPECum Sm)(*strict*)
               apply(force)
              apply(rename_tac Pum Pm SPECum Sm)(*strict*)
              apply(force)
             apply(rename_tac Pum Pm SPECum Sm)(*strict*)
             apply(force)
            apply(rename_tac Pum Pm SPECum Sm)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm SPECum Sm)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac "C2<C1")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(rule_tac
      P="P"
      and ?C1.0="C2"
      and ?C2.0="C1"
      and S="S"
      in unique_SMSOL_hlp)
               apply(rename_tac Pum Pm SPECum Sm)(*strict*)
               apply(force)
              apply(rename_tac Pum Pm SPECum Sm)(*strict*)
              apply(force)
             apply(rename_tac Pum Pm SPECum Sm)(*strict*)
             apply(force)
            apply(rename_tac Pum Pm SPECum Sm)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm SPECum Sm)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      and ?C1.0="C1"
      and ?C2.0="C2"
      in sup_of_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_solutions_is_SCP_Controller_Satisfactory_Maximal_Closed_Loop_solution)
               apply(rename_tac Pum Pm SPECum Sm)(*strict*)
               apply(force)
              apply(rename_tac Pum Pm SPECum Sm)(*strict*)
              apply(force)
             apply(rename_tac Pum Pm SPECum Sm)(*strict*)
             apply(force)
            apply(rename_tac Pum Pm SPECum Sm)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm SPECum Sm)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac "C1=C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "C2 < sup C1 C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(simp add: sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(case_tac C1)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(case_tac C2)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(rename_tac C1um C1m C2um C2m)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "C1m \<subseteq> C2m")
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(clarsimp)
   apply(rename_tac C1um C1m C2um C2m x)(*strict*)
   apply(subgoal_tac "C1um \<subseteq> C2um")
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m x)(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rename_tac C1um C1m C2um C2m x xa)(*strict*)
   apply (metis UnCI)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "C1 < sup C1 C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(simp add: sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(case_tac C1)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(case_tac C2)
   apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
   apply(rename_tac C1um C1m C2um C2m)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "C2m \<subseteq> C1m")
    apply(rename_tac C1um C1m C2um C2m)(*strict*)
    prefer 2
    apply(blast)
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   apply(clarsimp)
   apply(rename_tac C1um C1m C2um C2m x)(*strict*)
   apply(subgoal_tac "C2um \<subseteq> C1um")
    apply(rename_tac C1um C1m C2um C2m x)(*strict*)
    apply(force)
   apply(rename_tac C1um C1m C2um C2m x)(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rename_tac C1um C1m C2um C2m x xa)(*strict*)
   apply (metis UnCI)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      and ?C1.0="C1"
      and ?C2.0="C2"
      in sup_of_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_solutions_is_SCP_Controller_Satisfactory_Maximal_Closed_Loop_solution)
               apply(rename_tac Pum Pm SPECum Sm)(*strict*)
               apply(force)
              apply(rename_tac Pum Pm SPECum Sm)(*strict*)
              apply(force)
             apply(rename_tac Pum Pm SPECum Sm)(*strict*)
             apply(force)
            apply(rename_tac Pum Pm SPECum Sm)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm SPECum Sm)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "inf C1 (DES Pum Pm) \<le> sup C1 C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "inf C2 (DES Pum Pm) \<le> sup C1 C2")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "C1 \<le> (DES Pum Pm)")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      S="(DES SPECum Sm)"
      in SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_smaller_than_plant)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(subgoal_tac "C2 \<le> (DES Pum Pm)")
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      S="(DES SPECum Sm)"
      in SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_smaller_than_plant)
          apply(rename_tac Pum Pm SPECum Sm)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm SPECum Sm)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm SPECum Sm)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm SPECum Sm)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(simp add: sup_DES_ext_def supDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(case_tac C1)
  apply(rename_tac fun1 fun2)(*strict*)
  apply(case_tac C2)
  apply(rename_tac fun1 fun2 fun1a fun2a)(*strict*)
  apply(rename_tac C1um C1m C2um C2m)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "C1um \<inter> Pum = C1um")
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   prefer 2
   apply (metis Int_absorb2)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(subgoal_tac "C2um \<inter> Pum = C2um")
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   prefer 2
   apply (metis Int_absorb2)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(subgoal_tac "C1m \<inter> Pm = C1m")
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   prefer 2
   apply (metis Int_absorb2)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(subgoal_tac "C2m \<inter> Pm = C2m")
   apply(rename_tac C1um C1m C2um C2m)(*strict*)
   prefer 2
   apply (metis Int_absorb2)
  apply(rename_tac C1um C1m C2um C2m)(*strict*)
  apply(clarsimp)
  apply (metis DES.inject SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_smaller_than_plant inf_DES_ext_def le_iff_inf unique_SMSOL_hlp useSCP_Controller_Satisfactory_Maximal_Closed_Loop xt1(12))
  done

lemma SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_SI_spec: "
  IsDES P
  \<Longrightarrow> P = DES Pum Pm
  \<Longrightarrow> IsDES S
  \<Longrightarrow> S = DES SPECum Sm
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<Longrightarrow> IsDES C
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P (inf P S) \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P (inf P S) \<Sigma>UC
  \<Longrightarrow> C \<le> P
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P (inf P S) \<Sigma>UC"
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(clarsimp)
  apply(rename_tac C')(*strict*)
  apply(rule_tac
      t="Sup X"
      and s="inf C (DES Pum Pm)" for X
      in ssubst)
   apply(rename_tac C')(*strict*)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(simp (no_asm) add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(subgoal_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup X" for X
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(rule_tac
      t="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}"
      and s="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> C \<le> (inf (DES Pum Pm) (DES SPECum Sm))}"
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(rule antisym)
     apply(rename_tac C')(*strict*)
     apply(clarsimp)
     apply(rename_tac C' x)(*strict*)
     apply(simp add: DES_specification_satisfied_def)
    apply(rename_tac C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(rename_tac C')(*strict*)
    apply(simp add: DES_specification_satisfied_def)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C')(*strict*)
   apply(fold SCP_Closed_Loop_Satisfactory_Direct_def)[1]
   apply(rule SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   apply(clarsimp)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(case_tac C)
    apply(rename_tac C' fun1 fun2)(*strict*)
    apply(rename_tac Cum Cm)
    apply(rename_tac C' Cum Cm)(*strict*)
    apply(case_tac C')
    apply(rename_tac C' Cum Cm fun1 fun2)(*strict*)
    apply(rename_tac C'um C'm)
    apply(rename_tac C' Cum Cm C'um C'm)(*strict*)
    apply(clarsimp)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def DES_controllability_def DES_nonblockingness_def DES_specification_satisfied_def controllable_language_def)
    apply(simp add: IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def nonblockingness_language_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis Int_commute le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply (metis prefix_closure_intersection3)
   apply(rename_tac C')(*strict*)
   apply(rule DES_controllability_infimum)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<le> inf C (DES Pum Pm)")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup X" for X
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
   apply(rename_tac C')(*strict*)
   apply(rule Sup_upper)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
  apply(rename_tac C')(*strict*)
  apply(clarsimp)
  apply(case_tac C')
  apply(rename_tac C' fun1 fun2)(*strict*)
  apply(rename_tac C'um C'm)
  apply(rename_tac C' C'um C'm)(*strict*)
  apply(clarsimp)
  apply(rename_tac C'um C'm)(*strict*)
  apply(case_tac C)
  apply(rename_tac C'um C'm fun1 fun2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (DES Cum Cm) (DES Pum Pm) \<le> DES C'um C'm")
   apply(rename_tac C'um C'm Cum Cm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(subgoal_tac "inf (DES C'um C'm) (DES Pum Pm) \<le> DES Cum Cm")
   apply(rename_tac C'um C'm Cum Cm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(simp add: IsDES_def SCP_Controller_Satisfactory_def)
  apply(clarsimp)
  apply (metis Int_absorb1 Int_commute equalityI)
  done

lemma SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller: "
  IsDES P
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<Longrightarrow> IsDES C
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<Longrightarrow> C \<le> P
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(simp add: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(clarsimp)
  apply(rename_tac C')(*strict*)
  apply(rule_tac
      t="Sup X"
      and s="inf C (DES Pum Pm)" for X
      in ssubst)
   apply(rename_tac C')(*strict*)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(simp (no_asm) add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(subgoal_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup X" for X
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(rule_tac
      t="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}"
      and s="{C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> C \<le> (inf (DES Pum Pm) (DES SPECum Sm))}"
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(rule antisym)
     apply(rename_tac C')(*strict*)
     apply(clarsimp)
     apply(rename_tac C' x)(*strict*)
     apply(simp add: DES_specification_satisfied_def)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(rename_tac C')(*strict*)
    apply(simp add: DES_specification_satisfied_def)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
   apply(rename_tac C')(*strict*)
   apply(fold SCP_Closed_Loop_Satisfactory_Direct_def)[1]
   apply(rule SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   apply(clarsimp)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
    apply(case_tac C)
    apply(rename_tac C' fun1 fun2)(*strict*)
    apply(rename_tac Cum Cm)
    apply(rename_tac C' Cum Cm)(*strict*)
    apply(case_tac C')
    apply(rename_tac C' Cum Cm fun1 fun2)(*strict*)
    apply(rename_tac C'um C'm)
    apply(rename_tac C' Cum Cm C'um C'm)(*strict*)
    apply(clarsimp)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(simp add: SCP_Controller_Satisfactory_def DES_controllability_def DES_nonblockingness_def DES_specification_satisfied_def controllable_language_def)
    apply(simp add: IsDES_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def nonblockingness_language_def)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis Int_commute le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply(rule conjI)
     apply(rename_tac Cum Cm C'um C'm)(*strict*)
     apply (metis le_infI2)
    apply(rename_tac Cum Cm C'um C'm)(*strict*)
    apply (metis prefix_closure_intersection3)
   apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
   apply(rule conjI)
    apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
    apply(rule DES_controllability_infimum)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm C')(*strict*)
   apply(simp add: SCP_Controller_Satisfactory_def DES_controllability_def DES_nonblockingness_def DES_specification_satisfied_def controllable_language_def)
  apply(rename_tac C')(*strict*)
  apply(subgoal_tac "inf C' (DES Pum Pm) \<le> inf C (DES Pum Pm)")
   apply(rename_tac C')(*strict*)
   prefer 2
   apply(rule_tac
      t="inf C (DES Pum Pm)"
      and s="Sup X" for X
      in ssubst)
    apply(rename_tac C')(*strict*)
    apply(force)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
   apply(rename_tac C')(*strict*)
   apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
   apply(rename_tac C')(*strict*)
   apply(rule Sup_upper)
   apply(force)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C (DES Pum Pm) = Sup X" for X)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C (DES Pum Pm) \<in> X" for X)
  apply(rename_tac C')(*strict*)
  apply(thin_tac "inf C' (DES Pum Pm) \<in> {C. IsDES C \<and> DES_controllability \<Sigma>UC (DES Pum Pm) C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf (DES Pum Pm) (DES SPECum Sm)) C}")
  apply(rename_tac C')(*strict*)
  apply(clarsimp)
  apply(case_tac C')
  apply(rename_tac C' fun1 fun2)(*strict*)
  apply(rename_tac C'um C'm)
  apply(rename_tac C' C'um C'm)(*strict*)
  apply(clarsimp)
  apply(rename_tac C'um C'm)(*strict*)
  apply(case_tac C)
  apply(rename_tac C'um C'm fun1 fun2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (DES Cum Cm) (DES Pum Pm) \<le> DES C'um C'm")
   apply(rename_tac C'um C'm Cum Cm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(subgoal_tac "inf (DES C'um C'm) (DES Pum Pm) \<le> DES Cum Cm")
   apply(rename_tac C'um C'm Cum Cm)(*strict*)
   prefer 2
   apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(rename_tac C'um C'm Cum Cm)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(clarsimp)
  apply(simp add: IsDES_def SCP_Controller_Satisfactory_def)
  apply(clarsimp)
  apply (metis Int_absorb1 Int_commute equalityI)
  done

corollary SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller: "
  IsDES P
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<Longrightarrow> C \<le> P
  \<Longrightarrow> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm SPECum Sm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(subgoal_tac "IsDES C \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC")
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    prefer 2
    apply(rule_tac
      P="P"
      and S="S"
      in SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply (metis (no_types, lifting) SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def mem_Collect_eq)
   apply(rule context_conjI)
    apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory set_mp)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
  apply(rule SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
       apply(force)
      apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(force)
  done

corollary SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<Longrightarrow> C \<le> P
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC"
  apply(subgoal_tac "IsDES C \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC")
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      P="P"
      and S="S"
      in SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
    apply(force)
   apply(rule context_conjI)
    apply (metis (no_types, lifting) SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def mem_Collect_eq)
   apply(rule context_conjI)
    apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory set_mp)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_SCP_Controller_Satisfactory_Maximal_Closed_Loop)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      and C="DES (SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)) (SCP_UPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))"
      in SCP_UPsol_Is_Optimal)
      apply (metis SIUMRes_makes_DES)
     apply(force)
    apply(force)
   apply(simp add: SCP_UPsol_def)
  apply(simp add: SCP_UPsol_def)
  apply(rule_tac
      P="P"
      and S="S"
      in unique_SMSOL)
           apply(force)
          apply(force)
         apply(force)
        apply (metis SIUMRes_makes_DES)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma SCP_UPsol_smaller_than_plant: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> C \<le> P"
  apply(subgoal_tac "IsDES C")
   prefer 2
   apply(simp add: SCP_UPsol_def)
   apply (metis SIUMRes_makes_DES)
  apply(simp add: SCP_UPsol_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm SPECum Sm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(simp add: SCP_UPu_def SCP_UPm_def SCP_Uspace_def IsDES_def)
  apply(rule conjI)
   apply(rename_tac Pum Pm SPECum Sm)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(clarsimp)
  apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
  apply(simp add: prefix_closure_def prefix_def IsDES_def)
  apply(rule_tac
      A="X"
      in set_mp)
   apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
  apply(rule_tac
      B="{w. \<exists>v. v \<in> Pm \<and> v \<in> Sm \<and> (\<exists>c. w @ c = v)}"
      in subset_trans)
   apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
  apply(rule_tac
      B="{w. \<exists>v. v \<in> Pum \<and> (\<exists>c. w @ c = v)}"
      in subset_trans)
   apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm SPECum Sm x X)(*strict*)
  apply(clarsimp)
  done

corollary SCP_UPsol_is_contained_in_SCP_Controller_Least_Restrictive_Direct: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Direct P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac SPECum Sm)
  apply(rename_tac Pum Pm SPECum Sm)(*strict*)
  apply(case_tac C)
  apply(rename_tac Pum Pm SPECum Sm set1 set2)(*strict*)
  apply(rename_tac Cum Cm)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(subgoal_tac "C\<le>P")
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      and C="C"
      in SCP_UPsol_smaller_than_plant)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(force)
  apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(rule context_conjI)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(simp add: SCP_UPsol_def)
   apply (metis SIUMRes_makes_DES)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(subgoal_tac "inf C P = C")
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   prefer 2
   apply (metis inf.orderE)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      and C="DES (SCP_UPu \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S)) (SCP_UPm \<Sigma>UC (des_langUM P) (des_langM P) (des_langM S))"
      in SCP_UPsol_Is_Optimal)
      apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
      apply (metis SIUMRes_makes_DES)
     apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(simp add: SCP_UPsol_def)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(rule order_antisym)
   apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(simp add: SCP_UPsol_def DES_specification_satisfied_def)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm)(*strict*)
  apply(rule Sup_least)
  apply(rename_tac Pum Pm SPECum Sm Cum Cm x)(*strict*)
  apply(clarsimp)
  apply(simp add: SCP_UPsol_def)
  apply(clarsimp)
  apply(rename_tac Pum Pm SPECum Sm x)(*strict*)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_def)
  apply(erule_tac
      x="x"
      in allE)
  apply(subgoal_tac "inf x (DES Pum Pm) = x")
   apply(rename_tac Pum Pm SPECum Sm x)(*strict*)
   prefer 2
   apply (metis inf.absorb1)
  apply(rename_tac Pum Pm SPECum Sm x)(*strict*)
  apply(clarsimp)
  apply(simp add: SCP_Controller_Satisfactory_def)
  done

definition SCP_Controller_Least_Restrictive2 :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES set" where
  "SCP_Controller_Least_Restrictive2 P S \<Sigma>UC \<equiv>
  {C. 
  C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> inf C P = Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC)
  \<and> inf C P \<in> SCP_Closed_Loop_Satisfactory P S \<Sigma>UC}"

theorem SCP_Controller_Least_Restrictive2__vs__SCP_Controller_Least_Restrictive: "
  SCP_Controller_Least_Restrictive2 P S \<Sigma>UC = SCP_Controller_Least_Restrictive P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Least_Restrictive2_def SCP_Controller_Least_Restrictive_def)
  apply(rule antisym)
   apply(simp add: SCP_Controller_Satisfactory_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: SCP_Closed_Loop_Satisfactory_def SCP_Controller_Satisfactory_def)
  apply(clarsimp)
  done

theorem bot_is_SCP_Controller_Satisfactory: "
  bot \<in> SCP_Controller_Satisfactory P S \<Sigma>UC"
  apply(simp add: SCP_Controller_Satisfactory_def)
  apply(simp add: botDES_def bot_DES_ext_def)
  apply(rule conjI)
   apply(simp add: IsDES_def prefix_closure_def)
  apply(rule conjI)
   apply(simp add: DES_specification_satisfied_def less_eq_DES_ext_def lesseqDES_def)
  apply(rule conjI)
   apply(simp add: nonblockingness_language_def DES_nonblockingness_def less_eq_DES_ext_def lesseqDES_def)
  apply(simp add: append_language_def DES_controllability_def controllable_language_def less_eq_DES_ext_def lesseqDES_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def)
  done

lemma DES_specification_satisfied_trans: "
  DES_specification_satisfied S P1
  \<Longrightarrow> P2 \<le> P1
  \<Longrightarrow> DES_specification_satisfied S P2"
  apply(simp add: DES_specification_satisfied_def)
  done

theorem SCP_Controller_Least_Restrictive2_is_not_empty: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Controller_Least_Restrictive2 P S \<Sigma>UC \<noteq> {}"
  apply(simp add: SCP_Controller_Least_Restrictive2_def)
  apply(rule_tac x="Sup (SCP_Closed_Loop_Satisfactory P S \<Sigma>UC)" in exI)
  apply(rule conjI)
   apply (metis SCP_Closed_Loop_Satisfactory_smaller_than_plant inf.absorb2 inf.commute)
  apply(rule conjI)
   apply(simp add: SCP_Controller_Satisfactory_def SCP_Closed_Loop_Satisfactory_def)
   apply(rule conjI)
    apply(rule Sup_DES_contained)
    apply(clarsimp)
    apply (metis infDES_preserves_IsDES inf_DES_ext_def)
   apply(rule conjI)
    apply(rule_tac ?P1.0="Sup {inf C P |C.
                IsDES C \<and>
                DES_specification_satisfied S (inf C P) \<and>
                DES_nonblockingness (inf C P) \<and> DES_controllability \<Sigma>UC P C}" in DES_specification_satisfied_trans)
     apply(rule Sup_Spec_contained)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(rule DES_nonblockingness_infimum)
     apply(rule Sup_least)
     apply(force)
    apply(rule Sup_BF_contained)
    apply(force)
   apply(rule Sup_Cont_contained)
   apply(clarsimp)
   apply (metis DES_controllability_infimum)
  apply(metis SCP_Closed_Loop_Satisfactory_supremum_contained)
  done

theorem SCP_Controller_Least_Restrictive_Adapted_Specification__vs__SCP_Controller_Least_Restrictive2: "
  IsDES P 
  \<Longrightarrow> IsDES S
  \<Longrightarrow> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC = SCP_Controller_Least_Restrictive2 P S \<Sigma>UC"
  apply (metis SCP_Controller_Least_Restrictive2__vs__SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Adapted_Specification_is_equal_to_SCP_Controller_Least_Restrictive_Direct SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct)
  done 

end
