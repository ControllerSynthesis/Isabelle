section {*FUNCTION\_\_F\_DPDA\_DFA\_CC\_\_fp\_\_DPDA\_DFA\_CONSTRUCT\_CONTROLLER\_FP*}
theory
  FUNCTION__F_DPDA_DFA_CC__fp__DPDA_DFA_CONSTRUCT_CONTROLLER_FP

imports
  PRJ_14_03__ENTRY

begin

definition FPiteratorMarked__fp__SpecInput :: "
  'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> bool"
  where
    "FPiteratorMarked__fp__SpecInput \<equiv>
  FPiteratorMarked__SpecInput"

definition FPiteratorMarked__fp__SpecOutput :: "
  'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event set
  \<Rightarrow> 'event DES
  \<Rightarrow> bool"
  where
    "FPiteratorMarked__fp__SpecOutput S P \<Sigma>UC C' \<equiv>
  IsDES C'
  \<and> DES_specification_satisfied S C'
  \<and> DES_nonblockingness C'
  \<and> DES_controllability \<Sigma>UC P C'
  \<and> C' \<le> P
  \<and> C' \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"

definition F_DPDA_DFA_CC__fp__SpecInput :: "
  ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DFA_CC__fp__SpecInput \<equiv>
  F_DPDA_DFA_CC__fp_one__SpecInput"

definition F_DPDA_DFA_CC__fp__SpecOutput :: "
  ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, nat) epda 
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option
  \<Rightarrow> bool"
  where
    "F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC C' \<equiv>
  case C' of
  None \<Rightarrow>
    FPiteratorMarked__fp__SpecOutput
      (epda_to_des S)
      (epda_to_des P)
      \<Sigma>UC 
      (DES {} {})
  | Some C' \<Rightarrow>
    FPiteratorMarked__fp__SpecOutput
      (epda_to_des S)
      (epda_to_des P)
      \<Sigma>UC 
      (epda_to_des C')
    \<and> valid_dpda C'
    \<and> \<not> epdaH_livelock C'
    \<and> epda_operational_controllable C' P \<Sigma>UC
    \<and> epdaH.accessible C'"

primrec fixed_iteration :: "
  nat
  \<Rightarrow> ('value \<Rightarrow> 'value)
  \<Rightarrow> 'value
  \<Rightarrow> 'value"
  where
    "fixed_iteration 0 F X = X"
  | "fixed_iteration (Suc n) F X = fixed_iteration n F (F X)"

lemma fixed_iteration_FB_iterate_vs_post_apply_hlp: "
  \<forall>A. F (fixed_iteration n F A) = fixed_iteration (Suc n) F A"
  apply(induct n rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x A)(*strict*)
  apply(case_tac x)
   apply(rename_tac x A)(*strict*)
   apply(clarsimp)
  apply(rename_tac x A nat)(*strict*)
  apply(clarsimp)
  done

lemma fixed_iteration_FB_iterate_vs_post_apply: "
  F (fixed_iteration n F A) = fixed_iteration (Suc n) F A"
  apply(subgoal_tac "\<forall>A. F (fixed_iteration n F A) = fixed_iteration (Suc n) F A")
   apply(force)
  apply(rule fixed_iteration_FB_iterate_vs_post_apply_hlp)
  done

primrec fixed_abortable_iteration :: "
  nat 
  \<Rightarrow> ('value \<Rightarrow> ('value option \<times> bool)) 
  \<Rightarrow> bool 
  \<Rightarrow> 'value 
  \<Rightarrow> ('value option \<times> bool)" 
  where
    "fixed_abortable_iteration 0 F continue D = 
    (Some D, continue)"
  | "fixed_abortable_iteration (Suc n) F continue D = 
    (let 
      (D', nowchanged) = F D 
    in
      case D' of 
      None \<Rightarrow> (None, False)
      | Some D' \<Rightarrow>
        (case nowchanged of
        True \<Rightarrow> fixed_abortable_iteration n F True D'
        | False \<Rightarrow> (Some D', False)))"

definition abortable_iterator :: "
  ('value \<Rightarrow> 'value option \<times> bool) 
  \<Rightarrow> ('value option \<times> bool \<Rightarrow> 'value option \<times> bool) "
  where
    "abortable_iterator F \<equiv>
  \<lambda>X. case X of 
      (None, b) \<Rightarrow> (None, False) 
      | (Some Y, b) \<Rightarrow> 
          (case F Y of 
          (E, b') \<Rightarrow> (E, b'))"

lemma fixed_iteration_idemp_on_None_False: "
  (None, False) = fixed_iteration n (\<lambda> (a, b) . case a of None \<Rightarrow> (None, False) | Some Y \<Rightarrow> case_prod Pair (F Y)) (None, False)"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma fixed_iteration_idemp_on_Some_False_if_then_term: "
  F D = (Some D, False) 
  \<Longrightarrow> (Some D, False) = fixed_iteration n (\<lambda> (a, b) . case a of None \<Rightarrow> (None, False) | Some Y \<Rightarrow> case_prod Pair (F Y)) (Some D, False)"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

definition iterator_props :: "
  ('value \<Rightarrow> bool)
  \<Rightarrow> ('value \<Rightarrow> 'value option \<times> bool)
  \<Rightarrow> bool"
  where
    "iterator_props P F \<equiv>
  (\<forall>A B. P A \<longrightarrow> F A = (Some B, True) \<longrightarrow> B \<noteq> A)
  \<and> (\<forall>A. P A \<longrightarrow> F A \<noteq> (None, True))
  \<and> (\<forall>A B b. P A \<longrightarrow> F A = (Some B, b) \<longrightarrow> P B)
  \<and> (\<forall>A B. P A \<longrightarrow> F A = (Some B, False) \<longrightarrow> A = B)"

lemma fixed_abortable_iteration_vs_fixed_iteration: "
  iterator_props P F 
  \<Longrightarrow> P D 
  \<Longrightarrow> fixed_abortable_iteration n F ischanged D = fixed_iteration n (abortable_iterator F) (Some D, ischanged)"
  apply(induct n arbitrary: ischanged D)
   apply(rename_tac ischanged D)(*strict*)
   apply(simp add: abortable_iterator_def)
  apply(rename_tac n ischanged D)(*strict*)
  apply(simp add: abortable_iterator_def)
  apply(rename_tac n D)(*strict*)
  apply(case_tac "F D")
  apply(rename_tac n D a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac n D a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n D b)(*strict*)
   apply(case_tac b)
    apply(rename_tac n D b)(*strict*)
    apply(subgoal_tac "(\<forall>A. P A \<longrightarrow> F A \<noteq> (None, True))")
     apply(rename_tac n D b)(*strict*)
     apply(erule_tac
      x="D"
      in allE)
     apply(force)
    apply(rename_tac n D b)(*strict*)
    apply(simp only: iterator_props_def)
   apply(rename_tac n D b)(*strict*)
   apply(clarsimp)
   apply(case_tac n)
    apply(rename_tac n D b)(*strict*)
    apply(clarsimp)
   apply(rename_tac n D b nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac D b nat)(*strict*)
   apply(rule fixed_iteration_idemp_on_None_False)
  apply(rename_tac n D a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n D b aa)(*strict*)
  apply(case_tac b)
   apply(rename_tac n D b aa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="True"
      in meta_allE)
   apply(erule_tac
      x="aa"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac n D b aa)(*strict*)
    apply(subgoal_tac "(\<forall>A B b. P A \<longrightarrow> F A = (Some B, b) \<longrightarrow> P B)")
     apply(rename_tac n D b aa)(*strict*)
     apply(force)
    apply(rename_tac n D b aa)(*strict*)
    apply(simp only: iterator_props_def)
    apply(erule conjE)+
    apply(force)
   apply(rename_tac n D b aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n D b aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "aa=D")
   apply(rename_tac n D b aa)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>A B. P A \<longrightarrow> F A = (Some B, False) \<longrightarrow> A = B)")
    apply(rename_tac n D b aa)(*strict*)
    apply(force)
   apply(rename_tac n D b aa)(*strict*)
   apply(simp only: iterator_props_def)
   apply(erule conjE)+
   apply(force)
  apply(rename_tac n D b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n D b)(*strict*)
  apply(rule fixed_iteration_idemp_on_Some_False_if_then_term)
  apply(force)
  done

lemma fixed_abortable_iteration_FB_iterate_vs_post_apply: "
  iterator_props P F 
  \<Longrightarrow> P A 
  \<Longrightarrow> (abortable_iterator F) (fixed_abortable_iteration n F b A) = fixed_abortable_iteration (Suc n) F b A"
  apply(rule_tac
      t="fixed_abortable_iteration n F b A"
      in ssubst)
   apply(rule fixed_abortable_iteration_vs_fixed_iteration)
    apply(force)
   apply(force)
  apply(rule_tac
      t="fixed_abortable_iteration (Suc n) F b A"
      in ssubst)
   apply(rule fixed_abortable_iteration_vs_fixed_iteration)
    apply(force)
   apply(force)
  apply(rule fixed_iteration_FB_iterate_vs_post_apply)
  done

lemma FB_iterate_FB_iterate_vs_pre_apply: "
  FB_iterate_dom (F, A) 
  \<Longrightarrow> iterator_props P F 
  \<Longrightarrow> P A 
  \<Longrightarrow> FB_iterate F A = (case F A of (None, b) \<Rightarrow> None | (Some V, b) \<Rightarrow> FB_iterate F V)"
  apply(induct rule: FB_iterate.pinduct)
  apply(rename_tac F A)(*strict*)
  apply(clarsimp)
  apply(case_tac "F A")
  apply(rename_tac F A a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac F A a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac F A b)(*strict*)
   apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
    apply(rename_tac F A b)(*strict*)
    apply(rule FB_iterate.psimps)
    apply(force)
   apply(rename_tac F A b)(*strict*)
   apply(clarsimp)
  apply(rename_tac F A a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac F A b aa)(*strict*)
  apply(erule_tac
      x="Some aa"
      in meta_allE)
  apply(erule_tac
      x="True"
      in meta_allE)
  apply(erule_tac
      x="aa"
      in meta_allE)
  apply(clarsimp)
  apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
   apply(rename_tac F A b aa)(*strict*)
   apply(rule FB_iterate.psimps)
   apply(force)
  apply(rename_tac F A b aa)(*strict*)
  apply(clarsimp)
  apply(case_tac b)
   apply(clarsimp)
  apply(clarsimp) 
  apply(subgoal_tac "A = aa")
   apply(rename_tac F A b aa)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>A B. P A \<longrightarrow> F A = (Some B, False) \<longrightarrow> A = B)")
    apply(rename_tac F A b aa)(*strict*)
    prefer 2
    apply(simp only: iterator_props_def)
    apply(erule conjE)+
    apply(force)
   apply(force) 
  apply(rename_tac F A b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac F b aa)(*strict*)
  apply(rule_tac
      t="FB_iterate F aa"
      in ssubst)
   apply(rename_tac F b aa)(*strict*)
   apply(rule FB_iterate.psimps)
   apply(force)
  apply(rename_tac F b aa)(*strict*)
  apply(clarsimp)
  done

lemma fixed_abortable_iteration_starting_bool_irrelevant_if_NoneTrue_is_reached: "
  fixed_abortable_iteration n F False aa = (None, True) 
  \<Longrightarrow> fixed_abortable_iteration n F True aa = (None, True)"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma fixed_abortable_iteration_starting_bool_irrelevant_if_SomeTrue_is_reached: "
  fixed_abortable_iteration n F bX aa = (Some a, b) 
  \<Longrightarrow> fixed_abortable_iteration n F True aa = (Some a, True)"
  apply(induct n arbitrary: aa a b bX)
   apply(rename_tac aa a b bX)(*strict*)
   apply(clarsimp)
  apply(rename_tac n aa a b bX)(*strict*)
  apply(clarsimp)
  apply(rename_tac n aa a b)(*strict*)
  apply(case_tac "F aa")
  apply(rename_tac n aa a b ab ba)(*strict*)
  apply(clarsimp)
  apply(case_tac ab)
   apply(rename_tac n aa a b ab ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac n aa a b ab ba ac)(*strict*)
  apply(clarsimp)
  apply(rename_tac n aa a b ba ac)(*strict*)
  apply(case_tac ba)
   apply(rename_tac n aa a b ba ac)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac n aa a b ba ac)(*strict*)
  apply(clarsimp)
  oops

declare fixed_abortable_iteration.simps [simp del]

lemma Characteristic_Fixed_Point_Iterator_In_Out: "
  Characteristic_Fixed_Point_Iterator F INP INV OUT 
  \<Longrightarrow> INP X 
  \<Longrightarrow> (\<And>X. OUT X \<Longrightarrow> P X) 
  \<Longrightarrow> P (F X)"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

definition F_DPDA_DFA_CC__fp__SpecOutputn :: "
  ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('states DT_symbol, 'event DT_symbol, nat) epda 
  \<Rightarrow> 'event DT_symbol set 
  \<Rightarrow> ((('states DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option) 
      \<times> bool) 
  \<Rightarrow> bool"
  where
    "F_DPDA_DFA_CC__fp__SpecOutputn C S P \<Sigma>UC C' \<equiv>
  (case C' of 
    (None, changed) \<Rightarrow> 
      \<exists>n. Compute_Fixed_Point_Finite 
            n 
            (\<lambda>X. FPiteratorMarked \<Sigma>UC (epda_to_des P) X) 
            (epda_to_des C) 
           = bot 
    | (Some C', changed) \<Rightarrow> 
      F_DPDA_DFA_CC__fp_one__SpecInput C' S P
      \<and> (\<exists>n. Compute_Fixed_Point_Finite 
              n 
              (\<lambda>X. FPiteratorMarked \<Sigma>UC (epda_to_des P) X) 
              (epda_to_des C) 
             = epda_to_des C') 
      \<and> (\<not> changed \<longrightarrow> epda_operational_controllable C' P \<Sigma>UC))"

lemma FPiteratorMarked_preserves_bot: "
  FPiteratorMarked S Y (DES {} {}) = DES {} {}"
  apply(simp add: FPiteratorMarked_def)
  apply(simp add: ifcomp_def)
  apply(clarsimp)
  apply(simp add: Enforce_Nonblockingness_DES_def Enforce_Marked_Controllable_Subset_def)
  done

lemma F_DPDA_DFA_CC__fp_one_no_None_True: "
  F_DPDA_DFA_CC__fp_one D Paut \<Sigma>UC = (None, b)
  \<Longrightarrow> b = False"
  apply(simp add: F_DPDA_DFA_CC__fp_one_def)
  apply(clarsimp)
  apply(case_tac "F_DPDA_EC D Paut \<Sigma>UC")
  apply(rename_tac a ba)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac a ba aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ba aa)(*strict*)
  apply(case_tac ba)
   apply(rename_tac ba aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac ba aa)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_CC__fp_one_equal_on_Some_False: "
  F_DPDA_DFA_CC__fp_one D Paut \<Sigma>UC = (Some A, False) 
  \<Longrightarrow> D = A"
  apply(simp add: F_DPDA_DFA_CC__fp_one_def)
  apply(case_tac "F_DPDA_EC D Paut \<Sigma>UC")
  apply(rename_tac a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(case_tac b)
   apply(rename_tac b aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: F_DPDA_EC_def)
   apply(case_tac "F_DPDA_RCS (F_DPDA_EA_OPT (F_DPDA_EUML (F_DPDA_OTS (F_DPDA_DFA_PRODUCT D Paut)))) Paut \<Sigma>UC")
   apply(rename_tac b a ba)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
    apply(rename_tac b a ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac b a ba aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac b ba aa)(*strict*)
   apply(case_tac ba)
    apply(rename_tac b ba aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac b ba aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(case_tac b)
   apply(rename_tac b aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_CC__fp_one_equal_on_Some_True: "
  F_DPDA_EC__SpecInput A (P, \<Sigma>UC)
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one A P \<Sigma>UC = (Some A, True)
  \<Longrightarrow> Q"
  apply(simp add: F_DPDA_DFA_CC__fp_one_def)
  apply(case_tac "F_DPDA_EC A P \<Sigma>UC")
  apply(rename_tac a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(case_tac b)
   apply(rename_tac b aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac b aa)(*strict*)
   prefer 2
   apply(rule F_DPDA_EC__SOUND)
    apply(rename_tac b aa)(*strict*)
    apply(force)
   apply(rename_tac b aa)(*strict*)
   apply(force)
  apply(rename_tac b aa)(*strict*)
  apply(simp only: F_DPDA_EC__SpecOutput_def)
  apply(clarsimp)
  apply(subgoal_tac "epda_to_des A \<le> epda_to_des aa")
   apply(rename_tac b aa)(*strict*)
   apply(subgoal_tac "epda_to_des aa < epda_to_des A")
    apply(rename_tac b aa)(*strict*)
    apply(force)
   apply(rename_tac b aa)(*strict*)
   apply(subgoal_tac "epda_to_des aa \<le> epda_to_des A")
    apply(rename_tac b aa)(*strict*)
    apply(force)
   apply(rename_tac b aa)(*strict*)
   apply(simp add: Enforce_Marked_Controllable_Subset_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(rule conjI)
    apply(rename_tac b aa)(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language aa"
      and s="{w \<in> epdaH.unmarked_language A. controllable_sublanguage ((prefix_closure {w}) - {w}) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language A)}"
      in ssubst)
     apply(rename_tac b aa)(*strict*)
     apply(force)
    apply(rename_tac b aa)(*strict*)
    apply(force)
   apply(rename_tac b aa)(*strict*)
   apply(rule_tac
      t="epdaH.marked_language aa"
      and s="{w \<in> epdaH.marked_language A. controllable_sublanguage (prefix_closure {w}) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language A)}"
      in ssubst)
    apply(rename_tac b aa)(*strict*)
    apply(blast)
   apply(rename_tac b aa)(*strict*)
   apply(force)
  apply(rename_tac b aa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac b aa)(*strict*)
   prefer 2
   apply(rule_tac
      G="aa"
      in F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
  apply(rename_tac b aa)(*strict*)
  apply(simp add: F_DPDA_EB_OPT__SpecOutput_def)
  apply(clarsimp)
  apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
  apply(clarsimp)
  apply(rule_tac
      t="epdaH.marked_language A"
      and s="epdaS.marked_language A"
      in subst)
   apply(rename_tac b aa)(*strict*)
   apply(rule epdaS_to_epdaH_mlang)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b aa)(*strict*)
  apply(rule_tac
      t="epdaH.marked_language aa"
      and s="epdaS.marked_language aa"
      in subst)
   apply(rename_tac b aa)(*strict*)
   apply(rule epdaS_to_epdaH_mlang)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b aa)(*strict*)
  apply(rule_tac
      t="epdaH.unmarked_language A"
      and s="epdaS.unmarked_language A"
      in subst)
   apply(rename_tac b aa)(*strict*)
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b aa)(*strict*)
  apply(rule_tac
      t="epdaH.unmarked_language aa"
      and s="epdaS.unmarked_language aa"
      in subst)
   apply(rename_tac b aa)(*strict*)
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b aa)(*strict*)
  apply(rule conjI)
   apply(rename_tac b aa)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(rule_tac
      B="prefix_closure (epdaS.marked_language A)"
      in subset_trans)
   apply(rename_tac b aa)(*strict*)
   apply(force)
  apply(rename_tac b aa)(*strict*)
  apply(rule_tac
      t="epdaS.marked_language A"
      and s="epdaS.marked_language aa"
      in ssubst)
   apply(rename_tac b aa)(*strict*)
   apply(force)
  apply(rename_tac b aa)(*strict*)
  apply (metis Nonblockingness2_def epda_Nonblockingness2 valid_dpda_to_valid_pda PDA_to_epda)
  done

declare Compute_Fixed_Point_Finite.simps [simp del]

theorem iterator_props_satisfied: "
  iterator_props (\<lambda>C. F_DPDA_DFA_CC__fp_one__SpecInput C S P) (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC)"
  apply(simp add: iterator_props_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac A)(*strict*)
   apply(rule F_DPDA_DFA_CC__fp_one_equal_on_Some_True)
    apply(rename_tac A)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac A)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def nonblockingness_language_def FPiteratorMarked__SpecInput_def DES_nonblockingness_def des_langUM_def des_langM_def)
   apply(clarsimp)
   apply(simp add: epda_to_des_def)
   apply(rule_tac
      s="epdaH.marked_language A"
      and t="epdaS.marked_language A"
      in ssubst)
    apply(rename_tac A)(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac A)(*strict*)
   apply(rule_tac
      s="epdaH.marked_language P"
      and t="epdaS.marked_language P"
      in ssubst)
    apply(rename_tac A)(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dfa_def valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac A)(*strict*)
   apply(rule_tac
      s="epdaH.unmarked_language A"
      and t="epdaS.unmarked_language A"
      in ssubst)
    apply(rename_tac A)(*strict*)
    apply(rule epdaS_to_epdaH_unmarked_language)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac A)(*strict*)
   apply(rule_tac
      s="epdaH.unmarked_language P"
      and t="epdaS.unmarked_language P"
      in ssubst)
    apply(rename_tac A)(*strict*)
    apply(rule epdaS_to_epdaH_unmarked_language)
    apply (metis valid_dfa_def valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac A)(*strict*)
   apply(clarsimp)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac A)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac A)(*strict*)
    prefer 2
    apply(rule F_DPDA_DFA_CC__fp_one_no_None_True)
    apply(force)
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac A B b)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac A B b)(*strict*)
    prefer 2
    apply(rule_tac \<Sigma>UC="\<Sigma>UC" in F_DPDA_DFA_CC__fp_one__SOUND)
    apply(force)
   apply(rename_tac A B b)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
  apply(clarsimp)
  apply(rename_tac A B)(*strict*)
  apply(rule F_DPDA_DFA_CC__fp_one_equal_on_Some_False)
  apply(force)
  done

theorem F_DPDA_DFA_CC__fp_one__SOUND_repetition: "
  F_DPDA_DFA_CC__fp_one__SpecInput C S P
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecOutputn C S P \<Sigma>UC (fixed_abortable_iteration (Suc n) (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C)"
  apply(induct n)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_DPDA_DFA_CC__fp_one__SOUND)
    apply(force)
   apply(simp add: fixed_abortable_iteration.simps F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecOutput_def FPiteratorMarked__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutputn_def)
   apply(case_tac "F_DPDA_DFA_CC__fp_one C P \<Sigma>UC")
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b aa changed x y)(*strict*)
   apply(case_tac aa)
    apply(rename_tac a b aa changed x y)(*strict*)
    apply(clarsimp)
    apply(rename_tac a b changed x y)(*strict*)
    apply(case_tac x)
     apply(rename_tac a b changed x y)(*strict*)
     apply(clarsimp)
     apply(rename_tac a b changed y)(*strict*)
     apply(rule_tac
      x="Suc 0"
      in exI)
     apply(simp add: Compute_Fixed_Point_Finite.simps)
     apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
    apply(rename_tac a b changed x y aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac b ba aa)(*strict*)
    apply(case_tac b)
     apply(rename_tac b ba aa)(*strict*)
     apply(clarsimp)
     apply(simp add: fixed_abortable_iteration.simps F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecOutput_def FPiteratorMarked__SpecOutput_def)
    apply(rename_tac b ba aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a b aa ba ab)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b ba ab)(*strict*)
   apply(case_tac a)
    apply(rename_tac a b ba ab)(*strict*)
    apply(clarsimp)
   apply(rename_tac a b ba ab aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac b ba ab aa)(*strict*)
   apply(case_tac b)
    apply(rename_tac b ba ab aa)(*strict*)
    apply(clarsimp)
    apply(simp add: fixed_abortable_iteration.simps F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecOutput_def FPiteratorMarked__SpecOutput_def)
    apply(clarsimp)
    apply(rename_tac b ba ab)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(simp add: Compute_Fixed_Point_Finite.simps)
   apply(rename_tac b ba ab aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac b ba)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(simp add: Compute_Fixed_Point_Finite.simps)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="fixed_abortable_iteration (Suc (Suc n)) (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C"
      and s="abortable_iterator (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) (fixed_abortable_iteration (Suc n) (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C)"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      P="\<lambda>C. F_DPDA_DFA_CC__fp_one__SpecInput C S P"
      and n="Suc n"
      and F="(\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC)"
      and b0="False"
      and A="C"
      in fixed_abortable_iteration_FB_iterate_vs_post_apply)
    apply(rename_tac n)(*strict*)
    apply(rule iterator_props_satisfied)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(case_tac "fixed_abortable_iteration (Suc n) (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C")
  apply(rename_tac n a b)(*strict*)
  apply(case_tac a)
   apply(rename_tac n a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n b)(*strict*)
   apply(simp add: abortable_iterator_def)
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutputn_def)
  apply(rename_tac n a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n b aa)(*strict*)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp_one__SpecInput aa S P")
   apply(rename_tac n b aa)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutputn_def)
  apply(rename_tac n b aa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n b aa)(*strict*)
   prefer 2
   apply(rule_tac
      C="aa"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND)
   apply(force)
  apply(rename_tac n b aa)(*strict*)
  apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def abortable_iterator_def F_DPDA_DFA_CC__fp_one__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutputn_def)
  apply(case_tac "F_DPDA_DFA_CC__fp_one aa P \<Sigma>UC")
  apply(rename_tac n b aa a ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac n b aa a ba na)(*strict*)
  apply(case_tac a)
   apply(rename_tac n b aa a ba na)(*strict*)
   apply(clarsimp)
   apply(rename_tac n b aa ba na)(*strict*)
   apply(rule_tac
      x="(Suc na)"
      in exI)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc na) (FPiteratorMarked \<Sigma>UC (epda_to_des P)) (epda_to_des C)"
      in subst)
    apply(rename_tac n b aa ba na)(*strict*)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n b aa ba na)(*strict*)
   apply(clarsimp)
   apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
  apply(rename_tac n b aa a ba na ab)(*strict*)
  apply(clarsimp)
  apply(rename_tac n b aa ba na ab)(*strict*)
  apply(rule_tac
      x="(Suc na)"
      in exI)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc na) (FPiteratorMarked \<Sigma>UC (epda_to_des P)) (epda_to_des C)"
      in subst)
   apply(rename_tac n b aa ba na ab)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n b aa ba na ab)(*strict*)
  apply(clarsimp)
  done

theorem fixed_abortable_iteration_vs_Compute_Fixed_Point_Finite: "
  valid_dpda Caut 
  \<Longrightarrow> valid_dfa Paut 
  \<Longrightarrow> valid_dpda Saut 
  \<Longrightarrow> Pdes = epda_to_des Paut 
  \<Longrightarrow> Sdes = epda_to_des (Saut::('c DT_symbol, 'a DT_symbol, 'c DT_symbol) epda) 
  \<Longrightarrow> G = FPiteratorMarked \<Sigma>UC Pdes 
  \<Longrightarrow> epda_to_des (Caut::('c DT_symbol, 'a DT_symbol, 'c DT_symbol) epda) = init 
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one__SpecInput Caut Saut Paut 
  \<Longrightarrow> case fixed_abortable_iteration (Suc n) (\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) False Caut of (None, b) \<Rightarrow> (Compute_Fixed_Point_Finite (Suc n) G init = bot) | (Some C'aut, b) \<Rightarrow> (Compute_Fixed_Point_Finite (Suc n) G init = (epda_to_des C'aut) \<and> (\<not> b \<longrightarrow> ((\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) C'aut = (Some C'aut, False) \<and> G (epda_to_des C'aut) = (epda_to_des C'aut)) ))"
  apply(induct n)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      C="Caut"
      and S="Saut"
      and P="Paut"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND)
    apply(force)
   apply(clarsimp)
   apply(rename_tac a b)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
   apply(clarsimp)
   apply(rename_tac a b x y)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(case_tac a)
    apply(rename_tac a b x y)(*strict*)
    apply(clarsimp)
    apply(rename_tac b x y)(*strict*)
    apply(case_tac "F_DPDA_DFA_CC__fp_one Caut Paut \<Sigma>UC")
    apply(rename_tac b x y a ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac b x y)(*strict*)
    apply(case_tac x)
     apply(rename_tac b x y)(*strict*)
     apply(clarsimp)
     apply(rename_tac b y)(*strict*)
     apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
     apply(simp add: Compute_Fixed_Point_Finite.simps)
    apply(rename_tac b x y a)(*strict*)
    apply(clarsimp)
    apply(rename_tac b y a)(*strict*)
    apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
    apply(case_tac y)
     apply(rename_tac b y a)(*strict*)
     apply(clarsimp)
     apply(simp add: fixed_abortable_iteration.simps)
    apply(rename_tac b y a)(*strict*)
    apply(clarsimp)
   apply(rename_tac a b x y aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac b x y aa)(*strict*)
   apply(case_tac x)
    apply(rename_tac b x y aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac b x y aa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac b y aa a)(*strict*)
   apply(case_tac y)
    apply(rename_tac b y aa a)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac b y aa a)(*strict*)
     apply(simp add: fixed_abortable_iteration.simps)
     apply(clarsimp)
     apply(rename_tac b y aa)(*strict*)
     apply(simp add: Compute_Fixed_Point_Finite.simps)
    apply(rename_tac b y aa a)(*strict*)
    apply(simp add: fixed_abortable_iteration.simps)
   apply(rename_tac b y aa a)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(simp add: Compute_Fixed_Point_Finite.simps)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="fixed_abortable_iteration (Suc (Suc n)) (\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) False Caut"
      and s="abortable_iterator (\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) (fixed_abortable_iteration (Suc n) (\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) False Caut)"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      n="Suc n"
      and F="(\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC)"
      and b0="False"
      and A="Caut"
      in fixed_abortable_iteration_FB_iterate_vs_post_apply)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      S="Saut"
      in iterator_props_satisfied)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc (Suc n)) G init"
      and s="G (Compute_Fixed_Point_Finite (Suc n) G init)"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x y a b)(*strict*)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp_one__SpecInput Caut Saut Paut")
   apply(rename_tac n x y a b)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
  apply(rename_tac n x y a b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n x y a b)(*strict*)
   prefer 2
   apply(rule_tac
      C="Caut"
      and S="Saut"
      and P="Paut"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND)
   apply(force)
  apply(rename_tac n x y a b)(*strict*)
  apply(case_tac a)
   apply(rename_tac n x y a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x y b)(*strict*)
   apply(case_tac x)
    apply(rename_tac n y a b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n y b)(*strict*)
    apply (metis FPiteratorMarked_preserves_bot botDES_def bot_DES_ext_def)
   apply(rename_tac n y a b aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y b aa)(*strict*)
   apply(simp add: abortable_iterator_def)
  apply(rename_tac n x y a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y a b aa)(*strict*)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp_one__SpecInput aa Saut Paut")
   apply(rename_tac n y a b aa)(*strict*)
   prefer 2
   apply(subgoal_tac "X" for X)
    apply(rename_tac n y a b aa)(*strict*)
    prefer 2
    apply(rule_tac
      C="Caut"
      and n="n"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND_repetition)
    apply(force)
   apply(rename_tac n y a b aa)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutputn_def)
  apply(rename_tac n y a b aa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n y a b aa)(*strict*)
   prefer 2
   apply(rule_tac
      C="aa"
      and S="Saut"
      and P="Paut"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND)
   apply(force)
  apply(rename_tac n y a b aa)(*strict*)
  apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def abortable_iterator_def)
  apply(case_tac y)
   apply(rename_tac n y a b aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y b aa x ya)(*strict*)
   apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
  apply(rename_tac n y a b aa ab)(*strict*)
  apply(clarsimp)
  done

lemma FB_iterate_via_FB_iterateN: "
  FB_iterate_dom (F, A) 
  \<Longrightarrow> iterator_props P F 
  \<Longrightarrow> P A 
  \<Longrightarrow> \<exists>n. fixed_abortable_iteration n F False A = (FB_iterate F A, False) \<and> (case FB_iterate F A of None \<Rightarrow> True | Some X \<Rightarrow> F X = (Some X, False))"
  apply(induct rule: FB_iterate.pinduct)
  apply(rename_tac F A)(*strict*)
  apply(case_tac "F A")
  apply(rename_tac F A a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac F A a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac F A b)(*strict*)
   apply(thin_tac "\<And>x y a. False \<Longrightarrow> x = None \<Longrightarrow> y \<Longrightarrow> P a \<Longrightarrow> (\<exists>n. fixed_abortable_iteration n F False a = (FB_iterate F a, False)) \<and> (case FB_iterate F a of None \<Rightarrow> True | Some X \<Rightarrow> F X = (Some X, False))")
   apply(rename_tac F A b)(*strict*)
   apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
    apply(rename_tac F A b)(*strict*)
    apply(rule FB_iterate_FB_iterate_vs_pre_apply)
      apply(rename_tac F A b)(*strict*)
      apply(force)
     apply(rename_tac F A b)(*strict*)
     apply(force)
    apply(rename_tac F A b)(*strict*)
    apply(force)
   apply(rename_tac F A b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(simp add: fixed_abortable_iteration.simps)
  apply(rename_tac F A a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac F A b aa)(*strict*)
  apply(erule_tac
      x="Some aa"
      in meta_allE)
  apply(erule_tac
      x="True"
      in meta_allE)
  apply(erule_tac
      x="aa"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac b)
   apply(rename_tac F A b aa)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "A=aa")
    apply(rename_tac F A b aa)(*strict*)
    prefer 2
    apply(subgoal_tac "(\<forall>A B. P A \<longrightarrow> F A = (Some B, False) \<longrightarrow> A = B)")
     apply(rename_tac F A b aa)(*strict*)
     apply(force)
    apply(rename_tac F A b aa)(*strict*)
    apply(simp only: iterator_props_def)
    apply(erule conjE)+
    apply(force)
   apply(rename_tac F A b aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac F b aa)(*strict*)
   apply(rule_tac
      t="FB_iterate F aa"
      in ssubst)
    apply(rename_tac F b aa)(*strict*)
    apply(rule FB_iterate.psimps)
    apply(force)
   apply(rename_tac F b aa)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(simp add: fixed_abortable_iteration.simps)
  apply(rename_tac F A b aa)(*strict*)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac F A b aa)(*strict*)
   apply(subgoal_tac "(\<forall>A B b. P A \<longrightarrow> F A = (Some B, b) \<longrightarrow> P B)")
    apply(rename_tac F A b aa)(*strict*)
    apply(force)
   apply(rename_tac F A b aa)(*strict*)
   apply(simp only: iterator_props_def)
   apply(erule conjE)+
   apply(force)
  apply(rename_tac F A b aa)(*strict*)
  apply(case_tac "FB_iterate F aa")
   apply(rename_tac F A b aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac F A b aa n)(*strict*)
   apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
    apply(rename_tac F A b aa n)(*strict*)
    apply(rule FB_iterate.psimps)
    apply(force)
   apply(rename_tac F A b aa n)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(case_tac n)
    apply(rename_tac F A b aa n)(*strict*)
    apply(clarsimp)
    apply(rename_tac F A b aa)(*strict*)
    apply(simp add: fixed_abortable_iteration.simps)
   apply(rename_tac F A b aa n nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac F A b aa nat)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
  apply(rename_tac F A b aa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac F A b aa a n)(*strict*)
  apply(rule conjI)
   apply(rename_tac F A b aa a n)(*strict*)
   prefer 2
   apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
    apply(rename_tac F A b aa a n)(*strict*)
    apply(rule FB_iterate.psimps)
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(clarsimp)
  apply(rename_tac F A b aa a n)(*strict*)
  apply(rule_tac
      x="Suc (Suc n)"
      in exI)
  apply(rule_tac
      t="fixed_abortable_iteration (Suc (Suc n)) F False A"
      in subst)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(rule_tac
      P="P"
      in fixed_abortable_iteration_FB_iterate_vs_post_apply)
    apply(rename_tac F A b aa a n)(*strict*)
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(subgoal_tac "P aa")
    apply(rename_tac F A b aa a n)(*strict*)
    apply(subgoal_tac "(\<forall>A. P A \<longrightarrow> F A \<noteq> (None, True))")
     apply(rename_tac F A b aa a n)(*strict*)
     apply(force)
    apply(rename_tac F A b aa a n)(*strict*)
    apply(simp only: iterator_props_def)
    apply(erule conjE)+
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(subgoal_tac "(\<forall>A B b. P A \<longrightarrow> F A = (Some B, b) \<longrightarrow> P B)")
    apply(rename_tac F A b aa a n)(*strict*)
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(simp only: iterator_props_def)
   apply(erule conjE)+
   apply(force)
  apply(rename_tac F A b aa a n)(*strict*)
  apply(subgoal_tac "A\<noteq> aa")
   apply(rename_tac F A b aa a n)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>A B. P A \<longrightarrow> F A = (Some B, True) \<longrightarrow> B \<noteq> A)")
    apply(rename_tac F A b aa a n)(*strict*)
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(simp only: iterator_props_def)
   apply(erule conjE)+
   apply(force)
  apply(rename_tac F A b aa a n)(*strict*)
  apply(rule_tac
      t="FB_iterate F A"
      and s="Some a"
      in ssubst)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(rule_tac
      t="FB_iterate F A"
      in ssubst)
    apply(rename_tac F A b aa a n)(*strict*)
    apply(rule FB_iterate.psimps)
    apply(force)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(force)
  apply(rename_tac F A b aa a n)(*strict*)
  apply(thin_tac "FB_iterate F aa = Some a")
  apply(case_tac n)
   apply(rename_tac F A b aa a n)(*strict*)
   apply(clarsimp)
   apply(rename_tac F A b aa a)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(clarsimp)
   apply(rename_tac F A b a)(*strict*)
   apply(simp only: abortable_iterator_def)
   apply(clarsimp)
  apply(rename_tac F A b aa a n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac F A b aa a nat)(*strict*)
  apply(simp add: fixed_abortable_iteration.simps)
  apply(simp only: abortable_iterator_def)
  apply(clarsimp)
  done

lemma instantiated_FB_iterate_via_FB_iterateN: "
  FB_iterate_dom (F, A) 
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one__SpecInput A S P
  \<Longrightarrow> F = (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) 
  \<Longrightarrow> \<exists>n. fixed_abortable_iteration n F False A = (FB_iterate F A, False) \<and> (case FB_iterate F A of None \<Rightarrow> True | Some X \<Rightarrow> F X = (Some X, False))"
  apply(rule_tac
      P="(\<lambda>C. F_DPDA_DFA_CC__fp_one__SpecInput C S P)"
      in FB_iterate_via_FB_iterateN)
    apply(force)
   apply(clarsimp)
   apply(rule iterator_props_satisfied)
  apply(force)
  done

theorem fixed_abortable_iteration_vs_Compute_Fixed_Point_Finite_for_termination_at_zero: "
  valid_dpda Caut 
  \<Longrightarrow> valid_dfa Paut 
  \<Longrightarrow> valid_dpda Saut 
  \<Longrightarrow> Pdes = epda_to_des Paut 
  \<Longrightarrow> Sdes = epda_to_des (Saut::('c DT_symbol, 'a DT_symbol, 'd DT_symbol) epda) 
  \<Longrightarrow> G = FPiteratorMarked \<Sigma>UC Pdes 
  \<Longrightarrow> epda_to_des (Caut::('c DT_symbol, 'a DT_symbol, 'd DT_symbol) epda) = init 
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one__SpecInput Caut Saut Paut 
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one Caut Paut \<Sigma>UC = (Some Caut, False) 
  \<Longrightarrow> case fixed_abortable_iteration 0 (\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) False Caut of (None, b) \<Rightarrow> (Compute_Fixed_Point_Finite 0 G init = bot) | (Some C'aut, b) \<Rightarrow> (Compute_Fixed_Point_Finite 0 G init = (epda_to_des C'aut) \<and> (\<not> b \<longrightarrow> ((\<lambda>X. F_DPDA_DFA_CC__fp_one X Paut \<Sigma>UC) C'aut = (Some C'aut, False) \<and> G (epda_to_des C'aut) = (epda_to_des C'aut)) ))"
  apply(simp add: fixed_abortable_iteration.simps Compute_Fixed_Point_Finite.simps)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac \<Sigma>UC="\<Sigma>UC" in F_DPDA_DFA_CC__fp_one__SOUND)
   apply(force)
  apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
  done

lemma Compute_Fixed_Point_Finite_in_dom: "
  Compute_Fixed_Point_Finite n F I = R 
  \<Longrightarrow> F R = R 
  \<Longrightarrow> Compute_Fixed_Point_dom (F, I)"
  apply(rule_tac
      F="F"
      in computeterm_by_compute_initialN)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac na)(*strict*)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_Finite_in_dom_and_equal: "
  Compute_Fixed_Point_Finite n F I = R 
  \<Longrightarrow> F R = R 
  \<Longrightarrow> R = Compute_Fixed_Point F I \<and> Compute_Fixed_Point_dom (F, I)"
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rule Compute_Fixed_Point_Finite_in_dom)
    apply(force)
   apply(force)
  apply (metis Compute_Fixed_Point_Finite_invariant_after_fixed_point compute_by_Compute_Fixed_Point_Finite nat_le_linear)
  done

theorem F_DPDA_DFA_CC__fp__SOUND: "
  FB_iterate_dom (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC, C) 
  \<Longrightarrow> epda_to_des C = FPinit (epda_to_des P) (epda_to_des S) 
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecInput C S P
  \<Longrightarrow> R = F_DPDA_DFA_CC__fp C P \<Sigma>UC 
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC R"
  apply(clarsimp)
  apply(simp add: F_DPDA_DFA_CC__fp_def)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp__SpecInput C S P")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_DFA_CC__fp__SpecInput_def)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp_one__SpecInput C S P")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_DFA_CC__fp__SpecInput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      in instantiated_FB_iterate_via_FB_iterateN)
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "\<exists>R. R = FB_iterate (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) C")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule exE)+
  apply(rename_tac n R)(*strict*)
  apply(subgoal_tac "F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC R")
   apply(rename_tac n R)(*strict*)
   apply(force)
  apply(rename_tac n R)(*strict*)
  apply(subgoal_tac "case R of None \<Rightarrow> True | Some X \<Rightarrow> F_DPDA_DFA_CC__fp_one X P \<Sigma>UC = (Some X, False)")
   apply(rename_tac n R)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n R)(*strict*)
  apply(thin_tac "case FB_iterate (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) C of None \<Rightarrow> True | Some X \<Rightarrow> F_DPDA_DFA_CC__fp_one X P \<Sigma>UC = (Some X, False)")
  apply(rename_tac n R)(*strict*)
  apply(subgoal_tac "fixed_abortable_iteration n (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C = (R, False)")
   apply(rename_tac n R)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n R)(*strict*)
  apply(thin_tac "fixed_abortable_iteration n (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) False C = (FB_iterate (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) C, False)")
  apply(rename_tac n R)(*strict*)
  apply(thin_tac "R = FB_iterate (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) C")
  apply(subgoal_tac "(epda_to_des_opt R) \<in> SCP_Controller_Least_Restrictive_Adapted_Specification (epda_to_des P) (epda_to_des S) \<Sigma>UC")
   apply(rename_tac n R)(*strict*)
   apply(case_tac R)
    apply(rename_tac n R)(*strict*)
    apply(simp add: epda_to_des_opt_def)
    apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(simp add: bot_DES_ext_def botDES_def F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def)
    apply(rule conjI)
     apply(rename_tac n)(*strict*)
     apply(simp add: IsDES_def)
     apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
    apply(rename_tac n)(*strict*)
    apply(rule conjI)
     apply(rename_tac n)(*strict*)
     apply(simp add: DES_specification_satisfied_def)
     apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
    apply(rename_tac n)(*strict*)
    apply(rule conjI)
     apply(rename_tac n)(*strict*)
     apply(simp add: DES_nonblockingness_def)
     apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
    apply(rename_tac n)(*strict*)
    apply(simp add: DES_controllability_def)
    apply(simp add: append_alphabet_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def append_language_def controllable_language_def)
   apply(rename_tac n R a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n a)(*strict*)
   apply(simp add: epda_to_des_opt_def)
   apply(case_tac n)
    apply(rename_tac n a)(*strict*)
    apply(clarsimp)
    apply(rename_tac a)(*strict*)
    apply(simp add: fixed_abortable_iteration.simps Compute_Fixed_Point_Finite.simps)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac \<Sigma>UC="\<Sigma>UC" in F_DPDA_DFA_CC__fp_one__SOUND)
     apply(force)
    apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
    apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def F_DPDA_DFA_CC__fp__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
    apply(simp add: FPiteratorMarked__SpecOutput_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
   apply(rename_tac n a nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac a nat)(*strict*)
   apply(rename_tac n)
   apply(rename_tac a n)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a n)(*strict*)
    prefer 2
    apply(rule_tac
      n="n"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND_repetition)
    apply(force)
   apply(rename_tac a n)(*strict*)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutputn_def FPiteratorMarked__fp__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def)
   apply(clarsimp)
   apply(rename_tac a n na)(*strict*)
   apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a n na)(*strict*)
    prefer 2
    apply(rule_tac
      S="epda_to_des S"
      and P="epda_to_des P"
      in SCP_Controller_Least_Restrictive_Direct_contained)
     apply(rename_tac a n na)(*strict*)
     apply(rule epda_to_des_enforces_IsDES)
     apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
    apply(rename_tac a n na)(*strict*)
    apply(rule epda_to_des_enforces_IsDES)
    apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
   apply(rename_tac a n na)(*strict*)
   apply(clarsimp)
   apply(simp add: SCP_Controller_Least_Restrictive_Direct_def)
   apply(subgoal_tac "inf (epda_to_des a) (epda_to_des P) = (epda_to_des a)")
    apply(rename_tac a n na)(*strict*)
    prefer 2
    apply (metis inf_DES_ext_def le_iff_inf)
   apply(rename_tac a n na)(*strict*)
   apply(clarsimp)
   apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def FPinit_def  DES_specification_satisfied_def)
   apply(rule Sup_Cont_contained)
   apply(rename_tac a n na X)(*strict*)
   apply(force)
  apply(rename_tac n R)(*strict*)
  apply(case_tac n)
   apply(rename_tac n R)(*strict*)
   apply(clarsimp)
   apply(rename_tac R)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      Caut="C"
      and Saut="S"
      and Paut="P"
      in fixed_abortable_iteration_vs_Compute_Fixed_Point_Finite_for_termination_at_zero)
            apply(simp add: FPiteratorMarked__SpecOutput_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
           apply(simp add: FPiteratorMarked__SpecOutput_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
          apply(simp add: FPiteratorMarked__SpecOutput_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def prefix_closure_def prefix_def)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(simp add: fixed_abortable_iteration.simps)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: Compute_Fixed_Point_Finite.simps)
   apply(simp add: epda_to_des_opt_def)
   apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def)
   apply(simp add: SCP_Controller_Least_Restrictive_Direct_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac y)(*strict*)
    prefer 2
    apply(rule_tac \<Sigma>UC="\<Sigma>UC" in F_DPDA_DFA_CC__fp_one__SOUND)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
   apply(clarsimp)
   apply(rule_tac
      t="inf (FPinit (epda_to_des P) (epda_to_des S)) (epda_to_des P)"
      and s="FPinit (epda_to_des P) (epda_to_des S)"
      in ssubst)
    apply(rename_tac y)(*strict*)
    apply(subgoal_tac "FPinit (epda_to_des P) (epda_to_des S) \<le> (epda_to_des P)")
     apply(rename_tac y)(*strict*)
     apply (metis inf_DES_ext_def le_iff_inf)
    apply(rename_tac y)(*strict*)
    apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(rename_tac y)(*strict*) 
   apply(rule conjI)
    apply(rename_tac y)(*strict*)
    apply(rule_tac
      t="FPinit (epda_to_des P) (epda_to_des S)"
      and s="epda_to_des C"
      in ssubst)
     apply(rename_tac y)(*strict*)
     apply(force)
    apply(rename_tac y)(*strict*)
    apply(rule epda_to_des_enforces_IsDES)
    apply(simp add: F_DPDA_DFA_CC__fp__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def valid_dpda_def valid_pda_def)
   apply(rename_tac y)(*strict*)
   apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
   apply(rule order_antisym)
    apply(rename_tac y)(*strict*)
    apply(rule Sup_upper)
    apply(clarsimp)
    apply(simp add: FPiteratorMarked__SpecOutput_def)
    apply(simp add: DES_specification_satisfied_def FPinit_def)
    apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def FPinit_def FPiteratorInit_def)
    apply(clarsimp)
    apply(simp (no_asm) add: Enforce_Nonblockingness_DES_def inf_DES_ext_def infDES_def Enforce_Specification_Satisfaction_def)
    apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
    apply(simp (no_asm) add: DES_nonblockingness_def epda_to_des_def DES_specification_satisfied_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def des_langM_def des_langUM_def inf_DES_ext_def infDES_def top_DES_ext_def topDES_def)
    apply(rename_tac y)(*strict*)
    apply(rule_tac
      B=" prefix_closure (epdaH.marked_language P)"
      in subset_trans)
     apply(rename_tac y)(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
     apply(force)
    apply(rename_tac y)(*strict*)
    apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def valid_dpda_def valid_pda_def valid_dfa_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac y x c)(*strict*)
    apply(rule epdaH_prefixes_of_marked_words_are_unmarked_words)
     apply(rename_tac y x c)(*strict*)
     apply(force)
    apply(rename_tac y x c)(*strict*)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(rule Sup_least)
   apply(rename_tac y x)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_specification_satisfied_def FPinit_def FPiteratorInit_def)
   apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(case_tac x)
   apply(rename_tac y x fun1 fun2)(*strict*)
   apply(clarsimp)
   apply(rename_tac y fun1 fun2)(*strict*)
   apply(subgoal_tac "fun2 \<subseteq> epdaH.marked_language P \<and> fun2 \<subseteq> epdaH.marked_language S \<and> fun1 \<subseteq> epdaH.unmarked_language P \<and> fun1 \<subseteq> epdaH.unmarked_language S")
    apply(rename_tac y fun1 fun2)(*strict*)
    prefer 2
    apply(simp add: inf_DES_ext_def infDES_def)
    apply(simp add: des_langM_def des_langUM_def epda_to_des_def)
    apply(simp add: Enforce_Nonblockingness_DES_def inf_DES_ext_def infDES_def Enforce_Specification_Satisfaction_def)
    apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(rename_tac y fun1 fun2)(*strict*)
   apply(simp (no_asm) add: Enforce_Nonblockingness_DES_def inf_DES_ext_def infDES_def Enforce_Specification_Satisfaction_def)
   apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(simp (no_asm) add: DES_nonblockingness_def epda_to_des_def DES_specification_satisfied_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def des_langM_def des_langUM_def inf_DES_ext_def infDES_def top_DES_ext_def topDES_def)
   apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def DES_nonblockingness_def valid_dpda_def valid_pda_def valid_dfa_def prefix_closure_def prefix_def nonblockingness_language_def)
   apply(clarsimp)
   apply(rename_tac y fun1 fun2 x)(*strict*)
   apply(simp add: DES_nonblockingness_def prefix_closure_def prefix_def nonblockingness_language_def)
   apply(simp add: des_langM_def des_langUM_def epda_to_des_def)
   apply(subgoal_tac "x \<in> {w. \<exists>v. v \<in> fun2 \<and> (\<exists>c. w @ c = v)} \<and> x \<in> epdaH.unmarked_language S \<and> x \<in> epdaH.unmarked_language P")
    apply(rename_tac y fun1 fun2 x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y fun1 fun2 x)(*strict*)
   apply(thin_tac "x \<in> fun1")
   apply(clarsimp)
   apply(rename_tac y fun1 fun2 x c)(*strict*)
   apply(subgoal_tac "x@c \<in> epdaH.marked_language S \<and> x@c \<in> epdaH.marked_language P")
    apply(rename_tac y fun1 fun2 x c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y fun1 fun2 x c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="x@c"
      in exI)
   apply(clarsimp)
  apply(rename_tac n R nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac R nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac R n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac R n)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND_repetition)
   apply(force)
  apply(rename_tac R n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point_Finite n (FPiteratorMarked \<Sigma>UC (epda_to_des P)) (epda_to_des C) = epda_to_des_opt R")
   apply(rename_tac R n)(*strict*)
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutputn_def)
   apply(case_tac R)
    apply(rename_tac R n)(*strict*)
    apply(clarsimp)
    apply(rename_tac n na)(*strict*)
    apply(rule_tac
      x="na"
      in exI)
    apply(simp add: epda_to_des_opt_def)
   apply(rename_tac R n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n a na)(*strict*)
   apply(rule_tac
      x="na"
      in exI)
   apply(simp add: epda_to_des_opt_def)
  apply(rename_tac R n)(*strict*)
  apply(clarsimp)
  apply(rename_tac R n na)(*strict*)
  apply(subgoal_tac "epda_to_des_opt R = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC (epda_to_des P)) (FPinit (epda_to_des P) (epda_to_des S)) \<and> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC (epda_to_des P), FPinit (epda_to_des P) (epda_to_des S))")
   apply(rename_tac R n na)(*strict*)
   apply(rule_tac
      t="epda_to_des_opt R"
      and s="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC (epda_to_des P)) (FPinit (epda_to_des P) (epda_to_des S))"
      in ssubst)
    apply(rename_tac R n na)(*strict*)
    apply(force)
   apply(rename_tac R n na)(*strict*)
   apply(rule Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked)
      apply(rename_tac R n na)(*strict*)
      apply(rule epda_to_des_enforces_IsDES)
      apply(simp add: F_DPDA_DFA_CC__fp__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def valid_dpda_def valid_pda_def valid_dfa_def)
     apply(rename_tac R n na)(*strict*)
     apply(rule epda_to_des_enforces_IsDES)
     apply(simp add: F_DPDA_DFA_CC__fp__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def valid_dpda_def valid_pda_def valid_dfa_def)
    apply(rename_tac R n na)(*strict*)
    apply(simp add: FPiteratorMarked_def FPinit_def FPiteratorInit_def FPinit_def FPiteratorInit_def)
   apply(rename_tac R n na)(*strict*)
   apply(simp add: FPiteratorMarked_def FPinit_def FPiteratorInit_def FPinit_def FPiteratorInit_def)
  apply(rename_tac R n na)(*strict*)
  apply(subgoal_tac "(FPiteratorMarked \<Sigma>UC (epda_to_des P)) (epda_to_des_opt R) = epda_to_des_opt R")
   apply(rename_tac R n na)(*strict*)
   prefer 2
   apply(case_tac R)
    apply(rename_tac R n na)(*strict*)
    apply(clarsimp)
    apply(rename_tac n na)(*strict*)
    apply(simp add: epda_to_des_opt_def)
    apply(simp add: bot_DES_ext_def botDES_def F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def)
    apply (metis FPiteratorMarked_preserves_bot botDES_def bot_DES_ext_def)
   apply(rename_tac R n na a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n na a)(*strict*)
   apply(simp add: epda_to_des_opt_def)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n na a)(*strict*)
    prefer 2
    apply(rule_tac
      C="a"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_DFA_CC__fp_one__SOUND)
    apply(simp add: F_DPDA_DFA_CC__fp__SpecOutputn_def)
    apply(clarsimp)
    apply(rename_tac n na a nb)(*strict*)
    apply(force)
   apply(rename_tac n na a)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
  apply(rename_tac R n na)(*strict*)
  apply(rule Compute_Fixed_Point_Finite_in_dom_and_equal)
   apply(rename_tac R n na)(*strict*)
   apply(force)
  apply(rename_tac R n na)(*strict*)
  apply(force)
  done

lemma FPiteratorMarked__fp__minimal: "
  FPiteratorMarked__fp__SpecInput C S P
  \<Longrightarrow> FPiteratorMarked__fp__SpecOutput S P \<Sigma>UC R
  \<Longrightarrow> \<exists>w \<in> des_langM R. w \<notin> des_langM R'
  \<Longrightarrow> FPiteratorMarked__fp__SpecOutput S P \<Sigma>UC R'
  \<Longrightarrow> False"
  apply(subgoal_tac "R' \<le> P")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(subgoal_tac "R \<le> P")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(subgoal_tac "inf R' P \<noteq> inf R P")
   prefer 2
   apply(simp add: infDES_def inf_DES_ext_def Enforce_Marked_Controllable_Subset_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def less_DES_ext_def lessDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(clarsimp)
   apply(blast)
  apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  done

lemma F_DPDA_DFA_CC__fp__minimal: "
  F_DPDA_DFA_CC__fp__SpecInput C S P
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC (Some R)
  \<Longrightarrow> \<exists>w \<in> des_langM (epda_to_des R). w \<notin> des_langM (epda_to_des R')
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC (Some R')
  \<Longrightarrow> False"
  apply(subgoal_tac "epda_to_des R' \<le> (epda_to_des P)")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(subgoal_tac "epda_to_des R \<le> (epda_to_des P)")
   prefer 2
   apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(subgoal_tac "inf (epda_to_des R') (epda_to_des P) \<noteq> inf (epda_to_des R) (epda_to_des P)")
   prefer 2
   apply(simp add: infDES_def inf_DES_ext_def Enforce_Marked_Controllable_Subset_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def less_DES_ext_def lessDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(clarsimp)
   apply(blast)
  apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  done

lemma FPiteratorMarked__fp__Infimum: "
  FPiteratorMarked__fp__SpecInput C S P
  \<Longrightarrow> FPiteratorMarked__fp__SpecOutput S P \<Sigma>UC C'
  \<Longrightarrow> C' = Inf {C' | C'. FPiteratorMarked__fp__SpecOutput S P \<Sigma>UC C'}"
  apply(rule antisym) 
   apply(rule Inf_greatest)
   apply(clarsimp)
   apply (metis (mono_tags, lifting) FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def eq_iff le_iff_inf mem_Collect_eq)
  apply(rule Inf_lower)
  apply(force)
  done

lemma marked_witness_for_not_lesser_DES: "
  IsDES B
  \<Longrightarrow> DES_nonblockingness A
  \<Longrightarrow> \<not> (A \<le> B)
  \<Longrightarrow> \<exists>w \<in> des_langM A. w \<notin> des_langM B"
  apply (metis DES_specification_satisfied_def DES_specification_satisfied_from_DES_nonblockingness_and_marked_satisfaction subsetI)
  done

lemma F_DPDA_DFA_CC__fp__Infimum: "
  F_DPDA_DFA_CC__fp__SpecInput C S P
  \<Longrightarrow> F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC (Some C')
  \<Longrightarrow> epda_to_des C' = Inf {epda_to_des C' | C'. F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC (Some C')}"
  apply(rule antisym) 
   prefer 2
   apply(rule Inf_lower)
   apply(force)
  apply(rule Inf_greatest)
  apply(clarsimp)
  apply(case_tac "epda_to_des C' \<le> epda_to_des C'a")
   apply(force)
  apply(clarsimp)
  apply(rule_tac R="C'" and R'="C'a" in F_DPDA_DFA_CC__fp__minimal)
     apply(force)
    apply(force)
   prefer 2
   apply(force)
  apply(rule marked_witness_for_not_lesser_DES)
    apply (metis (erased, lifting) FPiteratorMarked__fp__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutput_def option.simps(5))
   apply (metis (erased, lifting) FPiteratorMarked__fp__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutput_def option.simps(5))
  apply(force)
  done

hide_fact fixed_iteration_FB_iterate_vs_post_apply_hlp
hide_fact fixed_iteration_FB_iterate_vs_post_apply
hide_fact fixed_iteration_idemp_on_None_False
hide_fact fixed_iteration_idemp_on_Some_False_if_then_term
hide_fact fixed_abortable_iteration_vs_fixed_iteration
hide_fact fixed_abortable_iteration_FB_iterate_vs_post_apply
hide_fact FB_iterate_FB_iterate_vs_pre_apply
hide_fact fixed_abortable_iteration_starting_bool_irrelevant_if_NoneTrue_is_reached
hide_fact Characteristic_Fixed_Point_Iterator_In_Out
hide_fact FPiteratorMarked_preserves_bot
hide_fact F_DPDA_DFA_CC__fp_one_no_None_True
hide_fact F_DPDA_DFA_CC__fp_one_equal_on_Some_False
hide_fact F_DPDA_DFA_CC__fp_one_equal_on_Some_True
hide_fact FB_iterate_via_FB_iterateN
hide_fact instantiated_FB_iterate_via_FB_iterateN
hide_fact Compute_Fixed_Point_Finite_in_dom
hide_fact Compute_Fixed_Point_Finite_in_dom_and_equal
hide_fact iterator_props_satisfied
hide_fact F_DPDA_DFA_CC__fp_one__SOUND_repetition
hide_fact fixed_abortable_iteration_vs_Compute_Fixed_Point_Finite
hide_fact fixed_abortable_iteration_vs_Compute_Fixed_Point_Finite_for_termination_at_zero

end

