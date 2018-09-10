section {*FUNCTION\_\_DPDA\_DFA\_CC\_\_fp\_one\_\_DPDA\_DFA\_CONSTRUCT\_CONTROLLER\_FP\_ONE*}
theory
  FUNCTION__DPDA_DFA_CC__fp_one__DPDA_DFA_CONSTRUCT_CONTROLLER_FP_ONE

imports
  PRJ_14_02__ENTRY

begin

definition FPiteratorMarked__SpecInput :: "
  'event DES 
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event DES 
  \<Rightarrow> bool"
  where
    "FPiteratorMarked__SpecInput C S P \<equiv>
  IsDES C 
  \<and> IsDES S 
  \<and> IsDES P 
  \<and> DES_nonblockingness C 
  \<and> DES_specification_satisfied S C 
  \<and> C \<le> P"

definition FPiteratorMarked__SpecOutput_Alt :: "
  'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event set
  \<Rightarrow> 'event DES
  \<Rightarrow> bool
  \<Rightarrow> bool" 
  where
    "FPiteratorMarked__SpecOutput_Alt C S P \<Sigma>UC C' unchanged \<equiv>
  IsDES C'
  \<and> DES_specification_satisfied S C'
  \<and> (C = C' \<longleftrightarrow> unchanged)
  \<and> (if C = C' then DES_nonblockingness C' \<and> DES_controllability \<Sigma>UC P C' else True)"

definition FPiteratorMarked__SpecOutput :: "
  'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event DES
  \<Rightarrow> 'event set
  \<Rightarrow> 'event DES
  \<Rightarrow> bool
  \<Rightarrow> bool" 
  where
    "FPiteratorMarked__SpecOutput C S P \<Sigma>UC C' unchanged \<equiv>
  IsDES C'
  \<and> DES_specification_satisfied S C'  
  \<and> (C = C' \<longleftrightarrow> unchanged)
  \<and> (C = C' \<longrightarrow> DES_nonblockingness C' \<and> DES_controllability \<Sigma>UC P C')"    

definition F_DPDA_DFA_CC__fp_one__SpecInput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_DFA_CC__fp_one__SpecInput C S P \<equiv>
  valid_dpda C
  \<and> valid_dpda S
  \<and> valid_dfa P
  \<and> FPiteratorMarked__SpecInput (epda_to_des C) (epda_to_des S) (epda_to_des P)
  \<and> \<not> epdaH_livelock C
  \<and> epdaH.accessible C"

definition F_DPDA_DFA_CC__fp_one__SpecOutput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda 
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda 
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ((('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option) 
      \<times> bool)
  \<Rightarrow> bool"
  where
    "F_DPDA_DFA_CC__fp_one__SpecOutput C S P \<Sigma>UC C' \<equiv>
  case C' of
    (None, changed) \<Rightarrow>
      FPiteratorMarked \<Sigma>UC (epda_to_des P) (epda_to_des C) = DES {} {}
    | (Some C', changed) \<Rightarrow>
      FPiteratorMarked \<Sigma>UC (epda_to_des P) (epda_to_des C) = epda_to_des C'
      \<and> FPiteratorMarked__SpecOutput 
          (epda_to_des C) 
          (epda_to_des S)
          (epda_to_des P)
          \<Sigma>UC 
          (epda_to_des C')
          (\<not> changed)
      \<and> F_DPDA_DFA_CC__fp_one__SpecInput C' S P
      \<and> epda_to_des C' \<le> epda_to_des C
      \<and> (\<not> changed \<longleftrightarrow> C = C')
      \<and> (\<not> changed \<longrightarrow> epda_operational_controllable C' P \<Sigma>UC)"

lemma leq_le_trans_DES: "
  a \<le> b \<Longrightarrow> b < (c::('a)DES) \<Longrightarrow>  a \<le> c"
  apply(force)
  done

theorem F_DPDA_DFA_CC__fp_one__SOUND: "
  F_DPDA_DFA_CC__fp_one__SpecInput C S P
  \<Longrightarrow> F_DPDA_DFA_CC__fp_one__SpecOutput C S P \<Sigma>UC (F_DPDA_DFA_CC__fp_one C P \<Sigma>UC)"
  apply(simp add: F_DPDA_DFA_CC__fp_one_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="C"
      and P="P"
      and \<Sigma>UC="\<Sigma>UC"
      in F_DPDA_EC__SOUND)
    apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def)
    apply(clarsimp)
    apply(rule_tac
      s="epdaH.unmarked_language C"
      and t="epdaS.unmarked_language C"
      in ssubst)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      s="epdaH.unmarked_language P"
      and t="epdaS.unmarked_language P"
      in ssubst)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply (metis valid_dfa_def valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      s="epdaH.marked_language C"
      and t="epdaS.marked_language C"
      in ssubst)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule_tac
      s="epdaH.marked_language P"
      and t="epdaS.marked_language P"
      in ssubst)
     apply(rule epdaS_to_epdaH_mlang)
     apply (metis valid_dfa_def valid_dpda_to_valid_pda PDA_to_epda)
    apply(rule conjI)
     apply(force)
    apply(simp add: DES_nonblockingness_def nonblockingness_language_def)
   apply(force)
  apply(case_tac "F_DPDA_EC C P \<Sigma>UC")
  apply(rename_tac a b)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: FPiteratorMarked__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecOutput_def F_DPDA_EC__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked_def epda_to_des_def)
   apply(simp add: ifcomp_def)
   apply(rule conjI)
    apply(rename_tac b)(*strict*)
    apply(clarsimp)
    apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def DES_nonblockingness_def nonblockingness_language_def)
    apply(simp add: prefix_closure_def prefix_def)
   apply(rename_tac b)(*strict*)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def DES_nonblockingness_def prefix_closure_def prefix_def Enforce_Nonblockingness_DES_def)
  apply(rename_tac a b aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac b aa)(*strict*)
  apply(rename_tac C')
  apply(rename_tac b C')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac b C')(*strict*)
   prefer 2
   apply(rule_tac
      G="C'"
      in F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def F_DPDA_EC__SpecOutput_def)
  apply(rename_tac b C')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac b C')(*strict*)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="epda_to_des P"
      in Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
   apply(simp add: F_DPDA_EC__SpecOutput_def FPiteratorMarked__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
  apply(rename_tac b C')(*strict*)
  apply(case_tac b)
   apply(rename_tac b C')(*strict*)
   apply(clarsimp)
   apply(simp only: F_DPDA_EC__SpecOutput_def FPiteratorMarked__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(subgoal_tac "(\<forall>X. IsDES X \<and> DES_nonblockingness X \<longrightarrow> DES_controllability \<Sigma>UC (epda_to_des P) X = (Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM (epda_to_des P)) X = X))")
    apply(rename_tac b)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac b)(*strict*)
   apply(erule_tac
      x="(epda_to_des C)"
      in allE)
   apply(clarsimp)
   apply(simp add: F_DPDA_DFA_CC__fp_one__SpecOutput_def)
   apply(rename_tac b)(*strict*)
   apply(simp add: epda_to_des_def F_DPDA_DFA_CC__fp_one__SpecOutput_def F_DPDA_EC__SpecOutput_def FPiteratorMarked__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked_def)
   apply(simp add: ifcomp_def)
  apply(clarsimp)
  apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def DES_nonblockingness_def) 
  apply(rename_tac b C')(*strict*)
  apply(clarsimp)
  apply(simp only: F_DPDA_DFA_CC__fp_one__SpecOutput_def F_DPDA_EC__SpecOutput_def F_DPDA_DFA_CC__fp_one__SpecInput_def FPiteratorMarked__SpecInput_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_EB_OPT__SpecOutput_def)
  apply(subgoal_tac "epdaS.marked_language C' = epdaH.marked_language C'")
   apply(rename_tac b C')(*strict*)
   prefer 2
   apply(rule epdaS_to_epdaH_mlang)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C')(*strict*)
  apply(subgoal_tac "epdaS.unmarked_language C' = epdaH.unmarked_language C'")
   apply(rename_tac b C')(*strict*)
   prefer 2
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C')(*strict*)
  apply(case_tac "F_DPDA_EB_OPT C'")
   apply(rename_tac b C')(*strict*)
   apply(clarsimp)
   apply(simp add: epda_to_des_def FPiteratorMarked__SpecOutput_def IsDES_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def prefix_closure_def prefix_def)
   apply(simp add: FPiteratorMarked_def)
   apply(simp add: ifcomp_def)
   apply(rule conjI)
    apply(rename_tac b C')(*strict*)
    apply(clarsimp)
   apply(rename_tac b C')(*strict*)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def DES_nonblockingness_def prefix_closure_def prefix_def Enforce_Nonblockingness_DES_def)
  apply(rename_tac b C' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac C'')
  apply(rename_tac b C' C'')(*strict*)
  apply(subgoal_tac "epdaS.marked_language C'' = epdaH.marked_language C''")
   apply(rename_tac b C' C'')(*strict*)
   prefer 2
   apply(rule epdaS_to_epdaH_mlang)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C' C'')(*strict*)
  apply(subgoal_tac "epdaS.unmarked_language C'' = epdaH.unmarked_language C''")
   apply(rename_tac b C' C'')(*strict*)
   prefer 2
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C' C'')(*strict*)
  apply(subgoal_tac "epda_to_des C > epda_to_des C'")
   apply(rename_tac b C' C'')(*strict*)
   prefer 2
   apply(subgoal_tac "epda_to_des C' \<le> epda_to_des C")
    apply(rename_tac b C' C'')(*strict*)
    apply(subgoal_tac "epda_to_des C' \<noteq> epda_to_des C")
     apply(rename_tac b C' C'')(*strict*)
     apply(force)
    apply(rename_tac b C' C'')(*strict*)
    apply(force)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: Enforce_Marked_Controllable_Subset_def)
   apply(simp add: epda_to_des_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(rule conjI)
    apply(rename_tac b C' C'')(*strict*)
    apply(rule_tac
      t="epdaH.unmarked_language C'"
      and s="{w \<in> epdaH.unmarked_language C. controllable_sublanguage ((prefix_closure {w}) - {w}) (alphabet_to_language \<Sigma>UC) (epdaH.unmarked_language P) (epdaH.unmarked_language C)}"
      in ssubst)
     apply(rename_tac b C' C'')(*strict*)
     apply(force)
    apply(rename_tac b C' C'')(*strict*)
    apply(force)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: controllable_subset_def)
   apply(rule_tac
      t="epdaH.marked_language C''"
      and s="{w \<in> epdaH.unmarked_language C. controllable_sublanguage (prefix_closure {w}) \<langle>\<Sigma>UC\<rangle> (epdaH.unmarked_language P) (epdaH.unmarked_language C)} \<inter> epdaH.marked_language C"
      in ssubst)
    apply(rename_tac b C' C'')(*strict*)
    apply(force)
   apply(rename_tac b C' C'')(*strict*)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(subgoal_tac "epda_to_des C' \<ge> epda_to_des C''")
   apply(rename_tac b C' C'')(*strict*)
   prefer 2
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def)
   apply(clarsimp)
   apply(rename_tac b C' C'' x)(*strict*)
   apply(simp add: IsDES_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(rule_tac
      A="prefix_closure (epdaH.marked_language C'')"
      in set_mp)
    apply(rename_tac b C' C'' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac b C' C'' x)(*strict*)
   apply(rule_tac
      t="prefix_closure (epdaH.marked_language C'')"
      and s="prefix_closure (epdaH.marked_language C')"
      in ssubst)
    apply(rename_tac b C' C'' x)(*strict*)
    apply(force)
   apply(rename_tac b C' C'' x)(*strict*)
   apply(simp (no_asm) add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac b C' C'' x xa c)(*strict*)
   apply(rule_tac
      v="c"
      in epdaH_unmarked_languageuage_prefix_closed)
    apply(rename_tac b C' C'' x xa c)(*strict*)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac b C' C'' x xa c)(*strict*)
   apply(rule_tac
      A="X" for X
      in set_mp)
    apply(rename_tac b C' C'' x xa c)(*strict*)
    apply(rule epdaH.lang_inclusion)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac b C' C'' x xa c)(*strict*)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule_tac t="FPiteratorMarked__SpecOutput (epda_to_des C) (epda_to_des S) (epda_to_des P) \<Sigma>UC
        (epda_to_des C'') False" and s="FPiteratorMarked__SpecOutput_Alt (epda_to_des C) (epda_to_des S) (epda_to_des P) \<Sigma>UC
        (epda_to_des C'') False" in ssubst)
   apply(simp add: FPiteratorMarked__SpecOutput_def FPiteratorMarked__SpecOutput_Alt_def)
  apply(simp add: FPiteratorMarked__SpecOutput_Alt_def)
  apply(rule context_conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "FPiteratorMarked \<Sigma>UC (epda_to_des P) (epda_to_des C) = epda_to_des C'' \<and> IsDES (epda_to_des C'') \<and> DES_specification_satisfied (epda_to_des S) (epda_to_des C'') \<and> DES_nonblockingness (epda_to_des C'') \<and> epda_to_des C'' \<le> epda_to_des P \<and> epdaH.accessible C''")
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: DES_specification_satisfied_def)
   apply(clarsimp) 
   apply(rule context_conjI)
    apply(simp add: prefix_closure_def prefix_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def  Enforce_Nonblockingness_DES_def)
   apply(rule conjI)
    apply(simp add: prefix_closure_def prefix_def lesseqDES_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def  Enforce_Nonblockingness_DES_def)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: FPiteratorMarked_def ifcomp_def)
   apply(rule conjI)
    apply(rename_tac b C' C'')(*strict*)
    apply(simp add: FPiteratorMarked__SpecOutput_Alt_def IsDES_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def)
    apply(clarsimp)
   apply(rename_tac b C' C'')(*strict*)
   apply(clarsimp)
   apply(simp add: nonblockingness_language_def)
   apply(simp add: prefix_closure_def prefix_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def  Enforce_Nonblockingness_DES_def)
   apply(clarsimp)
   apply(rename_tac b C' C'' x c)(*strict*)
   apply(rule_tac
      v="c"
      in epdaH_prefixes_of_marked_words_are_unmarked_words)
    apply(rename_tac b C' C'' x c)(*strict*)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac b C' C'' x c)(*strict*)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: DES_specification_satisfied_def epda_to_des_def)
   apply(simp add: less_eq_DES_ext_def lesseqDES_def less_DES_ext_def lessDES_def FPiteratorMarked__SpecOutput_Alt_def IsDES_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def nonblockingness_language_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def)
   apply(simp add: less_eq_DES_ext_def lesseqDES_def less_DES_ext_def lessDES_def FPiteratorMarked__SpecOutput_Alt_def IsDES_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def nonblockingness_language_def)
   apply(clarsimp)
   apply(simp add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule conjI)
   apply(rename_tac b C' C'')(*strict*)
   apply(simp add: IsDES_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac b C' C'')(*strict*)
  apply(rule epdaS_to_epdaH_accessible)
   apply(rename_tac b C' C'')(*strict*)
   apply (metis valid_dpda_to_valid_pda PDA_to_epda)
  apply(rename_tac b C' C'')(*strict*)
  apply(force)
  done

end

