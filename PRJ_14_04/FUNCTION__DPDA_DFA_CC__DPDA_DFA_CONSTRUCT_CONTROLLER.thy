section {*FUNCTION\_\_DPDA\_DFA\_CC\_\_DPDA\_DFA\_CONSTRUCT\_CONTROLLER*}
theory
  FUNCTION__DPDA_DFA_CC__DPDA_DFA_CONSTRUCT_CONTROLLER

imports
  PRJ_14_04__ENTRY

begin

definition F_DPDA_DFA_CC__SpecInput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> bool" 
  where
    "F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC \<equiv>
  valid_dpda S
  \<and> valid_dfa P"

definition F_DPDA_DFA_CC__SpecOutput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option
  \<Rightarrow> bool" 
  where
    "F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC R \<equiv>
  case R of
  None \<Rightarrow>
    FPiteratorMarked__fp__SpecOutput (epda_to_des S) (epda_to_des P) \<Sigma>UC bot
  | Some C' \<Rightarrow>
    FPiteratorMarked__fp__SpecOutput (epda_to_des S) (epda_to_des P) \<Sigma>UC (epda_to_des C')
    \<and> valid_dpda C'
    \<and> \<not> epdaH_livelock C'
    \<and> epdaH.accessible C'
    \<and> epda_operational_controllable C' P \<Sigma>UC"

definition F_DPDA_DFA_CC__fp_start__SpecInput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> bool" 
  where
    "F_DPDA_DFA_CC__fp_start__SpecInput S P \<equiv>
  valid_dpda S
  \<and> valid_dfa P"

definition F_DPDA_DFA_CC__fp_start__SpecOutput :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option
  \<Rightarrow> bool" 
  where
    "F_DPDA_DFA_CC__fp_start__SpecOutput S P R \<equiv>
  case R of
  None \<Rightarrow>
    bot = FPinit (epda_to_des P) (epda_to_des S)
  | Some C' \<Rightarrow>
    epda_to_des C' = FPinit (epda_to_des P) (epda_to_des S)
    \<and> valid_dpda C'
    \<and> \<not> epdaH_livelock C'
    \<and> epdaH.accessible C'
    \<and> FPiteratorMarked__SpecInput (epda_to_des C') (epda_to_des S) (epda_to_des P)"

lemma F_DPDA_DFA_CC__fp_start__corresponds_to__FPiteratorMarked__fp_start: "
  valid_dpda S
  \<Longrightarrow> valid_dfa P
  \<Longrightarrow> epda_to_des_opt (F_DPDA_DFA_CC__fp_start S P) = FPinit (epda_to_des P) (epda_to_des S)"
  apply(simp add: epda_to_des_opt_def FPinit_def FPiteratorInit_def F_DPDA_DFA_CC__fp_start_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      Gi="S"
      and D="P"
      in F_DPDA_DFA_PRODUCT__SOUND1)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput1_def F_DPDA_DFA_CC__SpecInput_def)
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="F_DPDA_DFA_PRODUCT S P"
      in F_EPDA_TC__SOUND)
   apply(simp add: F_EPDA_TC__SpecInput_def)
  apply(simp add: F_EPDA_TC__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda"
      in F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
   apply(force)
  apply(simp add: F_DPDA_EB_OPT__SpecOutput_def)
  apply(subgoal_tac "epdaH.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda)")
   apply(subgoal_tac "epdaS.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)")
    apply(subgoal_tac "epdaS.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)) = epdaH.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P))")
     apply(case_tac "F_DPDA_DFA_CC__fp_start S P::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda option")
      apply(clarsimp)
      apply(simp add: F_DPDA_DFA_CC__fp_start_def)
      apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
      apply(simp add: epda_to_des_def)
      apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def)
      apply(simp (no_asm) add: DES_nonblockingness_def epda_to_des_def DES_specification_satisfied_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def des_langM_def des_langUM_def inf_DES_ext_def infDES_def top_DES_ext_def topDES_def)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
     apply(simp add: F_DPDA_DFA_CC__fp_start_def)
     apply(simp add: epda_to_des_def)
     apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def Enforce_Specification_Satisfaction_def Enforce_Nonblockingness_DES_def)
     apply(simp (no_asm) add: DES_nonblockingness_def epda_to_des_def DES_specification_satisfied_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def des_langM_def des_langUM_def inf_DES_ext_def infDES_def top_DES_ext_def topDES_def)
     apply(clarsimp)
     apply(subgoal_tac "epdaS.unmarked_language a = epdaH.unmarked_language a")
      apply(rename_tac a)(*strict*)
      apply(subgoal_tac "epdaS.marked_language a = epdaH.marked_language a")
       apply(rename_tac a)(*strict*)
       apply(clarsimp)
       apply(rule propSym)
       apply(rule context_conjI)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      t="epdaH.marked_language a"
      and s="epdaH.marked_language S \<inter> epdaH.marked_language P"
      in ssubst)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(rule inf.commute)
       apply(rename_tac a)(*strict*)
       apply(clarsimp)
       apply(rename_tac a x c)(*strict*)
       apply(subgoal_tac "x@c \<in> epdaH.marked_language a")
        apply(rename_tac a x c)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac a x c)(*strict*)
       apply(rule_tac
      v="c"
      in epdaH_unmarked_languageuage_prefix_closed)
        apply(rename_tac a x c)(*strict*)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac a x c)(*strict*)
       apply(rule_tac set_mp)
        apply(rename_tac a x c)(*strict*)
        apply(rule epdaH.lang_inclusion)
        apply (simp add: valid_dpda_def PDA_to_epda)
       apply(rename_tac a x c)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epdaH.marked_language SSX" 
      and s="epdaS.marked_language SSX" for SSX
      in subst)
       apply(rename_tac a)(*strict*)
       apply(rule epdaS_to_epdaH_mlang)
       apply (simp add: valid_dpda_to_valid_pda PDA_to_epda)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
      apply(rename_tac a)(*strict*)
      apply(rule epdaS_to_epdaH_unmarked_language)
      apply (simp add: valid_dpda_to_valid_pda PDA_to_epda)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
    apply(rule epdaS_to_epdaH_mlang)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(subgoal_tac "epdaH.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)")
   apply(subgoal_tac "epdaH.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)) = epdaS.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P))")
    apply(force)
   apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
    apply(rule epdaS_to_epdaH_mlang)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(force)
  apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
   apply(rule epdaS_to_epdaH_mlang)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(force)
  done

theorem F_DPDA_DFA_CC__fp_start__SOUND: "
  F_DPDA_DFA_CC__fp_start__SpecInput S P
  \<Longrightarrow> R = F_DPDA_DFA_CC__fp_start S P
  \<Longrightarrow> F_DPDA_DFA_CC__fp_start__SpecOutput S P R"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      in F_DPDA_DFA_CC__fp_start__corresponds_to__FPiteratorMarked__fp_start)
    apply(simp add: F_DPDA_DFA_CC__fp_start__SpecInput_def)
   apply(simp add: F_DPDA_DFA_CC__fp_start__SpecInput_def)
  apply(simp add: F_DPDA_DFA_CC__fp_start__SpecOutput_def)
  apply(case_tac "F_DPDA_DFA_CC__fp_start S P")
   apply(clarsimp)
   apply(simp add: epda_to_des_opt_def)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(simp add: epda_to_des_opt_def)
  apply(simp add: F_DPDA_DFA_CC__fp_start_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      Gi="S"
      and D="P"
      in F_DPDA_DFA_PRODUCT__SOUND1)
   apply(simp add: F_DPDA_DFA_CC__fp_start__SpecInput_def FUN_DPDA_DFA_PRODUCT__SpecInput1_def F_DPDA_DFA_CC__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_DPDA_DFA_PRODUCT S P"
      in F_EPDA_TC__SOUND)
   apply(simp add: F_EPDA_TC__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(simp add: F_EPDA_TC__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      G="F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda"
      in F_DPDA_EB_OPT__SOUND)
   apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(simp add: F_DPDA_EB_OPT__SpecOutput_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply (metis valid_dpda_def PDA_to_epda epdaS_to_epdaH_accessible)
  apply(rename_tac a)(*strict*)
  apply(simp add: FPiteratorMarked__SpecInput_def)
  apply(rule_tac
      t="FPinit (epda_to_des P) (epda_to_des S)"
      and s="epda_to_des a"
      in ssubst)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_def PDA_to_epda)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_def PDA_to_epda F_DPDA_DFA_CC__fp_start__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(rule epda_to_des_enforces_IsDES)
   apply (metis valid_dpda_def PDA_to_epda valid_dfa_def F_DPDA_DFA_CC__fp_start__SpecInput_def)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(simp add: DES_nonblockingness_def nonblockingness_language_def)
   apply(rule_tac
      t="FPinit (epda_to_des P) (epda_to_des S)"
      and s="epda_to_des a"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "epdaS.unmarked_language a = epdaH.unmarked_language a")
    apply(rename_tac a)(*strict*)
    apply(subgoal_tac "epdaS.marked_language a = epdaH.marked_language a")
     apply(rename_tac a)(*strict*)
     apply(simp (no_asm) add: des_langM_def des_langUM_def epda_to_des_def)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
     apply(rename_tac a)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
    apply(rename_tac a)(*strict*)
    apply(rule epdaS_to_epdaH_unmarked_language)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule conjI)
   apply(rename_tac a)(*strict*)
   apply(simp add: DES_specification_satisfied_def nonblockingness_language_def)
   apply(rule_tac
      t="FPinit (epda_to_des P) (epda_to_des S)"
      and s="epda_to_des a"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(simp (no_asm) add: des_langM_def des_langUM_def epda_to_des_def)
   apply(subgoal_tac "epdaS.unmarked_language a = epdaH.unmarked_language a")
    apply(rename_tac a)(*strict*)
    apply(subgoal_tac "epdaS.unmarked_language S = epdaH.unmarked_language S")
     apply(rename_tac a)(*strict*)
     apply(subgoal_tac "epdaS.marked_language a = epdaH.marked_language a")
      apply(rename_tac a)(*strict*)
      apply(subgoal_tac "epdaS.marked_language S = epdaH.marked_language S")
       apply(rename_tac a)(*strict*)
       apply(subgoal_tac "epdaS.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)")
        apply(rename_tac a)(*strict*)
        apply(simp (no_asm) add: FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def valid_dpda_def valid_pda_def valid_dfa_def prefix_closure_def prefix_def)
        apply(rule conjI)
         apply(rename_tac a)(*strict*)
         apply(rule_tac
      B="prefix_closure (epdaS.marked_language a)"
      in subset_trans)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(rule_tac
      B="prefix_closure (epdaS.marked_language S)"
      in subset_trans)
          apply(rename_tac a)(*strict*)
          apply(rule prefix_closure_preserves_subseteq)
          apply(rule_tac
      t="epdaS.marked_language a"
      and s="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(rule_tac
      t="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language S \<inter> epdaH.marked_language P"
      in ssubst)
           apply(rename_tac a)(*strict*)
           apply(force)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def)
         apply(erule conjE)+
         apply (metis Nonblockingness2_def epda_Nonblockingness2 valid_dpda_def PDA_to_epda )
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      t="epdaH.marked_language a"
      and s="epdaS.marked_language a"
      in ssubst)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      t="epdaS.marked_language a"
      and s="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      t="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      t="epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language S \<inter> epdaH.marked_language P"
      in ssubst)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
        apply(rename_tac a)(*strict*)
        apply(rule epdaS_to_epdaH_mlang)
        apply(simp add: valid_dpda_def valid_pda_def)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def)
      apply(erule conjE)+
      apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
       apply(rename_tac a)(*strict*)
       apply(rule epdaS_to_epdaH_mlang)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
      apply(rename_tac a)(*strict*)
      apply(rule epdaS_to_epdaH_mlang)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def)
    apply(erule conjE)+
    apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
     apply(rename_tac a)(*strict*)
     apply(rule epdaS_to_epdaH_unmarked_language)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
    apply(rename_tac a)(*strict*)
    apply(rule epdaS_to_epdaH_unmarked_language)
    apply(simp add: valid_dpda_def valid_pda_def)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(simp (no_asm) add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def)
  apply(simp add: nonblockingness_language_def)
  apply(subgoal_tac "epdaS.unmarked_language a = epdaH.unmarked_language a")
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "epdaS.unmarked_language P = epdaH.unmarked_language P")
    apply(rename_tac a)(*strict*)
    apply(subgoal_tac "epdaS.marked_language a = epdaH.marked_language a")
     apply(rename_tac a)(*strict*)
     apply(subgoal_tac "epdaS.marked_language P = epdaH.marked_language P")
      apply(rename_tac a)(*strict*)
      apply(subgoal_tac "epdaS.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)")
       apply(rename_tac a)(*strict*)
       apply(rule conjI)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      B="prefix_closure (epdaS.marked_language a)"
      in subset_trans)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(rule_tac
      B="prefix_closure (epdaS.marked_language P)"
      in subset_trans)
         apply(rename_tac a)(*strict*)
         apply(rule prefix_closure_preserves_subseteq)
         apply(rule_tac
      t="epdaS.marked_language a"
      and s="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(rule_tac
      t="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language S \<inter> epdaH.marked_language P"
      in ssubst)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def valid_dfa_def)
        apply(erule conjE)+
        apply (metis Nonblockingness2_def epda_Nonblockingness2 valid_dpda_def PDA_to_epda)
       apply(rename_tac a)(*strict*)
       apply(rule_tac
      t="epdaH.marked_language a"
      and s="epdaS.marked_language a"
      in ssubst)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(rule_tac
      t="epdaS.marked_language a"
      and s="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(rule_tac
      t="epdaS.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)"
      in ssubst)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(rule_tac
      t="epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)"
      and s="epdaH.marked_language S \<inter> epdaH.marked_language P"
      in ssubst)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
       apply(rename_tac a)(*strict*)
       apply(rule epdaS_to_epdaH_mlang)
       apply(simp add: valid_dpda_def valid_pda_def)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def)
     apply(erule conjE)+
     apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
      apply(rename_tac a)(*strict*)
      apply(rule epdaS_to_epdaH_mlang)
      apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="epdaH.marked_language SSX"
      and s="epdaS.marked_language SSX" for SSX
      in subst)
     apply(rename_tac a)(*strict*)
     apply(rule epdaS_to_epdaH_mlang)
     apply(simp add: valid_dpda_def valid_pda_def)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(simp only: F_DPDA_DFA_CC__fp_start__SpecInput_def)
   apply(erule conjE)+
   apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
    apply(rename_tac a)(*strict*)
    apply(rule epdaS_to_epdaH_unmarked_language)
    apply(simp add: valid_dpda_def valid_pda_def valid_dfa_def)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(rule_tac
      t="epdaH.unmarked_language SSX"
      and s="epdaS.unmarked_language SSX" for SSX
      in subst)
   apply(rename_tac a)(*strict*)
   apply(rule epdaS_to_epdaH_unmarked_language)
   apply(simp add: valid_dpda_def valid_pda_def)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

lemma F_DPDA_DFA_CC__SpecOutput__vs__F_DPDA_DFA_CC__fp__SpecOutput: "
  F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC C = F_DPDA_DFA_CC__fp__SpecOutput S P \<Sigma>UC C"
  apply(simp add: F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__fp__SpecOutput_def)
  apply(case_tac C)
   apply(simp add: botDES_def bot_DES_ext_def)
  apply(force)
  done

theorem F_DPDA_DFA_CC__SOUND: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> (\<And>C. F_DPDA_DFA_CC__fp_start S P = Some C \<Longrightarrow> FB_iterate_dom (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC, C))
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (F_DPDA_DFA_CC S P \<Sigma>UC)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      in F_DPDA_DFA_CC__fp_start__SOUND)
    apply(simp add: F_DPDA_DFA_CC__fp_start__SpecInput_def F_DPDA_DFA_CC__SpecInput_def)
   apply(force)
  apply(simp add: F_DPDA_DFA_CC_def)
  apply(case_tac "F_DPDA_DFA_CC__fp_start S P::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda option")
   apply(clarsimp)
   apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__fp_start_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def)
   apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def IsDES_def bot_DES_ext_def botDES_def)
   apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def append_language_def controllable_language_def)
   apply(rule conjI)
    apply(simp add: IsDES_def)
    apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
   apply(rule order_antisym)
    apply(rule Sup_upper)
    apply(clarsimp)
    apply(simp add: IsDES_def bot_DES_ext_def botDES_def)
    apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def)
   apply(case_tac x)
   apply(rename_tac x fun1 fun2)(*strict*)
   apply(clarsimp)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(subgoal_tac "epdaH.marked_language S \<inter> epdaH.marked_language P = {}")
    apply(rename_tac fun1 fun2)(*strict*)
    apply(subgoal_tac "fun2={}")
     apply(rename_tac fun1 fun2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac fun1 fun2)(*strict*)
    apply(clarsimp)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac fun1 fun2)(*strict*)
    prefer 2
    apply(rule_tac
      Gi="S"
      and D="P"
      in F_DPDA_DFA_PRODUCT__SOUND1)
    apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecInput1_def F_DPDA_DFA_CC__SpecInput_def)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(simp add: FUN_DPDA_DFA_PRODUCT__SpecOutput1_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac fun1 fun2)(*strict*)
    prefer 2
    apply(rule_tac
      G="F_DPDA_DFA_PRODUCT S P"
      in F_EPDA_TC__SOUND)
    apply(simp add: F_EPDA_TC__SpecInput_def)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(simp add: F_EPDA_TC__SpecOutput_def)
   apply(subgoal_tac "epdaH.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda)")
    apply(rename_tac fun1 fun2)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac fun1 fun2)(*strict*)
     prefer 2
     apply(rule_tac
      G="F_EPDA_TC (F_DPDA_DFA_PRODUCT S P)::('a DT_symbol, 'b DT_symbol, 'c DT_symbol) epda"
      in F_DPDA_EB_OPT__SOUND)
     apply(simp add: F_DPDA_EB_OPT__SpecInput_def)
     apply(force)
    apply(rename_tac fun1 fun2)(*strict*)
    apply(simp add: F_DPDA_EB_OPT__SpecOutput_def)
    apply(clarsimp)
    apply(subgoal_tac "epdaS.marked_language (F_DPDA_DFA_PRODUCT S P) = epdaH.marked_language (F_DPDA_DFA_PRODUCT S P)")
     apply(rename_tac fun1 fun2)(*strict*)
     apply(clarsimp)
    apply(rename_tac fun1 fun2)(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(rule_tac
      t="epdaH.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P))"
      and s="epdaS.marked_language (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P))"
      in subst)
    apply(rename_tac fun1 fun2)(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(rule_tac
      t="epdaH.marked_language ((F_DPDA_DFA_PRODUCT S P))"
      and s="epdaS.marked_language ((F_DPDA_DFA_PRODUCT S P))"
      in subst)
    apply(rename_tac fun1 fun2)(*strict*)
    apply(rule epdaS_to_epdaH_mlang)
    apply (metis valid_dpda_to_valid_pda PDA_to_epda)
   apply(rename_tac fun1 fun2)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac C)
  apply(rename_tac C)(*strict*)
  apply(simp add: F_DPDA_DFA_CC__fp_start__SpecOutput_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac C)(*strict*)
   prefer 2
   apply(rule_tac
      C="C"
      and P="P"
      and \<Sigma>UC="\<Sigma>UC"
      and S="S"
      in F_DPDA_DFA_CC__fp__SOUND)
      apply(rename_tac C)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac C)(*strict*)
     apply(force)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(simp add: F_DPDA_DFA_CC__fp__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_DFA_CC__SpecInput_def)
  apply(rename_tac C)(*strict*)
  apply(simp add: F_DPDA_DFA_CC__SpecOutput_def botDES_def bot_DES_ext_def)
  apply(simp add: F_DPDA_DFA_CC__fp__SpecOutput_def F_DPDA_DFA_CC__SpecOutput_def botDES_def bot_DES_ext_def)
  apply(case_tac "F_DPDA_DFA_CC__fp C P \<Sigma>UC")
   apply(rename_tac C)(*strict*)
   prefer 2
   apply(rename_tac C a)(*strict*)
   apply(clarsimp)
  apply(simp add: FPiteratorMarked__fp__SpecOutput_def)
  apply(rename_tac C)(*strict*)
  apply(simp add: FPiteratorMarked__fp__SpecOutput_def botDES_def bot_DES_ext_def)
  done

lemma F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory_Direct_adapted: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> epda_to_des (F_DPDA_DFA_PRODUCT SOL P) = Sup (SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC)"
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory_Direct: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> epda_to_des (F_DPDA_DFA_PRODUCT SOL P) = Sup (SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (epda_to_des S) \<Sigma>UC)"
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
    apply(force)
   apply(force)
  apply(subgoal_tac "epda_to_des SOL = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply (metis inf.absorb2 inf.commute) 
  apply(clarsimp)
  apply(subgoal_tac "SCP_Controller_Least_Restrictive_Adapted_Specification (epda_to_des P) (epda_to_des S) \<Sigma>UC = SCP_Controller_Least_Restrictive_Direct (epda_to_des P) (epda_to_des S) \<Sigma>UC")
   prefer 2
   apply(rule SCP_Controller_Least_Restrictive_Adapted_Specification_is_equal_to_SCP_Controller_Least_Restrictive_Direct)
   apply(rule epda_to_des_enforces_IsDES)
   apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def)
  apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def)
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  done



lemma F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> epda_to_des (F_DPDA_DFA_PRODUCT SOL P) = Sup (SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC)"
  apply(rule_tac t="SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC" and s="SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P) (epda_to_des S) \<Sigma>UC" in subst)
   apply(rule SCP_Closed_Loop_Satisfactory__vs__SCP_Closed_Loop_Satisfactory_Direct)
    apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Direct_def)
    apply (metis epda_to_des_enforces_IsDES valid_dfa_def valid_dpda_def valid_pda_def)
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Direct_def)
   apply (metis epda_to_des_enforces_IsDES valid_dpda_def valid_pda_def)
  apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory_Direct)
   apply(force)
  apply(force)
  done

lemma F_DPDA_DFA_CC__SpecOutput__TO__SCP_SATISFACTORY_CONTROLLER_DPDA: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> SOL \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC"
  apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def F_DPDA_DFA_CC__SpecOutput_def F_DPDA_DFA_CC__SpecInput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
    apply(force)
   apply(force)
  apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) 
   \<in> (SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P)
         (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC)")
   prefer 2
   apply (metis SCP_Closed_Loop_Satisfactory_Direct_supremum_contained)
  apply(thin_tac "inf (epda_to_des SOL) (epda_to_des P) =
   Sup (SCP_Closed_Loop_Satisfactory_Direct (epda_to_des P)
         (inf (epda_to_des P) (epda_to_des S)) \<Sigma>UC)")
  apply(subgoal_tac "epdaH_specification_satisfaction
    (F_DPDA_DFA_PRODUCT SOL P) S")
   prefer 2
   apply(thin_tac "ATS_Destinations.accessible epdaH_initial_configurations
    epdaH_step_relation epda_destinations
    epdaH_get_destinations SOL")
   apply(rule DES_specification_satisfied_to_epdaH_specification_satisfaction)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_livelock_freedom (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule no_epdaH_livelock_implies_F_DPDA_DFA_PRODUCT__epdaH_livelock_freedom)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__Nonblockingness_branching)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "epdaH_deadlock_freedom (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule epdaHNonblockingness_branching__to__epdaH_deadlock_freedom)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma F_DPDA_DFA_CC__SpecOutput__TO__SCP_SATISFACTORY_CLOSED_LOOP_DPDA: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> F_DPDA_DFA_PRODUCT SOL P \<in> SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC"
  apply(simp add: SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def)
  apply(rule_tac x="SOL" in exI)
  apply(clarsimp)
  apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_SATISFACTORY_CONTROLLER_DPDA)
   apply(force)
  apply(force)
  done

theorem Operational_Soundness2: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC  
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC None
  \<Longrightarrow> \<not>(\<exists>SOL. SOL \<in> SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY S P \<Sigma>UC)"
  apply(simp add: F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(clarsimp)
  apply(simp add: F_DPDA_DFA_CC__SpecInput_def SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(erule_tac x="epda_to_des(F_DPDA_DFA_PRODUCT SOL P)" in allE)
  apply(thin_tac "DES_specification_satisfied (epda_to_des S) bot")
  apply(thin_tac "DES_nonblockingness bot")
  apply(thin_tac "DES_controllability \<Sigma>UC (epda_to_des P) bot")
  apply(thin_tac "IsDES bot")
  apply(clarsimp)
  apply(thin_tac "SCP_DPDA_DFA_IS_SUPREMUM (F_DPDA_DFA_PRODUCT C P)
              {F_DPDA_DFA_PRODUCT C P |C. C \<in> SCP_SATISFACTORY_CONTROLLER_DPDA S P \<Sigma>UC}")
  apply(subgoal_tac "valid_dpda (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply (rule F_DPDA_DFA_PRODUCT__generates__DPDA)
     prefer 3
     apply(force)
    apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
   apply(force)
  apply(subgoal_tac "epda_to_des (F_DPDA_DFA_PRODUCT C P) \<noteq> bot")
   prefer 2
   apply(rule epda_to_des__of__valid_epda__not_empty)
   apply (simp add:  valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(subgoal_tac "IsDES (epda_to_des (F_DPDA_DFA_PRODUCT C P))")
   prefer 2
   apply(rule epda_to_des_enforces_IsDES)
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
   apply(clarsimp)
   apply (metis valid_dpda_def valid_pda_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (epda_to_des C) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C P)")
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
    apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)  
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
   prefer 2
   apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
    apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)  
   apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
  apply(subgoal_tac "epda_to_des (F_DPDA_DFA_PRODUCT C P) \<le> epda_to_des P")
   prefer 2
   apply (metis inf.commute inf_le1)
  apply(subgoal_tac "DES_nonblockingness (epda_to_des (F_DPDA_DFA_PRODUCT C P))")
   prefer 2
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "DES_specification_satisfied (inf (epda_to_des P) (epda_to_des S))
           (epda_to_des (F_DPDA_DFA_PRODUCT C P))")
   prefer 2
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "DES_controllability \<Sigma>UC (epda_to_des P) (epda_to_des (F_DPDA_DFA_PRODUCT C P))")
   prefer 2
   apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem Operational_Soundness: "
  F_DPDA_DFA_CC__SpecInput S P \<Sigma>UC  
  \<Longrightarrow> F_DPDA_DFA_CC__SpecOutput S P \<Sigma>UC (Some SOL)
  \<Longrightarrow> SOL \<in> SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY S P \<Sigma>UC    
    \<and> epdaH_accessible SOL
    \<and> epdaH_accessible_in_closed_loop SOL (F_DPDA_DFA_PRODUCT SOL P)
    \<and> epda_to_des (F_DPDA_DFA_PRODUCT SOL P) = Sup (SCP_Closed_Loop_Satisfactory (epda_to_des P) (epda_to_des S) \<Sigma>UC)"
  apply(rule context_conjI)
   apply(simp add: SCP_DPDA_DFA_LEAST_RESTRICTIVE_SATISFACTORY_def SCP_DPDA_DFA_IS_SUPREMUM_def)
   apply(rule context_conjI)
    apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_SATISFACTORY_CONTROLLER_DPDA)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_SATISFACTORY_CLOSED_LOOP_DPDA)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(subgoal_tac "Sup (epda_to_des ` SCP_SATISFACTORY_CLOSED_LOOP_DPDA S P \<Sigma>UC) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
     apply(force)
    apply(rule antisym)
     apply(rule Sup_least)
     apply(clarsimp)
     apply(simp add: SCP_SATISFACTORY_CLOSED_LOOP_DPDA_def)
     apply(clarsimp)
     apply(rename_tac C1 C2)
     apply(subgoal_tac "inf (epda_to_des C1) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C1 P)")
      prefer 2
      apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
       apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)  
      apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
      apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
     apply(subgoal_tac "inf (epda_to_des SOL) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT SOL P)")
      prefer 2
      apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
       apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)  
      apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
     apply(subgoal_tac "inf (epda_to_des C2) (epda_to_des P) = epda_to_des (F_DPDA_DFA_PRODUCT C2 P)")
      prefer 2
      apply(rule F_DPDA_DFA_PRODUCT__epda_to_des)
       apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)  
      apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
      apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
     apply(simp add: F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
     apply(clarsimp)
     apply(rule Sup_upper)
     apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def F_DPDA_DFA_CC__SpecInput_def)
     apply(rule context_conjI)
      apply(rule epda_to_des_enforces_IsDES)
      apply(simp add: SCP_SATISFACTORY_CONTROLLER_DPDA_def)
      apply(clarsimp)
      apply (metis F_DPDA_DFA_PRODUCT__generates__DPDA valid_dpda_def valid_pda_def)
     apply(rule context_conjI)
      apply(simp add: inf_DES_ext_def infDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def epda_to_des_def)
      apply(force)
     apply(subgoal_tac "DES_nonblockingness (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))")
      prefer 2
      apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_nonblockingness)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(subgoal_tac "DES_specification_satisfied (inf (epda_to_des P) (epda_to_des S))
           (epda_to_des (F_DPDA_DFA_PRODUCT C2 P))")
      prefer 2
      apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO__DES_specification_satisfied)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rule SCP_SATISFACTORY_CONTROLLER_DPDA__TO_DES_controllability)
       apply(force)
      apply(force)
     apply(force)
    apply(rule Sup_upper)
    apply(clarsimp)
   apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(simp add: F_DPDA_DFA_CC__SpecOutput_def)
   apply(rule epdaHaccessible__to__epdaH_accessible) 
   apply(force)
  apply(rule context_conjI)
   apply(rule epdaH_accessible__implies__epdaH_accessible_in_closed_loop__for__F_DPDA_DFA_PRODUCT__if__language_inclusion)
      apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def)
     apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def)
    apply(simp add: F_DPDA_DFA_CC__SpecInput_def F_DPDA_DFA_CC__SpecOutput_def FPiteratorMarked__fp__SpecOutput_def)
    apply(simp add: prefix_closure_def prefix_def FPiteratorMarked__SpecInput_def F_DPDA_DFA_CC__fp_one__SpecInput_def F_DPDA_EC__SpecInput_def DES_specification_satisfied_def epda_to_des_def des_langUM_def des_langM_def less_eq_DES_ext_def lesseqDES_def nonblockingness_language_def DES_nonblockingness_def DES_controllability_def append_alphabet_def SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def inf_DES_ext_def infDES_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def)
   apply(force)
  apply(rule F_DPDA_DFA_CC__SpecOutput__TO__SCP_Closed_Loop_Satisfactory)
   apply(force)
  apply(force)
  done


hide_fact F_DPDA_DFA_CC__fp_start__corresponds_to__FPiteratorMarked__fp_start
hide_fact F_DPDA_DFA_CC__fp_start__SOUND
hide_fact F_DPDA_DFA_CC__SOUND

end

