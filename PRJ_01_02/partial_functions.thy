section {*partial\_functions*}
theory
  partial_functions

imports
  PRJ_01_02__ENTRY

begin

lemma partial_termination_wf_prime: "
  \<forall>x::'\<alpha>. RECURSIVE_COND x \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL x)
  \<Longrightarrow> \<forall>x::'\<alpha>. RECURSIVE_COND x \<and> TERM_ARGS_TEST x \<longrightarrow> ((MEASURE::'\<alpha>\<Rightarrow>nat) x)>(MEASURE (MODIFY_ARGS_FOR_REC_CALL x))
  \<Longrightarrow> \<forall>x::'\<alpha>. (\<not>(RECURSIVE_COND x)) \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_FUN x
  \<Longrightarrow> \<forall>x::'\<alpha>. TERM_FUN (MODIFY_ARGS_FOR_REC_CALL x) \<and> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL x) \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_FUN x
  \<Longrightarrow> \<forall>y. x = MEASURE y \<and> TERM_ARGS_TEST y \<longrightarrow> TERM_FUN y"
  apply(rule nat_less_induct)
  apply(rename_tac n)(*strict*)
  apply(clarify)
  apply(rename_tac n y)(*strict*)
  apply(erule_tac
      x = "y"
      and P = "\<lambda>y. TERM_FUN (MODIFY_ARGS_FOR_REC_CALL y) \<and> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL y) \<and> TERM_ARGS_TEST y \<longrightarrow> TERM_FUN y"
      in allE)
  apply(rename_tac n y)(*strict*)
  apply(case_tac "RECURSIVE_COND y")
   apply(rename_tac n y)(*strict*)
   apply(subgoal_tac "TERM_FUN (MODIFY_ARGS_FOR_REC_CALL y)")
    apply(rename_tac n y)(*strict*)
    apply(rule_tac
      P = "TERM_FUN (MODIFY_ARGS_FOR_REC_CALL y) \<and> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL y) \<and> TERM_ARGS_TEST y"
      in mp)
     apply(rename_tac n y)(*strict*)
     apply(blast)
    apply(rename_tac n y)(*strict*)
    apply(clarify)
    apply(force)
   apply(rename_tac n y)(*strict*)
   defer
   apply(blast)
  apply(rename_tac n y)(*strict*)
  apply(erule_tac
      x = "MEASURE (MODIFY_ARGS_FOR_REC_CALL y)"
      in allE)
  apply(erule_tac
      P = "MEASURE (MODIFY_ARGS_FOR_REC_CALL y) < MEASURE y"
      in impE)
   apply(rename_tac n y)(*strict*)
   defer
   apply(erule_tac
      x = "MODIFY_ARGS_FOR_REC_CALL y"
      and P = "\<lambda>ya. MEASURE (MODIFY_ARGS_FOR_REC_CALL y) = MEASURE ya \<and> TERM_ARGS_TEST ya \<longrightarrow> TERM_FUN ya"
      in allE)
   apply(rename_tac n y)(*strict*)
   apply(blast)
  apply(rename_tac n y)(*strict*)
  apply(erule_tac
      x = "y"
      and P = "\<lambda>y. RECURSIVE_COND y \<and> TERM_ARGS_TEST y \<longrightarrow> MEASURE (MODIFY_ARGS_FOR_REC_CALL y) < MEASURE y"
      in allE)
  apply(rename_tac n y)(*strict*)
  apply(clarify)
  done

lemma partial_termination_wf: "
  \<forall>x. RECURSIVE_COND x \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL x)
  \<Longrightarrow> \<forall>x. RECURSIVE_COND x \<and> TERM_ARGS_TEST x \<longrightarrow> ((MEASURE::'\<alpha>\<Rightarrow>nat) x)>(MEASURE (MODIFY_ARGS_FOR_REC_CALL x))
  \<Longrightarrow> \<forall>x. \<not>RECURSIVE_COND x \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_FUN x
  \<Longrightarrow> \<forall>x. TERM_FUN (MODIFY_ARGS_FOR_REC_CALL x) \<and> TERM_ARGS_TEST (MODIFY_ARGS_FOR_REC_CALL x) \<and> TERM_ARGS_TEST x \<longrightarrow> TERM_FUN x
  \<Longrightarrow> TERM_ARGS_TEST y
  \<Longrightarrow> TERM_FUN y"
  apply(subgoal_tac "TERM_ARGS_TEST y \<longrightarrow> TERM_FUN y")
   apply(blast)
  apply(subgoal_tac "\<forall>x. \<forall>y. x = MEASURE y \<and> TERM_ARGS_TEST y \<longrightarrow> TERM_FUN y")
   apply(blast)
  apply(rule allI)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x = "x"
      and RECURSIVE_COND = "RECURSIVE_COND"
      and MODIFY_ARGS_FOR_REC_CALL = "MODIFY_ARGS_FOR_REC_CALL"
      in partial_termination_wf_prime)
     apply(rename_tac x)(*strict*)
     apply(blast) +
  done

lemma partial_nat_less_induct_strenthen: "
  \<forall>n. (\<forall>x. valid_item_set_INPUT x \<longrightarrow> (MEASURE::'\<alpha>\<Rightarrow>nat) x < n \<longrightarrow> P x) \<longrightarrow> (\<forall>x. valid_item_set_INPUT x \<longrightarrow> MEASURE x = n \<longrightarrow> P x)
  \<Longrightarrow> \<forall>x. valid_item_set_INPUT x \<longrightarrow> P x \<longrightarrow> Q x
  \<Longrightarrow> valid_item_set_INPUT y
  \<Longrightarrow> Q y"
  apply(subgoal_tac "\<forall>n. \<forall>y. valid_item_set_INPUT y \<longrightarrow> MEASURE y = n \<longrightarrow> P y")
   apply(blast)
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      n = "n"
      in nat_less_induct)
  apply(rename_tac n na)(*strict*)
  apply(auto)
  done

end
