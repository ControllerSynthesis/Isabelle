section {*FUNCTION\_\_FRESH*}
theory
  FUNCTION__FRESH

imports
  PRJ_12_02__ENTRY

begin

lemma infinite_symbol_set: "
  inj_on f (UNIV::nat set)
  \<Longrightarrow> f ` (UNIV::nat set) \<subseteq> (UNIV::'a DT_symbol set)
  \<Longrightarrow> \<not> (finite (UNIV:: ('a DT_symbol) set))"
  apply (metis finite_vimageI infinite_UNIV_nat vimage_UNIV)
  done

lemma inj_on_exists: "
  finite A
  \<Longrightarrow> \<exists>f::'x \<Rightarrow> 'a DT_symbol. inj_on f A"
  apply(rule_tac
      B = "(UNIV::'a DT_symbol set)"
      in inj_on_from_infinite_set)
   apply(force)
  apply(rule_tac
      f = "cons_symbol_nat"
      in infinite_symbol_set)
   apply(simp add: inj_on_def)
  apply(force)
  done

theorem SOME_injective_is_injective: "
  finite A
  \<Longrightarrow> inj_on (SOME f::'x\<Rightarrow>'a DT_symbol. inj_on f A) A"
  apply(subgoal_tac "\<exists>f::'x \<Rightarrow> 'a DT_symbol. inj_on f A")
   prefer 2
   apply(rule inj_on_exists)
   apply(force)
  apply(clarsimp)
  apply(rename_tac f)(*strict*)
  apply(rule_tac
      P = "\<lambda>f. inj_on f A"
      in someI_ex)
  apply(rule_tac
      x = "f"
      in exI)
  apply(force)
  done

theorem exists_SOME_injective_is_injective: "
  finite A
  \<Longrightarrow> \<exists>f. inj_on f A \<and> f = (SOME f::'x\<Rightarrow>'a DT_symbol. inj_on f A)"
  apply(rule_tac
      x = "(SOME f::'x\<Rightarrow>'a DT_symbol. inj_on f A)"
      in exI)
  apply(clarsimp)
  apply(rule SOME_injective_is_injective)
  apply(force)
  done

lemma symbol_annotate_makesInfinite: "
  \<not> (finite {cons_symbol_nat n | n. True})"
  apply(case_tac "\<not>(finite {cons_symbol_nat n| n. True})")
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(clarify)
   apply(force)
  apply(subgoal_tac "finite ((\<lambda>n. cons_symbol_nat n) -` ({cons_symbol_nat n |n. True}))")
   apply(force)
  apply(rule Finite_Set.finite_vimageI)
   apply(force)
  apply(rule injI)
  apply(rename_tac x y)(*strict*)
  apply(clarsimp)
  done

lemma new_elem_exists: "
  finite Q
  \<Longrightarrow> \<exists>n. cons_symbol_nat n \<notin> Q"
  apply(case_tac "\<exists>n. cons_symbol_nat n \<notin> Q")
   apply(clarsimp)
  apply(subgoal_tac "False")
   apply(auto)
  apply(subgoal_tac "\<not>(finite Q)")
   apply(clarsimp)
  apply(rule_tac
      A = "{cons_symbol_nat n| n. True}"
      in notFinite_subset)
   apply(metis symbol_annotate_makesInfinite)
  apply(auto)
  done

lemma F_FRESH__recursive_termination: "
  finite Q
  \<Longrightarrow> F_FRESH__recursive_dom (Q, n)"
  apply(subgoal_tac "\<exists>m. cons_symbol_nat m \<notin> (Q\<union>{cons_symbol_nat k| k. k < n})")
   prefer 2
   apply(rule_tac new_elem_exists)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(rename_tac k)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(Q,n). finite Q \<and> cons_symbol_nat k \<notin> Q \<and> \<not>k < n"
      and RECURSIVE_COND = "\<lambda>(Q,n). (cons_symbol_nat n)\<in> Q"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(Q,n). (Q,Suc n)"
      and MEASURE = "\<lambda>(Q,n). (Suc k) - n"
      in partial_termination_wf)
      apply(rename_tac k)(*strict*)
      apply(auto)
    apply(rename_tac k a b)(*strict*)
    apply(subgoal_tac "b = k")
     apply(rename_tac k a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac k a b)(*strict*)
    apply(arith)
   apply(rename_tac k a b)(*strict*)
   apply(thin_tac "finite Q")
   apply(thin_tac "cons_symbol_nat k \<notin> Q")
   apply(thin_tac "\<not> k < b")
   apply(rule_tac F_FRESH__recursive.domintros)
   apply(blast)
  apply(rule_tac F_FRESH__recursive.domintros)
  apply(force)
  done

lemma F_FRESH__recursive_is_F_FRESH__recursive: "
  finite Q
  \<Longrightarrow> F_FRESH__recursive Q n \<notin> Q"
  apply(subgoal_tac "\<exists>m. cons_symbol_nat m \<notin> (Q\<union>{cons_symbol_nat k| k. k < n})")
   prefer 2
   apply(rule_tac new_elem_exists)
   defer
   apply(erule exE)
   apply(rename_tac m)(*strict*)
   apply(rename_tac k)
   apply(rename_tac k)(*strict*)
   apply(subgoal_tac "(\<lambda>(Q,n). F_FRESH__recursive Q n \<notin> Q)(Q,n)")
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(Q,n). finite Q \<and> cons_symbol_nat k \<notin> Q \<and> \<not>k < n"
      and RECURSIVE_COND = "\<lambda>(Q,n). (cons_symbol_nat n)\<in> Q"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(Q,n). (Q,Suc n)"
      and MEASURE = "\<lambda>(Q,n). (Suc k) - n"
      and TERM_FUN = "\<lambda>(Q,n). F_FRESH__recursive Q n \<notin> Q"
      and y = "(Q,n)"
      in partial_termination_wf)
       apply(rename_tac k)(*strict*)
       apply(auto)
    apply(rename_tac k a b)(*strict*)
    apply(subgoal_tac "b = k")
     apply(rename_tac k a b)(*strict*)
     apply(clarsimp)
    apply(rename_tac k a b)(*strict*)
    apply(arith)
   apply(rename_tac k a b)(*strict*)
   apply(thin_tac "finite Q")
   apply(thin_tac "\<not> k < n")
   defer
   apply(rename_tac k a b)(*strict*)
   apply(thin_tac "finite Q")
   apply(thin_tac "cons_symbol_nat k \<notin> Q")
   apply(thin_tac "\<not> k < n")
   apply(rename_tac Q n)
   apply(rename_tac k Q n)(*strict*)
   apply(subgoal_tac "F_FRESH__recursive Q n \<notin> Q")
    apply(rename_tac k Q n)(*strict*)
    apply(blast)
   apply(rename_tac k Q n)(*strict*)
   apply(rule_tac
      t = "F_FRESH__recursive Q n"
      and s = "(if cons_symbol_nat n \<notin> Q then cons_symbol_nat n else F_FRESH__recursive Q (Suc n))"
      in ssubst)
    apply(rename_tac k Q n)(*strict*)
    apply(rule F_FRESH__recursive.psimps)
    apply(rule F_FRESH__recursive_termination)
    apply(blast)
   apply(rename_tac k Q n)(*strict*)
   apply(clarsimp)
  apply(thin_tac "cons_symbol_nat k \<notin> Q")
  apply(rename_tac k Q n)(*strict*)
  apply(subgoal_tac "F_FRESH__recursive Q n \<notin> Q")
   apply(rename_tac k Q n)(*strict*)
   apply(blast)
  apply(rename_tac k Q n)(*strict*)
  apply(rule_tac
      t = "F_FRESH__recursive Q n"
      and s = "(if cons_symbol_nat n \<notin> Q then cons_symbol_nat n else F_FRESH__recursive Q (Suc n))"
      in ssubst)
   apply(rename_tac k Q n)(*strict*)
   apply(rule F_FRESH__recursive.psimps)
   apply(rule F_FRESH__recursive_termination)
   apply(blast)
  apply(rename_tac k Q n)(*strict*)
  apply(clarsimp)
  done

theorem F_FRESH_is_fresh: "
  finite Q
  \<Longrightarrow> F_FRESH Q \<notin> Q"
  apply(simp add: F_FRESH_def)
  apply(metis F_FRESH__recursive_is_F_FRESH__recursive)
  done

end
