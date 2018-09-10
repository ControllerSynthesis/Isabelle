section {*lists\_append\_Cons*}
theory
  lists_append_Cons

imports
  sets

begin

lemma append_take_drop_id_extended: "
  take n w @ drop n w @ c = w @ c"
  apply (simp) 
  done

lemma Cons_inj: "
  [x] = [y]
  \<Longrightarrow> x = x'
  \<Longrightarrow> y = y'
  \<Longrightarrow> x' = y'"
  apply(force)
  done

lemma ConsApp: "
  a # w = [a] @ w"
  apply(auto)
  done

lemma triv_double_append: "
  xa @ e = w @ [X] 
  \<Longrightarrow> xb @ [X] = e 
  \<Longrightarrow> xa @ xb = w"
  apply(force)
  done

lemma list_arg_cong2_append: "
  a = b 
  \<Longrightarrow> w = v 
  \<Longrightarrow> w @ a = x 
  \<Longrightarrow> v @ b = y 
  \<Longrightarrow> x = y"
  apply(force)
  done

lemma append_injr: "
  a @ v = b @ v 
  \<Longrightarrow> a = b"
  apply(force)
  done

lemma append_linj: "
  w @ a = w @ b 
  \<Longrightarrow> a = b"
  apply(auto)
  done

lemma equal_by_pre_context: "
  a @ b = c 
  \<Longrightarrow> a @ d = c 
  \<Longrightarrow> b = d"
  apply(rule_tac
      t = "b"
      and s = "drop (length a) (a@b)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "d"
      and s = "drop (length a) (a@d)"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma append_injective1: "
  w @ a = v @ b 
  \<Longrightarrow> a = b 
  \<Longrightarrow> w = v"
  apply(auto)
  done

lemma append_injective2: "
  w @ a = v @ b 
  \<Longrightarrow> w = v 
  \<Longrightarrow> a = b"
  apply(auto)
  done

lemma listEqI_head: "
  a = b 
  \<Longrightarrow> w = v 
  \<Longrightarrow> x = a # w 
  \<Longrightarrow> y = b # v 
  \<Longrightarrow> x = y"
  apply(force)
  done

lemma listEqI_heads: "
  a = b 
  \<Longrightarrow> w = v 
  \<Longrightarrow> x = a @ w 
  \<Longrightarrow> y = b @ v 
  \<Longrightarrow> x = y"
  apply(force)
  done

lemma NoteAboutRev: "
  t\<pi>' = tr' # t\<pi>'' 
  \<Longrightarrow> (List.rev t\<pi>'') @ [tr'] = List.rev t\<pi>'"
  apply(auto)
  done

lemma unequal_by_first_char: "
  a \<noteq> b 
  \<Longrightarrow> a # w = x 
  \<Longrightarrow> b # v = y 
  \<Longrightarrow> x \<noteq> y"
  apply(auto)
  done

lemma lang_eq_by_left_addition: "
  (\<lambda>x. w@x) ` A = (\<lambda>x. w@x) ` B
  \<Longrightarrow> A = B"
  apply(force)
  done

lemma StrDiff: "
  x\<notin>{[],[a]}
  \<Longrightarrow> y\<notin>{[],[a]}
  \<Longrightarrow> x@y \<noteq> [a]"
  apply(auto)
  apply(case_tac "x")
   apply(auto)
  done

lemma NotemptyString: "
  \<exists>v a. c = v@[a]
  \<Longrightarrow> c \<noteq> []"
  apply(auto)
  done

lemma emptyString: "
  c \<noteq> []
  \<Longrightarrow> \<exists>v a. c = v@[a]"
  apply(rule_tac
      P = "c \<noteq> []"
      and Q = "\<exists> v a. c = v@[a]"
      in impE)
    apply(rule_tac
      xs = "c"
      in rev_induct)
     apply(simp)
    apply(rename_tac x xs)(*strict*)
    defer
    apply(simp)
   apply(simp)
  apply(rename_tac x xs)(*strict*)
  apply(auto)
  done

lemma drop_last_both_eq: "
  w@[x] = v@[x]
  \<Longrightarrow> w = v"
  apply(force)
  done

lemma concat_asso: "
  x @ (y @ z) = (x @ y) @ z"
  apply(rule_tac
      list = "x"
      in list.induct)
   apply(auto)
  done

lemma oneElem_neq_triv: "
  ([a] \<noteq> [b]) = (a \<noteq> b)"
  apply(auto)
  done

lemma listEqI1: "
  a = b
  \<Longrightarrow> [a] = [b]"
  apply(auto)
  done

lemma length_1_context_empty: "
  [x] = w1 @ [y] @ w2
  \<Longrightarrow> w1 = [] \<and> w2 = [] \<and> x = y"
  apply(subgoal_tac "[x] = w1 @ [y] @ w2 \<longrightarrow> w1 = [] \<and> w2 = [] \<and> x = y")
   apply(blast)
  apply(thin_tac "[x] = w1 @ [y] @ w2")
  apply(induct_tac w1)
   apply(auto)
  done

lemma length_1_context_left_empty_left: "
  w1 @ [x] = [x]
  \<Longrightarrow> w1 = []"
  apply(subgoal_tac "w1 @ [x] = [x] \<longrightarrow> w1 = []")
   apply(blast)
  apply(rule_tac
      list = "w1"
      in list.induct)
   apply(auto)
  done

lemma length_1_context_both_empty_left: "
  w1 @ [x] @ w2 = [y]
  \<Longrightarrow> w1 = []"
  apply(subgoal_tac "w1 @ [x] @ w2 = [y] \<longrightarrow> w1 = []")
   apply(blast)
  apply(rule_tac
      list = "w1"
      in list.induct)
   apply(auto)
  done

lemma length_1_context_both_empty_right: "
  w1 @ [x] @ w2 = [y]
  \<Longrightarrow> w2 = []"
  apply(subgoal_tac "w1 @ [x] @ w2 = [y] \<longrightarrow> w2 = []")
   apply(blast)
  apply(rule_tac
      list = "w1"
      in list.induct)
   apply(auto)
  done

lemma listeq_by_mutual_append: "
  v1 = w1 @ v2
  \<Longrightarrow> v2 = w2 @ v1
  \<Longrightarrow> w1 = [] \<and> w2 = []"
  apply(force)
  done

lemma last_append_not_empty: "
  v1 \<noteq> []
  \<Longrightarrow> last v1 = last v2
  \<Longrightarrow> last (w @ v1) = last v2"
  apply(force)
  done

lemma last_Cons_not_empty: "
  v1 \<noteq> []
  \<Longrightarrow> last v1 = last v2
  \<Longrightarrow> last (x # v1) = last v2"
  apply(force)
  done

end
