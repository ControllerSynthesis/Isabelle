section {*lists\_set*}
theory
  lists_set

imports
  lists_append_Cons

begin

lemma nset_diff: "
  x  \<in> set w
  \<Longrightarrow> set w \<subseteq> A - {x}
  \<Longrightarrow> P"
  apply(force)
  done

lemma not_in_diff: "
  set x \<subseteq> A - {y}
  \<Longrightarrow> y \<notin> set x"
  apply(force)
  done

lemma triv_compl: "
  set w \<subseteq> A - {X}
  \<Longrightarrow> X \<notin> set w"
  apply(force)
  done

lemma set_append_contra1: "
  a \<in> set w
  \<Longrightarrow>a\<notin>(set (w@v))
  \<Longrightarrow>P"
  apply(force)
  done

lemma set_append_contra2: "
  a \<in> set w
  \<Longrightarrow>a\<notin>(set (v@w))
  \<Longrightarrow>P"
  apply(force)
  done

lemma set_Cons: "
  set (a#w) = {a} \<union> set w"
  apply(force)
  done

lemma map_set_subset: "
  set w \<subseteq> A
  \<Longrightarrow> set (map f w) \<subseteq> f ` A"
  apply(auto)
  done

lemma set_app_subset: "
  set w \<subseteq> set (w@v)"
  apply(force)
  done

lemma elim_Some_from_list: "
  None \<notin> set w
  \<Longrightarrow> \<exists>v. map Some v = w"
  apply(induct w)
   apply(auto)
  apply(rename_tac a v)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v)(*strict*)
   apply(auto)
  apply(rename_tac v aa)(*strict*)
  apply(rule_tac
      x = "aa#v"
      in exI)
  apply(auto)
  done

lemma set_append1: "
  set a \<subseteq> set (a@b)"
  apply(clarsimp)
  done

lemma set_append2: "
  set a \<subseteq> set (b@a)"
  apply(clarsimp)
  done

lemma not_set_append: "
  a\<notin> set w
  \<Longrightarrow> a\<notin>set v
  \<Longrightarrow> a\<notin>(set (w@v))"
  apply(force)
  done

lemma set_bi_append: "
  set w \<subseteq> set (w1@w@w2)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma elem_set_app: "
  a \<notin> set (w @ v)
  \<Longrightarrow> a  \<in> set v
  \<Longrightarrow> P"
  apply(auto)
  done

lemma set_subset_in: "
  set ([q]) \<subseteq> A
  \<Longrightarrow> q  \<in> A"
  apply(force)
  done

lemma set_subset_in2: "
  q  \<in> A
  \<Longrightarrow> set ([q]) \<subseteq> A"
  apply(force)
  done

lemma set_take_head: "
  a \<noteq> b
  \<Longrightarrow> a \<notin> set w
  \<Longrightarrow> a \<notin> set(b#w)"
  apply(auto)
  done

lemma head_in_set: "
  w = a#w'
  \<Longrightarrow> a \<in> set w"
  apply(force)
  done

lemma set_take_head2: "
  a \<in> A
  \<Longrightarrow> set w \<subseteq> A
  \<Longrightarrow> set (a#w) \<subseteq> A"
  apply(auto)
  done

lemma set_concat_subset: "
  set a \<subseteq> A
  \<Longrightarrow> set b \<subseteq> A
  \<Longrightarrow> set (a@b)\<subseteq>A"
  apply(auto)
  done

end

