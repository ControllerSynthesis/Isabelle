section {*two\_elements*}
theory
  two_elements  

imports
  miscellaneous  

begin

declare [[ hypsubst_thin = false ]]
datatype ('a, 'b) DT_two_elements =
  teA "'a"
  | teB "'b"
declare [[ hypsubst_thin = true ]]


primrec setA :: "(('a, 'b) DT_two_elements) list \<Rightarrow> 'a set" where
  "setA [] = {}"
| "setA (x # w) = setA w \<union> (case x of teA a \<Rightarrow> {a} | teB b \<Rightarrow> {})"

primrec setB :: "(('a, 'b) DT_two_elements) list \<Rightarrow> 'b set" where
  "setB [] = {}"
| "setB (x # w) = setB w \<union> (case x of teA a \<Rightarrow> {} | teB b \<Rightarrow> {b})"

primrec liftA :: "'a list \<Rightarrow> ('a,'b)DT_two_elements list" where
  "liftA [] = []"
| "liftA (A # w) = teA A # liftA w"

primrec liftB :: "'b list \<Rightarrow> ('a,'b)DT_two_elements list" where
  "liftB [] = []"
| "liftB (b # w) = teB b # liftB w"

primrec filterA :: "('a,'b) DT_two_elements list \<Rightarrow> 'a list" where
  "filterA [] = []"
| "filterA (x # w) = (case x of teA A \<Rightarrow> [A] | teB b \<Rightarrow> [])@filterA w"

primrec filterB :: "('a,'b)DT_two_elements list \<Rightarrow> 'b list" where
  "filterB [] = []"
| "filterB (x # w) = (case x of teB b \<Rightarrow> [b] | teA A \<Rightarrow> [])@filterB w"

definition two_elements_construct_domain :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a,'b)DT_two_elements set" where
  "two_elements_construct_domain A B \<equiv> teA ` A \<union> teB ` B"

lemma setB_decomp: "
  x  \<in> setB w
  \<Longrightarrow> \<exists>w1 w2. w1 @ [teB x] @ w2 = w"
  apply(subgoal_tac "\<forall>w. \<forall>x. x  \<in> setB w \<longrightarrow> (\<exists>w1 w2. w1 @ [teB x] @ w2 = w)")
   apply(erule_tac
      x = "w"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac wa)(*strict*)
  apply(induct_tac wa)
   apply(rename_tac wa)(*strict*)
   apply(rule allI)
   apply(rename_tac wa xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa a list)(*strict*)
  apply(rule allI)
  apply(rename_tac wa a list xa)(*strict*)
  apply(rule impI)
  apply(case_tac "a = teB xa")
   apply(rename_tac wa a list xa)(*strict*)
   apply(auto)
   apply(rename_tac a list xa)(*strict*)
   apply(erule_tac
      x = "xa"
      in allE)
   apply(auto)
   apply(rename_tac a xa w1 w2)(*strict*)
   apply(rule_tac
      x = "a # w1"
      in exI)
   apply(rule_tac
      x = "w2"
      in exI)
   apply(auto)
  apply(rename_tac a list xa)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list xa aa)(*strict*)
   apply(auto)
  done

lemma unequal_by_setA: "
  A \<in> setA w
  \<Longrightarrow> A\<notin>setA v
  \<Longrightarrow> w \<noteq> v"
  apply(auto)
  done

lemma setA_liftB_exists: "
  setA w = {}
  \<Longrightarrow> \<exists>v. w = liftB v"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac v b)(*strict*)
  apply(rule_tac
      x = "b # v"
      in exI)
  apply(clarsimp)
  done

lemma maxSplit: "
  \<exists>w1 w2. liftB w1 @ w2 = w \<and> (case w2 of teB b # list \<Rightarrow> False | _ \<Rightarrow> True)"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(case_tac "w2")
   apply(rename_tac a w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w1)(*strict*)
   apply(case_tac a)
    apply(rename_tac a w1 aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 aa)(*strict*)
    apply(rule_tac
      x = "[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a w1 b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 b)(*strict*)
   apply(rule_tac
      x = "b # w1"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w1 w2 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w1 aa list)(*strict*)
  apply(case_tac aa)
   apply(rename_tac a w1 aa list ab)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w1 list ab)(*strict*)
   apply(case_tac a)
    apply(rename_tac a w1 list ab aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 list ab aa)(*strict*)
    apply(rule_tac
      x = "[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a w1 list ab b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 list ab b)(*strict*)
   apply(rule_tac
      x = "b # w1"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w1 aa list b)(*strict*)
  apply(clarsimp)
  done

lemma setA_empty_liftB_construct: "
  setA w = {}
  \<Longrightarrow> \<exists>v. liftB v = w"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac v b)(*strict*)
  apply(rule_tac
      x = "b # v"
      in exI)
  apply(clarsimp)
  done

lemma setA_Cons_teB: "
  setA y \<subseteq> A
  \<Longrightarrow> setA (teB a # y) \<subseteq> A"
  apply(auto)
  done

lemma setA_Cons_teA: "
  setA y \<subseteq> A
  \<Longrightarrow> a  \<in> A
  \<Longrightarrow> setA (teA a # y) \<subseteq> A"
  apply(auto)
  done

lemma setB_Cons_teA: "
  setB y \<subseteq> A
  \<Longrightarrow> setB (teA a # y) \<subseteq> A"
  apply(auto)
  done

lemma setB_Cons_teB: "
  setB y \<subseteq> A
  \<Longrightarrow> a  \<in> A
  \<Longrightarrow> setB (teB a # y) \<subseteq> A"
  apply(auto)
  done

lemma unequal_setA: "
  w = v
  \<Longrightarrow> setA w \<noteq> setA v
  \<Longrightarrow> P"
  apply(force)
  done

lemma setB_set_not: "
  a \<notin> setB w
  \<Longrightarrow> teB a \<notin> set w"
  apply(induct w)
   apply(auto)
  done

lemma setA_set_not: "
  a \<notin> setA w
  \<Longrightarrow> teA a \<notin> set w"
  apply(induct w)
   apply(auto)
  done

lemma nth_setA: "
  w!i = teA A
  \<Longrightarrow> i < length w
  \<Longrightarrow> setA w = {}
  \<Longrightarrow> P"
  apply(subgoal_tac "setA w \<noteq> {}")
   apply(clarsimp)
  apply(induct w arbitrary: i A)
   apply(rename_tac i A)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i A)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w i A aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i A b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w i A b)(*strict*)
  apply(case_tac i)
   apply(rename_tac w i A b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w i A b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w A nat)(*strict*)
  apply(erule_tac
      x = "nat"
      in meta_allE)
  apply(erule_tac
      x = "A"
      in meta_allE)
  apply(auto)
  done

lemma terminal_end_suffix: "
  setA x = {}
  \<Longrightarrow> w @ x = y @ teA A # z
  \<Longrightarrow> \<exists>r'. z = r' @ x"
  apply(subgoal_tac "length w + length x = length y + (Suc 0) + length z")
   prefer 2
   apply(subgoal_tac "length (w@x) = length(y @ teA A # z)")
    prefer 2
    apply(force)
   apply(rule_tac
      t = "length w + length x"
      and s = "length (w@x)"
      in ssubst)
    apply(rule sym)
    apply(rule length_append)
   apply(clarsimp)
  apply(case_tac "length x>length z")
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(clarsimp)
   apply(subgoal_tac "length w \<le> length y")
    prefer 2
    apply(arith)
   apply(rule_tac
      w = "x"
      and A = "A"
      and i = "(length y - (length w))"
      in nth_setA)
     apply(auto)
   apply(rule_tac
      t = "x ! (length y - length w)"
      and s = "(w@x) ! (length y)"
      in ssubst)
    apply(rule_tac
      t = "(w @ x) ! (length y)"
      and s = "(if (length y) < length w then w ! (length y) else x ! (length y - length w))"
      in ssubst)
     apply(rule nth_append)
    apply(subgoal_tac "length y \<ge> length w")
     prefer 2
     apply(arith)
    apply(force)
   apply(rule_tac
      t = "w@x"
      and s = "y @ teA A # z"
      in ssubst)
    apply(force)
   apply(rule nth_append_length)
  apply(subgoal_tac "length (w@x) = length(y @ teA A # z)")
   prefer 2
   apply(force)
  apply(rule_tac
      t = "length w + length x"
      and s = "length (w@x)"
      in ssubst)
   apply(rule sym)
   apply(rule length_append)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n. length z = n + length x")
   prefer 2
   apply(rule_tac
      x = "length z - length x"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      x = "take n z"
      in exI)
  apply(rule_tac
      t = "x"
      and s = "drop n z"
      in ssubst)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t = "x"
      and s = "drop (length w) (w@x)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule_tac
      t = "z"
      and s = "drop (Suc(length y)) (w@x)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t = "w@x"
      and s = "(y @ [teA A]) @ z"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule sym)
   apply(rule_tac
      w = "y@[teA A]"
      in drop_append2)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule sym)
  apply(rule_tac
      w = "w"
      in drop_append2)
  apply(force)
  done

lemma border_left: "
  setA w = {}
  \<Longrightarrow> w @ v = l @ teA A # r
  \<Longrightarrow> l = w @ drop (length w) l"
  apply(induct l arbitrary: w)
   apply(rename_tac w)(*strict*)
   apply(auto)
   apply(case_tac w)
    apply(rename_tac w)(*strict*)
    apply(auto)
  apply(rename_tac a l w)(*strict*)
  apply(case_tac w)
   apply(rename_tac a l w)(*strict*)
   apply(auto)
  done

lemma setA_take_head: "
  setA w\<subseteq>setA (a#w)"
  apply(auto)
  done

lemma filterB_take: "
  setA w = {}
  \<Longrightarrow> filterB (take k w) = take k (filterB w)"
  apply(induct w arbitrary: k)
   apply(rename_tac k)(*strict*)
   apply(auto)
  apply(rename_tac a w k)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w k aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w k b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w k b)(*strict*)
  apply(case_tac k)
   apply(rename_tac w k b)(*strict*)
   apply(auto)
  done

lemma set_liftB_insert: "
  a  \<in> set y
  \<Longrightarrow> teB a  \<in> set (liftB y)"
  apply(induct y)
   apply(force)
  apply(rename_tac aa y)(*strict*)
  apply(force)
  done

lemma set_liftB_commute: "
  set x \<subseteq> set y
  \<Longrightarrow> set(liftB x) \<subseteq> set(liftB y)"
  apply(induct x arbitrary: y)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac a x y)(*strict*)
  apply(clarsimp)
  apply(rule set_liftB_insert)
  apply(force)
  done

lemma liftB_commute_one_elem_app: "
  liftB (v@[x]) = liftB v @ [teB x]"
  apply(induct v)
   apply(auto)
  done

lemma last_elem_liftB_eq: "
  z \<noteq> []
  \<Longrightarrow> w @ liftB (v @ [x]) = y @ z
  \<Longrightarrow> \<exists>z'. z = z' @ [teB x]"
  apply(induct z arbitrary: w v y rule: rev_induct)
   apply(rename_tac w v y)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa xs w v y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "w @ liftB v @ [teB x] = y @ xs @ [xa]")
   apply(rename_tac xa xs w v y)(*strict*)
   prefer 2
   apply(rule_tac
      s = "liftB (v@[x])"
      and t = "liftB v @ [teB x]"
      in subst)
    apply(rename_tac xa xs w v y)(*strict*)
    apply(rule liftB_commute_one_elem_app)
   apply(rename_tac xa xs w v y)(*strict*)
   apply(force)
  apply(rename_tac xa xs w v y)(*strict*)
  apply(thin_tac "w @ liftB (v @ [x]) = y @ xs @ [xa]")
  apply(induct z arbitrary: w v y rule: rev_induct)
   apply(rename_tac xa xs w v y)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa xs xaa xsa w v y)(*strict*)
  apply(clarsimp)
  done

lemma setB_triv: "
  a \<in> setB [teB a]"
  apply(auto)
  done

lemma finite_two_elements_construct_domain: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> finite (two_elements_construct_domain A B)"
  apply(simp add: two_elements_construct_domain_def)
  done

lemma setA_setmp_concat_1: "
  a  \<in> setA w1
  \<Longrightarrow> setA (w1@w2) \<subseteq> A
  \<Longrightarrow> a  \<in> A"
  apply(induct w1)
   apply(auto)
  done

lemma setA_setmp_concat_2: "
  a  \<in> setA w2
  \<Longrightarrow> setA (w1@w2) \<subseteq> A
  \<Longrightarrow> a  \<in> A"
  apply(induct w1)
   apply(auto)
  done

lemma two_elements_construct_domain_append: "
  set w \<subseteq> two_elements_construct_domain A B
  \<Longrightarrow> a  \<in> two_elements_construct_domain A B
  \<Longrightarrow> set (w@[a]) \<subseteq> two_elements_construct_domain A B"
  apply(induct w arbitrary: a)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w aa)(*strict*)
  apply(auto)
  done

lemma match3: "
  w @ [teA A] @ v = [teB b1, teA B, teB b2]
  \<Longrightarrow> w = [teB b1] \<and> v = [teB b2] \<and> A = B"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(force)
  apply(rename_tac list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac lista)(*strict*)
  apply(case_tac lista)
   apply(rename_tac lista)(*strict*)
   apply(force)
  apply(rename_tac lista a list)(*strict*)
  apply(force)
  done

lemma set_setA: "
  teA a \<in> set w
  \<Longrightarrow> a  \<in> (setA w)"
  apply(induct w)
   apply(auto)
  done

lemma elemInsetB: "
  A  \<in> setB (l @ teB A # r)"
  apply(induct_tac l)
   apply(auto)
  done

lemma teA_notInMap: "
  a\<notin> A
  \<Longrightarrow> (teA a) \<notin> (teA ` A)"
  apply(auto)
  done

lemma teB_notInMap: "
  a\<notin> A
  \<Longrightarrow> (teB a) \<notin> (teB ` A)"
  apply(auto)
  done

lemma liftB_lift: "
  set w \<subseteq> A
  \<Longrightarrow> set (liftB w) \<subseteq> two_elements_construct_domain B A"
  apply(induct w)
   apply(simp add: two_elements_construct_domain_def) +
  done

lemma liftBDeConv1: "
  filterB (liftB w) = w"
  apply(induct_tac w)
   apply(auto)
  done

lemma liftBDeConv2: "
  setA w = {}
  \<Longrightarrow> liftB (filterB w) = w"
  apply(subgoal_tac "setA w = {} \<longrightarrow> liftB (filterB w) = w")
   apply(force)
  apply(thin_tac "setA w = {}")
  apply(induct_tac w)
   apply(auto)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(auto)
  done

lemma liftAMap: "
  liftA w = map (\<lambda>x. teA x) w"
  apply(induct_tac w)
   apply(auto)
  done

lemma liftBMap: "
  liftB w = map (\<lambda>x. teB x) w"
  apply(induct_tac w)
   apply(auto)
  done

lemma setA_decomp_R: "
  setA w \<noteq> {}
  \<Longrightarrow> \<exists>w1 w2 A. w1 @ [teA A] @ w2 = w \<and> setA w2 = {}"
  apply(rule_tac
      P = "setA w \<noteq> {}"
      and Q = "\<exists>w1 w2 A. w1 @ [teA A] @ w2 = w \<and> setA w2 = {}"
      in impE)
    defer
    apply(blast)
   apply(blast)
  apply(thin_tac "setA w \<noteq> {}")
  apply(induct_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(rule impI)
  apply(simp)
  apply(case_tac "setA list \<noteq> {}")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w1 w2 A)(*strict*)
   apply(rule_tac
      x = "a#w1"
      in exI)
   apply(rule_tac
      x = "w2"
      in exI)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(rule_tac
      x = "list"
      in exI)
   apply(clarsimp)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  done

lemma setA_decomp: "
  x  \<in> setA w
  \<Longrightarrow> \<exists>w1 w2. w1 @ [teA x] @ w2 = w"
  apply(subgoal_tac "\<forall>w. \<forall>x. x  \<in> setA w \<longrightarrow> (\<exists>w1 w2. w1 @ [teA x] @ w2 = w)")
   apply(erule_tac
      x = "w"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac wa)(*strict*)
  apply(induct_tac wa)
   apply(rename_tac wa)(*strict*)
   apply(rule allI)
   apply(rename_tac wa xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa a list)(*strict*)
  apply(rule allI)
  apply(rename_tac wa a list xa)(*strict*)
  apply(rule impI)
  apply(case_tac "a = teA xa")
   apply(rename_tac wa a list xa)(*strict*)
   apply(auto)
   apply(rename_tac a list xa)(*strict*)
   apply(erule_tac
      x = "xa"
      in allE)
   apply(auto)
   apply(rename_tac a xa w1 w2)(*strict*)
   apply(rule_tac
      x = "a#w1"
      in exI)
   apply(rule_tac
      x = "w2"
      in exI)
   apply(auto)
  apply(rename_tac a list xa)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list xa aa)(*strict*)
   apply(auto)
  done

lemma elemInsetA: "
  A  \<in> setA (l @ teA A # r)"
  apply(induct_tac l)
   apply(auto)
  done

lemma setBConcat: "
  setB (w1 @ w2) = setB w1 \<union> setB w2"
  apply(induct_tac w1)
   apply(auto)
  done

lemma setAConcat: "
  setA (w1 @ w2) = setA w1 \<union> setA w2"
  apply(induct_tac w1)
   apply(auto)
  done

lemma filterB_no_nonterms: "
  setA w = {}
  \<Longrightarrow> set (filterB w) = setB w"
  apply(induct w)
   apply(auto)
  apply(rename_tac a w x)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w x aa)(*strict*)
   apply(auto)
  done

lemma not_in_setBI: "
  teB x \<notin> set w
  \<Longrightarrow> x \<notin> setB w"
  apply(induct w arbitrary: x)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac a w x)(*strict*)
  apply(rule_tac
      t = "a#w"
      and s = "[a]@w"
      in ssubst)
   apply(rename_tac a w x)(*strict*)
   apply(force)
  apply(rename_tac a w x)(*strict*)
  apply(simp only: setBConcat concat_asso)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w x aa)(*strict*)
   apply(force)
  apply(rename_tac a w x b)(*strict*)
  apply(force)
  done

lemma setA_app: "
  setA w \<subseteq> A
  \<Longrightarrow> setA v \<subseteq> A
  \<Longrightarrow> setA (w@v) \<subseteq> A"
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(auto)
  done

lemma has_elem_setA: "
  setB w = {}
  \<Longrightarrow> i < length w
  \<Longrightarrow> \<exists>A. w ! i = teA A"
  apply(subgoal_tac "\<forall>w i. (setB w = {} \<longrightarrow> (i < length w) \<longrightarrow> (\<exists>A. w ! i = teA A))")
   apply(blast)
  apply(rule allI)
  apply(rename_tac wa)(*strict*)
  apply(rule length_induct)
  apply(rename_tac wa xs)(*strict*)
  apply(auto)
  apply(rename_tac xs ia)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs ia)(*strict*)
   apply(auto)
  apply(rename_tac ia a list)(*strict*)
  apply(erule_tac
      x = "list"
      in allE)
  apply(auto)
  apply(case_tac a)
   apply(rename_tac ia a list aa)(*strict*)
   apply(auto)
  apply(rename_tac ia list aa)(*strict*)
  apply(case_tac ia)
   apply(rename_tac ia list aa)(*strict*)
   apply(auto)
  done

lemma context_exists_for_elem_of_setB: "
  x  \<in> setB w
  \<Longrightarrow> \<exists>w1 w2. w = w1 @ teB x # w2"
  apply(subgoal_tac "x  \<in> setB w \<longrightarrow> (\<exists>w1 w2. w = w1 @ [teB x] @ w2)")
   apply(clarsimp)
  apply(thin_tac "x  \<in> setB w")
  apply(induct_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(auto)
    apply(rename_tac a list)(*strict*)
    apply(case_tac a)
     apply(rename_tac a list aa)(*strict*)
     apply(auto)
   apply(rename_tac a w1 w2)(*strict*)
   apply(rule_tac
      x = "a#w1"
      in exI)
   apply(rule_tac
      x = "w2"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w1 w2 aa)(*strict*)
   apply(auto)
  done

lemma setA_with_context_is_not_setB: "
  [teB b] \<noteq> l @ teA x # r"
  apply(induct_tac l)
   apply(auto)
  done

lemma setB_selects_sound1: "
  b  \<in> setB (x @ teB b # w)"
  apply(rule_tac
      list = "x"
      in list.induct)
   apply(clarsimp) +
  done



lemma SetxBiElem_check_vs_set_two_elements_construct_domain_check: "
  setB w \<subseteq> A
  \<Longrightarrow> setA w \<subseteq> B
  \<Longrightarrow> set w \<subseteq> two_elements_construct_domain B A"
  apply(subgoal_tac "\<forall>A B. setB w \<subseteq> A \<and> setA w \<subseteq> B \<longrightarrow> set w \<subseteq> two_elements_construct_domain B A")
   apply(blast)
  apply(thin_tac "setB w \<subseteq> A")
  apply(thin_tac "setA w \<subseteq> B")
  apply(induct_tac w)
   apply(auto)
  apply(rename_tac a list A B)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(erule_tac
      x = "B"
      in allE)
  apply(simp add: two_elements_construct_domain_def)
  apply(case_tac a)
   apply(rename_tac a list A B aa)(*strict*)
   apply(auto)
  done

lemma two_elements_construct_domain_setA: "
  set w \<subseteq> two_elements_construct_domain A B
  \<Longrightarrow> setA w \<subseteq> A"
  apply(induct w)
   apply(simp add: two_elements_construct_domain_def)
  apply(rename_tac a w)(*strict*)
  apply(auto)
  apply(rename_tac a w x)(*strict*)
  apply(simp add: two_elements_construct_domain_def)
  apply(auto)
  done

lemma two_elements_construct_domain_setB: "
  set w \<subseteq> two_elements_construct_domain A B
  \<Longrightarrow> setB w \<subseteq> B"
  apply(induct w)
   apply(simp add: two_elements_construct_domain_def)
  apply(rename_tac a w)(*strict*)
  apply(auto)
  apply(rename_tac a w x)(*strict*)
  apply(simp add: two_elements_construct_domain_def)
  apply(auto)
  done

lemma two_elements_construct_domain_subset: "
  A\<subseteq>A'
  \<Longrightarrow> B\<subseteq>B'
  \<Longrightarrow> two_elements_construct_domain A B \<subseteq> two_elements_construct_domain A' B'"
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(simp add: two_elements_construct_domain_def)
  apply(auto)
  done

lemma setATakeEQ: "
  setA (take (k + (length v)) v) = setA v"
  apply(induct v arbitrary: k)
   apply(rename_tac k)(*strict*)
   apply(auto)
  done

lemma setBTakeEQ: "
  setB (take (k + (length v)) v) = setB v"
  apply(induct v arbitrary: k)
   apply(rename_tac k)(*strict*)
   apply(auto)
  done

lemma setATakeIndexSubset: "
  setA (take k1 v) \<subseteq> setA (take (k1 + k2) v)"
  apply(induct v arbitrary: k1 k2)
   apply(rename_tac k1 k2)(*strict*)
   apply(auto)
  apply(rename_tac a v k1 k2 x)(*strict*)
  apply(case_tac k1)
   apply(rename_tac a v k1 k2 x)(*strict*)
   apply(auto)
  done

lemma setBTakeIndexSubset: "
  setB (take k1 v) \<subseteq> setB (take (k1 + k2) v)"
  apply(induct v arbitrary: k1 k2)
   apply(rename_tac k1 k2)(*strict*)
   apply(auto)
  apply(rename_tac a v k1 k2 x)(*strict*)
  apply(case_tac k1)
   apply(rename_tac a v k1 k2 x)(*strict*)
   apply(auto)
  done

lemma setBTakeIndexSubset2: "
  setB (take k1 v) \<subseteq> setB v"
  apply(rule_tac
      t = "setB v"
      and s = "setB (take (k1 + length v) v)"
      in ssubst)
   apply(force)
  apply(rule setBTakeIndexSubset)
  done

lemma setBDropIndexSubset: "
  setB (drop (k1 + k2) v) \<subseteq> setB (drop k1 v)"
  apply(induct v arbitrary: k1 k2)
   apply(rename_tac k1 k2)(*strict*)
   apply(auto)
  apply(rename_tac a v k1 k2 x)(*strict*)
  apply(case_tac k1)
   apply(rename_tac a v k1 k2 x)(*strict*)
   apply(auto)
  apply(rename_tac a v k2 x)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v k2 x aa)(*strict*)
   apply(auto)
   apply(rename_tac v k2 x aa)(*strict*)
   apply(case_tac k2)
    apply(rename_tac v k2 x aa)(*strict*)
    apply(auto)
   apply(rename_tac v x nat)(*strict*)
   apply(subgoal_tac "setB (drop (0 + nat) v) \<subseteq> setB (drop 0 v)")
    apply(rename_tac v x nat)(*strict*)
    prefer 2
    apply(blast)
   apply(rename_tac v x nat)(*strict*)
   apply(force)
  apply(rename_tac v k2 x b)(*strict*)
  apply(case_tac k2)
   apply(rename_tac v k2 x b)(*strict*)
   apply(auto)
  apply(rename_tac v x b nat)(*strict*)
  apply(subgoal_tac "setB (drop (0 + nat) v) \<subseteq> setB (drop 0 v)")
   apply(rename_tac v x b nat)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac v x b nat)(*strict*)
  apply(force)
  done

lemma setBDropIndexSubset2: "
  setB (drop k1 v) \<subseteq> setB v"
  apply(rule_tac
      t = "k1"
      and s = "0 + k1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "setB v"
      and s = "setB (drop 0 v)"
      in ssubst)
   apply(force)
  apply(rule setBDropIndexSubset)
  done

lemma setATakeIndexSubset2: "
  setA (take k1 v) \<subseteq> setA v"
  apply(rule_tac
      t = "setA v"
      and s = "setA (take (k1 + length v) v)"
      in ssubst)
   apply(force)
  apply(rule setATakeIndexSubset)
  done

lemma setADropIndexSubset: "
  setA (drop (k1 + k2) v) \<subseteq> setA (drop k1 v)"
  apply(induct v arbitrary: k1 k2)
   apply(rename_tac k1 k2)(*strict*)
   apply(auto)
  apply(rename_tac a v k1 k2 x)(*strict*)
  apply(case_tac k1)
   apply(rename_tac a v k1 k2 x)(*strict*)
   apply(auto)
  apply(rename_tac a v k2 x)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v k2 x aa)(*strict*)
   apply(auto)
   apply(rename_tac v k2 x aa)(*strict*)
   apply(case_tac k2)
    apply(rename_tac v k2 x aa)(*strict*)
    apply(auto)
   apply(rename_tac v x aa nat)(*strict*)
   apply(subgoal_tac "setA (drop (0 + nat) v) \<subseteq> setA (drop 0 v)")
    apply(rename_tac v x aa nat)(*strict*)
    prefer 2
    apply(blast)
   apply(rename_tac v x aa nat)(*strict*)
   apply(force)
  apply(rename_tac v k2 x b)(*strict*)
  apply(case_tac k2)
   apply(rename_tac v k2 x b)(*strict*)
   apply(auto)
  apply(rename_tac v x nat)(*strict*)
  apply(subgoal_tac "setA (drop (0 + nat) v) \<subseteq> setA (drop 0 v)")
   apply(rename_tac v x nat)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac v x nat)(*strict*)
  apply(force)
  done

lemma setADropIndexSubset2: "
  setA (drop k1 v) \<subseteq> setA v"
  apply(rule_tac
      t = "k1"
      and s = "0 + k1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "setA v"
      and s = "setA (drop 0 v)"
      in ssubst)
   apply(force)
  apply(rule setADropIndexSubset)
  done

lemma setATakeRestricted: "
  setA (take k v) = {}
  \<Longrightarrow> take k (filterB v) = filterB (take k v)"
  apply(rule_tac
      P = "setA (take k v) = {}"
      and Q = "take k (filterB v) = filterB (take k v)"
      in impE)
    defer
    apply(blast)
   apply(blast)
  apply(induct v arbitrary: k)
   apply(rename_tac k)(*strict*)
   apply(auto)
  apply(rename_tac a v k)(*strict*)
  apply(case_tac a)
   apply(rename_tac a v k aa)(*strict*)
   apply(auto)
   apply(rename_tac v k aa)(*strict*)
   apply(case_tac k)
    apply(rename_tac v k aa)(*strict*)
    apply(auto)
  apply(rename_tac v k b)(*strict*)
  apply(case_tac k)
   apply(rename_tac v k b)(*strict*)
   apply(auto)
  done

lemma set_setBliftB: "
  set x = setB (liftB x)"
  apply(induct x)
   apply(auto)
  done

lemma setB_liftB_subset: "
  set x \<subseteq> A
  \<Longrightarrow> setB (liftB x) \<subseteq> A"
  apply(rule_tac
      t = "setB (liftB x)"
      and s = "set x"
      in subst)
   apply(rule set_setBliftB)
  apply(force)
  done

lemma liftB_reflects_length: "
  length w = length (liftB w)"
  apply(induct_tac w)
   apply(auto)
  done

lemma filterB_reflects_length: "
  setA w = {}
  \<Longrightarrow> length w = length (filterB w)"
  apply(subgoal_tac "setA w = {} \<longrightarrow> length w = length (filterB w)")
   apply(blast)
  apply(thin_tac "setA w = {}")
  apply(induct_tac w)
   apply(auto)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(auto)
  done

lemma set_setB_liftB: "
  set z = setB (liftB z)"
  apply(induct_tac z)
   apply(auto)
  done

lemma setA_liftB_empty: "
  setA (liftB y) = {}"
  apply(induct_tac y)
   apply(auto)
  done

lemma liftB_reflects_Nil: "
  [] = liftB y
  \<Longrightarrow> y = []"
  apply(induct y)
   apply(force)
  apply(rename_tac a y)(*strict*)
  apply(force)
  done

lemma terminalTailEquals1_hlp: "
  setA w2 = {}
  \<Longrightarrow> v1 @ [teA A] = v2 @ teA B # w2
  \<Longrightarrow> [] = w2"
  apply(subgoal_tac "\<forall>v1 A B v2. setA w2 = {} \<and> v1@[teA A] = v2@[teA B]@w2 \<longrightarrow> [] = w2")
   apply(clarsimp)
  apply(rule_tac
      xs = "w2"
      in rev_induct)
   apply(blast)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs Aa)(*strict*)
  apply(auto)
   apply(rename_tac xs Aa x)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(blast)
  apply(rename_tac xs Aa)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(auto)
  done

lemma setB_app: "
  setB w \<subseteq> A
  \<Longrightarrow> setB v \<subseteq> A
  \<Longrightarrow> setB (w@v) \<subseteq> A"
  apply(simp (no_asm) only: setBConcat concat_asso)
  apply(auto)
  done

lemma terminalTailEquals1: "
  setA w1 = {}
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> v1@[teA A]@w1 = v2@[teA B]@w2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "\<forall>w1 w2 v1 v2 A B. setA w1 = {} \<and> setA w2 = {} \<and> v1@[teA A]@w1 = v2@[teA B]@w2 \<longrightarrow> w1 = w2")
   apply(erule_tac
      x = "w1"
      in allE)
   apply(erule_tac
      x = "w2"
      in allE)
   apply(erule_tac
      x = "v1"
      in allE)
   apply(erule_tac
      x = "v2"
      in allE)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "B"
      in allE)
   apply(force)
  apply(rule allI)
  apply(rename_tac w1a)(*strict*)
  apply(rule_tac
      xs = "w1a"
      in rev_induct)
   apply(rename_tac w1a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2a v1a v2a Aa Ba)(*strict*)
   apply(rule terminalTailEquals1_hlp)
    apply(rename_tac w2a v1a v2a Aa Ba)(*strict*)
    apply(blast)
   apply(rename_tac w2a v1a v2a Aa Ba)(*strict*)
   apply(blast)
  apply(rename_tac w1a x xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w2a v1a v2a Aa Ba)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac x xs w2a v1a v2a Aa Ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs Ba)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac x xs w2a v1a v2a Aa Ba a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w2a = w' @ [x']")
   apply(rename_tac x xs w2a v1a v2a Aa Ba a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xs w2a v1a v2a Aa Ba a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs v1a v2a Aa Ba a list w' x')(*strict*)
  apply(erule_tac
      x = "w'"
      in allE)
  apply(erule impE)
   apply(rename_tac xs v1a v2a Aa Ba a list w' x')(*strict*)
   defer
   apply(blast)
  apply(rename_tac xs v1a v2a Aa Ba a list w' x')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(case_tac list)
   apply(rename_tac xs v1a v2a Aa Ba a list w' x')(*strict*)
   apply(auto)
  apply(rename_tac xs v1a v2a Aa Ba a w' x' aa lista x)(*strict*)
  apply(case_tac aa)
   apply(rename_tac xs v1a v2a Aa Ba a w' x' aa lista x ab)(*strict*)
   apply(auto)
  apply(rename_tac xs v1a v2a Aa Ba a w' x' lista x b)(*strict*)
  apply(case_tac x')
   apply(rename_tac xs v1a v2a Aa Ba a w' x' lista x b aa)(*strict*)
   apply(auto)
  apply(rename_tac xs v1a v2a Aa Ba a w' lista x b ba)(*strict*)
  apply(case_tac a)
   apply(rename_tac xs v1a v2a Aa Ba a w' lista x b ba aa)(*strict*)
   apply(auto)
  apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
  apply(subgoal_tac "setA w'\<subseteq>{}")
   apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
   apply(force)
  apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
  apply(rule_tac
      B = "setA (w'@[teB ba])"
      in subset_trans)
   apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
  apply(rule_tac
      t = "w'@[teB ba]"
      and s = "teB bb # teB b # lista"
      in ssubst)
   apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
  apply(rule_tac
      B = "setA lista"
      in subset_trans)
   apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
   apply(simp (no_asm) add: setAConcat concat_asso)
  apply(rename_tac xs v1a v2a Aa Ba w' lista x b ba bb)(*strict*)
  apply(clarsimp)
  done



lemma terminalTailEquals2: "
  setA w1 = {}
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> v1@[teA A]@w2 = v2@u@w1
  \<Longrightarrow> (\<exists>x. w2 = x @ w1)"
  apply(subgoal_tac "\<forall>w1 w2 v1 v2 A u. setA w1 = {} \<and> setA w2 = {} \<and> v1@[teA A]@w2 = v2@u@w1 \<longrightarrow> (\<exists>x. w2 = x @ w1)")
   apply(erule_tac
      x = "w1"
      in allE)
   apply(erule_tac
      x = "w2"
      in allE)
   apply(erule_tac
      x = "v1"
      in allE)
   apply(erule_tac
      x = "v2"
      in allE)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "u"
      in allE)
   apply(force)
  apply(rule allI)
  apply(rename_tac w1a)(*strict*)
  apply(rule_tac
      xs = "w1a"
      in rev_induct)
   apply(rename_tac w1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1a x xs)(*strict*)
  apply(auto)
  apply(rename_tac x xs w2a v1a v2a Aa ua)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac x xs w2a v1a v2a Aa ua)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs Aa)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac x xs w2a v1a v2a Aa ua a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w2a = w' @ [x']")
   apply(rename_tac x xs w2a v1a v2a Aa ua a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xs w2a v1a v2a Aa ua a list)(*strict*)
  apply(thin_tac "w2a = a#list")
  apply(clarsimp)
  apply(rename_tac x xs v1a v2a Aa ua w')(*strict*)
  apply(case_tac w')
   apply(rename_tac x xs v1a v2a Aa ua w')(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs v1a v2a Aa ua)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
   prefer 2
   apply(rename_tac x xs v1a v2a Aa ua w' a list)(*strict*)
   apply(erule_tac
      x = "w'"
      in allE)
   apply(erule impE)
    apply(rename_tac x xs v1a v2a Aa ua w' a list)(*strict*)
    apply(simp only: setAConcat concat_asso)
    apply(clarsimp)
    apply(rename_tac x xs v1a v2a Aa ua a list)(*strict*)
    apply(rule_tac
      x = "v1a"
      in exI)
    apply(rule_tac
      x = "v2a"
      in exI)
    apply(rule_tac
      x = "Aa"
      in exI)
    apply(rule_tac
      x = "ua"
      in exI)
    apply(clarsimp)
   apply(rename_tac x xs v1a v2a Aa ua w' a list)(*strict*)
   apply(force)
  apply(rename_tac x xs v1a v2a Aa ua)(*strict*)
  apply(case_tac x)
   apply(rename_tac x xs v1a v2a Aa ua a)(*strict*)
   apply(auto)
  apply(rename_tac xs v1a v2a Aa ua)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs v1a v2a Aa ua)(*strict*)
   apply(force)
  apply(rename_tac xs v1a v2a Aa ua a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xs = w' @ [x']")
   apply(rename_tac xs v1a v2a Aa ua a list)(*strict*)
   apply(thin_tac "xs = a#list")
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac xs v1a v2a Aa ua a list)(*strict*)
  apply(auto)
   apply(rename_tac Aa w')(*strict*)
   apply(simp only: setAConcat concat_asso,clarsimp) +
  done

lemma liftBSplit: "
  w1@w2 = liftB z
  \<Longrightarrow> \<exists>z1 z2. w1 = liftB z1 \<and> w2 = liftB z2 \<and> z1@z2 = z"
  apply(subgoal_tac "\<forall>w2 z. w1@w2 = liftB z \<longrightarrow> (\<exists>z1 z2. w1 = liftB z1 \<and> w2 = liftB z2 \<and> z1@z2 = z)")
   apply(blast)
  apply(thin_tac "w1 @ w2 = liftB z")
  apply(induct_tac w1)
   apply(auto)
   apply(rename_tac z)(*strict*)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(auto)
  apply(rename_tac a list w2 z)(*strict*)
  apply(case_tac z)
   apply(rename_tac a list w2 z)(*strict*)
   apply(auto)
  apply(rename_tac list w2 aa lista)(*strict*)
  apply(erule_tac
      x = "w2"
      in allE)
  apply(erule_tac
      x = "lista"
      in allE)
  apply(auto)
  apply(rename_tac aa z1 z2)(*strict*)
  apply(rule_tac
      x = "aa#z1"
      in exI)
  apply(auto)
  done

lemma filterBLength: "
  setA w = {}
  \<Longrightarrow> length w = length (filterB w)"
  apply(subgoal_tac "setA w = {} \<longrightarrow> length w = length (filterB w)")
   apply(blast)
  apply(induct w)
   apply(auto)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(auto)
  done

lemma setATake1: "
  length y \<le> k
  \<Longrightarrow> setA (take k y) \<subseteq> setA y"
  apply(auto)
  done

lemma setATake2: "
  length y>k
  \<Longrightarrow> setA (take k y) \<subseteq> setA y"
  apply(subgoal_tac "(\<exists>x. (take k y)@x = y)")
   prefer 2
   apply(rule TakeLength2)
   apply(blast)
  apply(auto)
  apply(rename_tac x xa)(*strict*)
  apply(rule_tac
      t = "y"
      and s = "take k y @ xa"
      in ssubst)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(blast)
  done

lemma setATake: "
  setA (take k y) \<subseteq> setA y"
  apply(case_tac "length y>k")
   apply(rule setATake2)
   apply(blast)
  apply(rule setATake1)
  apply(auto)
  done

lemma liftB_BiElem: "
  set y = setB (liftB y)"
  apply(induct_tac y)
   apply(auto)
  done

lemma take_liftB: "
  take k (liftB w) = liftB (take k w)"
  apply(rule_tac
      t = "liftB"
      and s = "map (\<lambda>x. teB x)"
      in ssubst)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(rule liftBMap)
  apply(rule List.take_map)
  done

lemma liftB_take_prime: "
  setA y = {}
  \<Longrightarrow> take k y = liftB (take k (filterB y))"
  apply(rule_tac
      P = "\<lambda>q. take k q = liftB (take k (filterB y))"
      and t = "y"
      and s = "liftB(filterB y)"
      in ssubst)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rule_tac
      t = "take k (liftB (filterB y))"
      and s = "liftB (take k (filterB y))"
      in ssubst)
   apply(rule take_liftB)
  apply(force)
  done

lemma liftB_inj: "
  liftB w1 = liftB w2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "liftB w1 = liftB w2 \<longrightarrow> w1 = w2")
   apply(blast)
  apply(induct w1 arbitrary: w2)
   apply(rename_tac w2)(*strict*)
   apply(auto)
   apply(rule sym)
   apply(rule liftB_reflects_Nil)
   apply(blast)
  apply(rename_tac a w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac a w1 w2)(*strict*)
   apply(auto)
  done

lemma take_liftB_co: "
  take k z = liftB y
  \<Longrightarrow> setA z = {}
  \<Longrightarrow> take k (filterB z) = y"
  apply(rule liftB_inj)
  apply(rule_tac
      s = "liftB (take k (filterB z))"
      and t = "take k z"
      in ssubst)
   apply(rule_tac
      s = "take k (liftB (filterB z))"
      and t = "liftB (take k (filterB z))"
      in ssubst)
    apply(rule sym)
    apply(rule take_liftB)
   apply(rule_tac
      t = "liftB (filterB z)"
      and s = "z"
      in ssubst)
    apply(rule liftBDeConv2)
    apply(blast)
   apply(blast)
  apply(rule_tac
      t = "liftB (take k (filterB z))"
      and s = "take k (liftB (filterB z))"
      in ssubst)
   apply(rule sym)
   apply(rule take_liftB)
  apply(rule_tac
      t = "liftB (filterB z)"
      and s = "z"
      in ssubst)
   apply(rule liftBDeConv2)
   apply(blast)
  apply(blast)
  done

lemma liftB_commutes_over_concat: "
  liftB (w1@w2) = (liftB w1) @ (liftB w2)"
  apply(induct w1 arbitrary: w2)
   apply(rename_tac w2)(*strict*)
   apply(auto)
  done

lemma filterB_commutes_over_concat: "
  filterB (w1@w2) = (filterB w1) @ (filterB w2)"
  apply(induct w1 arbitrary: w2)
   apply(rename_tac w2)(*strict*)
   apply(auto)
  done

lemma setA_liftB: "
  setA (liftB y) = {}"
  apply(induct y)
   apply(auto)
  done

lemma setA_liftB_subset: "
  setA (liftB x) \<subseteq> A"
  apply(rule_tac
      t = "setA (liftB x)"
      and s = "{}"
      in ssubst)
   apply(rule setA_liftB)
  apply(force)
  done

lemma StepCanDismissTerminalTail: "
  setA grr = {}
  \<Longrightarrow> v @ grr = l @ teA A # r
  \<Longrightarrow> va @ grr = l @ w @ r
  \<Longrightarrow> \<exists>l r. v = l @ teA A # r \<and> va = l @ w @ r"
  apply(subgoal_tac "EX x. r = x @ grr")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x = "l"
      in exI)
   apply(rule_tac
      x = "x"
      in exI)
   apply(clarsimp)
  apply(case_tac "setA r = {}")
   apply(rule_tac
      ?v2.0 = "v"
      and u = "[]"
      and A = "A"
      in terminalTailEquals2)
     apply(blast)
    apply(blast)
   apply(clarsimp)
   apply(blast)
  apply(subgoal_tac "\<exists>w1 w2 A. w1 @ [teA A] @ w2 = r \<and> setA w2 = {}")
   prefer 2
   apply(rule setA_decomp_R)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac w1 w2 Aa)(*strict*)
  apply(subgoal_tac "EX x. w2 = x @ grr")
   apply(rename_tac w1 w2 Aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w2 Aa)(*strict*)
  apply(rule_tac
      ?v2.0 = "va"
      and u = "[]"
      and A = "Aa"
      in terminalTailEquals2)
    apply(rename_tac w1 w2 Aa)(*strict*)
    apply(blast)
   apply(rename_tac w1 w2 Aa)(*strict*)
   apply(blast)
  apply(rename_tac w1 w2 Aa)(*strict*)
  apply(clarsimp)
  apply(blast)
  done

lemma prefix_also_no_nonterms: "
  x @ (liftB y) = liftB z
  \<Longrightarrow> setA x = {}"
  apply(rule order_antisym)
   prefer 2
   apply(blast)
  apply(rule_tac
      B = "setA (x @ liftB y)"
      in subset_trans)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(blast)
  apply(rule_tac
      t = "setA (x @ liftB y)"
      and s = "setA (liftB z)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "setA (liftB z) = {}")
   apply(force)
  apply(rule setA_liftB_empty)
  done

lemma setA_Concat2: "
  setA xs \<subseteq> A
  \<Longrightarrow> xs = w1 @ w2
  \<Longrightarrow> setA w1 \<subseteq> A"
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(auto)
  done

lemma setB_Concat2: "
  setB xs \<subseteq> A
  \<Longrightarrow> xs = w1 @ w2
  \<Longrightarrow> setB w1 \<subseteq> A"
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(simp only: setBConcat concat_asso)
  apply(auto)
  done

lemma filterB_last: "
  setA w = {}
  \<Longrightarrow> length w >0
  \<Longrightarrow> [last (filterB w)] = filterB [last w]"
  apply(subgoal_tac "length w = length (filterB w)")
   prefer 2
   apply(rule filterBLength)
   apply(force)
  apply(induct w)
   apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac "a")
    apply(rename_tac a aa)(*strict*)
    apply(auto)
  apply(rename_tac a w)(*strict*)
  apply(case_tac "a")
   apply(rename_tac a w aa)(*strict*)
   apply(auto)
  done

lemma SameEndWithNonterminalBorder: "
  x @ [teA A] @ z = y @ [teB C]
  \<Longrightarrow> last z = teB C"
  apply(case_tac z)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. z = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(force)
  done

lemma SameEndWithNonterminalBorder_rev: "
  x @ [teA A] @ z = teB C#y
  \<Longrightarrow> hd x = teB C"
  apply(case_tac x)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(auto)
  done

primrec maximalPrefixB :: "('a,'b)DT_two_elements list \<Rightarrow> 'b list" where
  "maximalPrefixB [] = []"
| "maximalPrefixB (a#w) = (case a of teA B \<Rightarrow> [] | teB b \<Rightarrow> b#maximalPrefixB w)"

lemma maximalPrefixB_select: "
  maximalPrefixB w = v
  \<Longrightarrow> liftB v = w \<or> (\<exists>A x. w = (liftB v)@[teA A]@x)"
  apply(case_tac "liftB v = w")
   apply(force)
  apply(clarsimp)
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_liftB: "
  maximalPrefixB (liftB w) = w"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(force)
  done

definition maxTermPrefix :: "('a,'b) DT_two_elements list \<Rightarrow> 'b list" where
  "maxTermPrefix c = (THE y. (\<exists>w. liftB y @ w = c) \<and> (\<forall>w. liftB y @ w = c \<longrightarrow> (case w of [] \<Rightarrow> True | a#y \<Rightarrow> (case a of teB X \<Rightarrow> False | teA A \<Rightarrow> True))))"

definition maxTermPrefixS :: "('a,'b) DT_two_elements list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "maxTermPrefixS c y = ((\<exists>w. liftB y @ w = c) \<and> (\<forall>w. liftB y @ w = c \<longrightarrow> (case w of [] \<Rightarrow> True | a#y \<Rightarrow> (case a of teB X \<Rightarrow> False | teA A \<Rightarrow> True))))"

lemma maximal_terminal_prefix_THE_prime: "
  setA x = {}
  \<Longrightarrow> res = filterB x
  \<Longrightarrow> (THE y. (\<exists>w. liftB y @ w = x) \<and> (\<forall>w. liftB y @ w = x \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))) = res"
  apply(clarsimp)
  apply(rule the_equality)
   apply(rule_tac
      t = "liftB (filterB x)"
      and s = "x"
      in ssubst)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w)(*strict*)
  apply(case_tac w)
   apply(rename_tac y w)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(rule sym)
   apply(rule liftBDeConv1)
  apply(rename_tac y w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac y a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac y a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y list aa)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(force)
  apply(rename_tac y a list b)(*strict*)
  apply(clarsimp)
  done

lemma maxTermPrefix_on_term_string: "
  maxTermPrefixS w v
  \<Longrightarrow> setA w = {}
  \<Longrightarrow> v = filterB w"
  apply(simp add: maxTermPrefixS_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(case_tac w)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule liftBDeConv1)
  apply(rename_tac w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(force)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  done

lemma setA_vs_mset_empty: "
  (setA w = {}) = (\<forall>A. mset w (teA A) = 0)"
  apply(induct w)
   apply(clarsimp)
   apply(rename_tac A)(*strict*)
   apply(rule mset0)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(rule_tac
      x = "aa"
      in exI)
   apply(rule_tac
      t = "mset (teA aa # w) (teA aa)"
      and s = "Suc (mset w (teA aa))"
      in ssubst)
    apply(rename_tac w aa)(*strict*)
    apply(rule mset_Cons_eq)
   apply(rename_tac w aa)(*strict*)
   apply(force)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac w b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w b A)(*strict*)
   apply(rule_tac
      t = "mset (teB b # w) (teA A)"
      and s = "mset w (teA A)"
      in ssubst)
    apply(rename_tac w b A)(*strict*)
    apply(rule mset_Cons_neq)
    apply(force)
   apply(rename_tac w b A)(*strict*)
   apply(force)
  apply(rename_tac w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b A)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(rule_tac
      s = "mset (teB b # w) (teA A)"
      and t = "mset w (teA A)"
      in subst)
   apply(rename_tac w b A)(*strict*)
   apply(rule mset_Cons_neq)
   apply(force)
  apply(rename_tac w b A)(*strict*)
  apply(force)
  done

lemma liftB_terminal_tail_equals: "
  v @ [teB X] = liftB (w @ [Y])
  \<Longrightarrow> Y = X"
  apply(subgoal_tac "liftB (w @ [Y]) = liftB w @ (liftB [Y])")
   apply(clarsimp)
   apply (simp add: liftB_commute_one_elem_app)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma liftB_terminal_butlast_equals: "
  v @ [teB X] = liftB (w @ [Y])
  \<Longrightarrow> v = liftB w"
  apply(subgoal_tac "Y = X")
   prefer 2
   apply(rule liftB_terminal_tail_equals)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "liftB (w @ [Y]) = liftB w @ (liftB [Y])")
   apply(clarsimp)
   apply (simp add: liftB_commute_one_elem_app)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma set_setB: "
  teB A  \<in> set w
  \<Longrightarrow> A  \<in> setB w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma rev_liftB_elem: "
  teB X \<notin> set (liftB w)
  \<Longrightarrow> X \<notin> set w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma liftB_in_two_elements_construct_domain_to_subset: "
  set (liftB cb) \<subseteq> two_elements_construct_domain A B
  \<Longrightarrow> set cb \<subseteq> B"
  apply(induct cb)
   apply(clarsimp)
  apply(rename_tac a cb)(*strict*)
  apply(clarsimp)
  apply(simp add: two_elements_construct_domain_def)
  apply(erule disjE)
   apply(rename_tac a cb)(*strict*)
   apply(force)
  apply(rename_tac a cb)(*strict*)
  apply(force)
  done

lemma liftB_distributes_over_drop: "
  liftB (drop n xa) = drop n (liftB xa)"
  apply(induct xa arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a xa n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a xa n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a xa n nat)(*strict*)
  apply(clarsimp)
  done

lemma setB_empty_then_liftA_vs_filterA: "
  setB r = {}
  \<Longrightarrow> r = liftA (filterA r)"
  apply(induct r)
   apply(clarsimp)
  apply(rename_tac a r)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a r aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a r b)(*strict*)
  apply(clarsimp)
  done

lemma liftA_vs_filterA: "
  filterA (liftA r) = r"
  apply(induct r)
   apply(clarsimp)
  apply(rename_tac a r)(*strict*)
  apply(clarsimp)
  done

lemma filterA_append_tail: "
  filterA (liftA (w @ [x])) = v @ [y]
  \<Longrightarrow> w = v \<and> x = y"
  apply (metis liftA_vs_filterA append1_eq_conv rotate_simps)
  done

lemma filterA_preserves_length: "
  setB r = {}
  \<Longrightarrow> length (filterA r) = length r"
  apply(induct r)
   apply(clarsimp)
  apply(rename_tac a r)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a r aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a r b)(*strict*)
  apply(clarsimp)
  done

lemma THE_split1: "
  (THE v. \<exists>w. [teA A] = liftB w @ liftA v) = [A]"
  apply(rule_tac
      a="[A]"
      in HOL.theI2)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(case_tac w)
     apply(rename_tac w)(*strict*)
     apply(clarsimp)
    apply(rename_tac w a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list w)(*strict*)
   apply(case_tac w)
    apply(rename_tac a list w)(*strict*)
    apply(clarsimp)
    apply(rename_tac list)(*strict*)
    apply(case_tac list)
     apply(rename_tac list)(*strict*)
     apply(clarsimp)
    apply(rename_tac list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list w aa lista)(*strict*)
   apply(case_tac w)
    apply(rename_tac a list w aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list w aa lista ab listb)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w)(*strict*)
  apply(case_tac w)
   apply(rename_tac x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac x w a list)(*strict*)
  apply(clarsimp)
  done

lemma THE_split2: "
  (THE w. \<exists>v. [teA A] = liftB w @ liftA v) = []"
  apply(rule_tac
      a="[]"
      in HOL.theI2)
    apply(rule_tac
      x="[A]"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a list)(*strict*)
  apply(clarsimp)
  done

lemma setB_liftA: "
  setB (liftA w) = {}"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma split_decide1: "
  setA l = {}
  \<Longrightarrow> l @ teA A # r = liftB w @ liftA v
  \<Longrightarrow> l = liftB w"
  apply(induct l arbitrary: A r w v)
   apply(rename_tac A r w v)(*strict*)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac A r w v)(*strict*)
    apply(clarsimp)
   apply(rename_tac A r w v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l A r w v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a l A r w v aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l A r w v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac l A r w v b)(*strict*)
  apply(case_tac w)
   apply(rename_tac l A r w v b)(*strict*)
   apply(clarsimp)
   apply(rename_tac l A r v b)(*strict*)
   apply (metis setB_liftA setB_set_not emptyE list.sel hd_in_set list.simps(3))
  apply(rename_tac l A r w v b a list)(*strict*)
  apply(clarsimp)
  done

lemma split_decide2: "
  setA l = {}
  \<Longrightarrow> l @ teA A # r = liftB w @ liftA v
  \<Longrightarrow> teA A # r = liftA v"
  apply(induct l arbitrary: A r w v)
   apply(rename_tac A r w v)(*strict*)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac A r w v)(*strict*)
    apply(clarsimp)
   apply(rename_tac A r w v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l A r w v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a l A r w v aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l A r w v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac l A r w v b)(*strict*)
  apply(case_tac w)
   apply(rename_tac l A r w v b)(*strict*)
   apply(clarsimp)
   apply(rename_tac l A r v b)(*strict*)
   apply (metis setB_liftA setB_set_not emptyE list.sel hd_in_set list.simps(3))
  apply(rename_tac l A r w v b a list)(*strict*)
  apply(clarsimp)
  done

lemma liftA_append_setB: "
  w @ r @ y = liftA v
  \<Longrightarrow> setB r = {}"
  apply (metis setBConcat setB_liftA sup_eq_bot_iff)
  done

lemma liftA_append_tail: "
  liftA (w' @ [x']) = liftA w' @ [teA x']"
  apply(induct w')
   apply(clarsimp)
  apply(rename_tac a w')(*strict*)
  apply(clarsimp)
  done

lemma filterA_append_tail2: "
  filterA xs @ [x'] = filterA (xs @ [teA x'])"
  apply(induct xs)
   apply(clarsimp)
  apply(rename_tac a xs)(*strict*)
  apply(clarsimp)
  done

lemma liftB_liftA_split: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> l @ r = liftB w @ liftA x
  \<Longrightarrow> x = filterA r"
  apply(induct r arbitrary: l w x rule: rev_induct)
   apply(rename_tac l w x)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(case_tac x)
    apply(rename_tac w x)(*strict*)
    apply(clarsimp)
   apply(rename_tac w x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply (metis liftA.simps(2) elemInsetA empty_iff)
  apply(rename_tac x xs l w xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac x xs l w xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs l w)(*strict*)
   apply(case_tac x)
    apply(rename_tac x xs l w a)(*strict*)
    apply(clarsimp)
    apply(rename_tac xs l w a)(*strict*)
    apply (metis ConsApp ListMem_iff setA_liftB setA_set_not concat_asso emptyE last_in_set last_snoc listeq_by_mutual_append not_Cons_self)
   apply(rename_tac x xs l w b)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs l w b)(*strict*)
   apply (metis elemInsetB emptyE)
  apply(rename_tac x xs l w xa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa=w'@[x']")
   apply(rename_tac x xs l w xa a list)(*strict*)
   prefer 2
   apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xs l w xa a list)(*strict*)
  apply(thin_tac "xa=a # list")
  apply(clarsimp)
  apply(rename_tac x xs l w w' x')(*strict*)
  apply(case_tac x)
   apply(rename_tac x xs l w w' x' a)(*strict*)
   prefer 2
   apply(rename_tac x xs l w w' x' b)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs l w w' x' b)(*strict*)
   apply (metis elemInsetB emptyE)
  apply(rename_tac x xs l w w' x' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs l w w' x' a)(*strict*)
  apply(erule_tac
      x="l"
      in meta_allE)
  apply(erule_tac
      x="w"
      in meta_allE)
  apply(erule_tac
      x="w'"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "liftA (w' @ [x'])=liftA w' @ [teA x']")
   apply(rename_tac xs l w w' x' a)(*strict*)
   prefer 2
   apply(rule liftA_append_tail)
  apply(rename_tac xs l w w' x' a)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xs l w w' x' a)(*strict*)
   apply (simp add: setBConcat)
  apply(rename_tac xs l w w' x' a)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xs l w w' x' a)(*strict*)
   apply(subgoal_tac "a=x'")
    apply(rename_tac xs l w w' x' a)(*strict*)
    apply(clarsimp)
    apply(rename_tac xs l w w' x')(*strict*)
    apply(rule_tac
      v="[teA x']"
      in append_injr)
    apply(clarsimp)
    apply(force)
   apply(rename_tac xs l w w' x' a)(*strict*)
   apply(force)
  apply(rename_tac xs l w w' x' a)(*strict*)
  apply(subgoal_tac "a=x'")
   apply(rename_tac xs l w w' x' a)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac xs l w w' x' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs l w x')(*strict*)
  apply(rule filterA_append_tail2)
  done

lemma THE_split5: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> (THE v. \<exists>w. l @ r = liftB w @ liftA v) = filterA r"
  apply(rule_tac
      a="filterA r"
      in HOL.theI2)
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (metis setB_empty_then_liftA_vs_filterA liftBDeConv2)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(rule liftB_liftA_split)
     apply(rename_tac x w)(*strict*)
     apply(force)
    apply(rename_tac x w)(*strict*)
    apply(force)
   apply(rename_tac x w)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w)(*strict*)
  apply(rule liftB_liftA_split)
    apply(rename_tac x w)(*strict*)
    apply(force)
   apply(rename_tac x w)(*strict*)
   apply(force)
  apply(rename_tac x w)(*strict*)
  apply(force)
  done

lemma THE_split6: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> (THE w. \<exists>v. l @ r = liftB w @ liftA v) = filterB l"
  apply(rule_tac
      a="filterB l"
      in HOL.theI2)
    apply(rule_tac
      x="filterA r"
      in exI)
    apply (metis setB_empty_then_liftA_vs_filterA liftBDeConv2)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply (metis setB_empty_then_liftA_vs_filterA liftBDeConv1 liftB_liftA_split append_injective1)
  apply(rename_tac x)(*strict*)
  apply (metis setB_empty_then_liftA_vs_filterA liftBDeConv1 liftB_liftA_split append_injective1)
  done

lemma filterA_append_tail_eq: "
  setB (w @ [y]) = {}
  \<Longrightarrow> filterA (w @ [y]) = x @ [z]
  \<Longrightarrow> filterA w = x"
  apply(induct w arbitrary: x y z)
   apply(rename_tac x y z)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
    apply(rename_tac x y z a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x y z b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w x y z)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w x y z aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x y z aa)(*strict*)
   apply(case_tac x)
    apply(rename_tac w x y z aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w y)(*strict*)
    apply(case_tac y)
     apply(rename_tac w y a)(*strict*)
     apply(clarsimp)
     apply(rename_tac w a)(*strict*)
     apply (metis filterA_append_tail2 rotate_simps snoc_eq_iff_butlast)
    apply(rename_tac w y b)(*strict*)
    apply (metis liftA.simps(1) setB_empty_then_liftA_vs_filterA list.simps(2) rotate1_is_Nil_conv rotate_simps)
   apply(rename_tac w x y z aa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w x y z b)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w x y z b aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w x y z b ba)(*strict*)
  apply(clarsimp)
  done

lemma hlp_lem: "
  A # wx @ [x'] = liftA (w' @ [X])
  \<Longrightarrow> liftA (w' @ [X]) = liftA w' @ [teA X]
  \<Longrightarrow> liftA w' = A # wx"
  apply(rule sym)
  apply(rule_tac
      v="[x']"
      in append_injr)
  apply(clarsimp)
  apply (metis NotemptyString liftA.simps(2) liftA_append_tail last.simps last_snoc rotate_simps)
  done

lemma liftA_preserves_length: "
  length (liftA w) = length w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma SPLIT_2_0: "
  (THE v. \<exists>wa. liftB wx @ teA A # liftA wv = liftB wa @ liftA v) = A # wv"
  apply(rule_tac
      a="A # wv"
      in HOL.theI2)
    apply(rule_tac
      x="wx"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac wa)(*strict*)
    apply (metis setA_liftB liftA.simps(1) liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_Nil2 list.simps(2))
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list wa)(*strict*)
   apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split list.sel list.sel(2))
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac wa)(*strict*)
   apply (metis setA_liftB liftA.simps(1) liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_Nil2 list.simps(2))
  apply(rename_tac x a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list wa)(*strict*)
  apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split list.sel list.sel(2))
  done

lemma SPLIT_1_prime: "
  (THE v. \<exists>x. liftB x @ liftA v = [teA A]) = [A]"
  apply(rule_tac
      a="[A]"
      in HOL.theI2)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac xa a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac a list xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac list)(*strict*)
    apply(case_tac list)
     apply(rename_tac list)(*strict*)
     apply(clarsimp)
    apply(rename_tac list a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list xa aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa a list)(*strict*)
  apply(clarsimp)
  done

lemma split_decide1_x: "
  liftB waa @ teA A # teA (cons_l3 q1 b q2) # liftA list = l @ teA A # r
  \<Longrightarrow> liftB waa @ teA (cons_l3 q1 b q2) # liftA list = l @ r
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> liftB waa = l"
  apply (metis liftA.simps(2) split_decide1)
  done

lemma setA_decompose: "
  setA (a @ b @ c) = {}
  \<Longrightarrow> setA b = {}"
  apply (metis setAConcat setA_Concat2 Un_empty_left empty_subsetI set_eq_subset)
  done

lemma setA_has_position: "
  x  \<in> setA w
  \<Longrightarrow> \<exists>w1 w2. w = w1 @ teA x # w2"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w1 w2)(*strict*)
   apply(rule_tac
      x="a#w1"
      in exI)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   prefer 2
   apply(rename_tac a w b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma setA_decomp_R2: "
  setA w \<noteq> {}
  \<Longrightarrow> \<exists>w1 w2 A. w1 @ [teA A] @ w2 = w \<and> setA w1={}"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b w1 w2 A)(*strict*)
  apply(rule_tac
      x="teB b#w1"
      in exI)
  apply(clarsimp)
  done

lemma earliest_occurence_in_list: "
  x  \<in> setA w
  \<Longrightarrow> \<exists>w1 w2. w = w1 @ [teA x] @ w2 \<and> x \<notin> setA w1"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(case_tac "x=aa")
    apply(rename_tac w aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa w1 w2)(*strict*)
   apply(rule_tac
      x="teA aa#w1"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b w1 w2)(*strict*)
  apply(rule_tac
      x="teB b#w1"
      in exI)
  apply(clarsimp)
  done

lemma liftB_decompose: "
  liftB w = x@y
  \<Longrightarrow> \<exists>x' y'. liftB x'=x \<and> liftB y'=y \<and> w=x'@y'"
  apply(rule_tac
      x="take (length x) w"
      in exI)
  apply(rule_tac
      x="drop (length x) w"
      in exI)
  apply (metis liftB_distributes_over_drop append_take_drop_id dropPrecise takePrecise take_liftB)
  done

lemma setA_liftB_substring: "
  liftB a = b @ x @ c
  \<Longrightarrow> setA x = {}"
  apply (metis setA_liftB setA_decompose)
  done

lemma SPLIT_tail: "
  (THE r. \<exists>w B. liftB v1 @ teA B1 # liftA r1 = liftB w @ teA B # liftA r) = r1"
  apply(rule_tac
      a="r1"
      in HOL.theI2)
    apply(clarsimp)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w B)(*strict*)
   apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split list.inject)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w B)(*strict*)
  apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split list.inject)
  done

lemma drop_liftB: "
  drop n (liftB w) = liftB (drop n w)"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n nat)(*strict*)
  apply(clarsimp)
  done

lemma liftA_filterA: "
  setB w={}
  \<Longrightarrow> liftA (filterA w) = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma set_subset_to_setA_subset: "
  set w \<subseteq> set v
  \<Longrightarrow> setA w \<subseteq> setA v"
  apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check two_elements_construct_domain_setA equalityE subset_trans)
  done

lemma teB_nth_liftB: "
  i<length w
  \<Longrightarrow> teB (w ! i) = liftB w ! i"
  apply(induct w arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i nat)(*strict*)
  apply(clarsimp)
  done

lemma distrib_nth_liftB: "
  i < length (liftB w)
  \<Longrightarrow> [liftB w ! i] = liftB [w ! i]"
  apply(induct w arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i nat)(*strict*)
  apply(clarsimp)
  done

lemma setA_liftB_nth: "
  i<length l'
  \<Longrightarrow> setA ([liftB l' ! i]) = {}"
  apply(subgoal_tac "setA ([liftB l' ! i]) \<subseteq> setA (liftB l') ")
   apply(subgoal_tac "setA (liftB l') = {}")
    apply(force)
   apply(rule setA_liftB)
  apply(rule set_subset_to_setA_subset)
  apply (metis liftB_reflects_length nth_mem set_subset_in2)
  done

lemma THE_liftB_liftA: "
  (THE va. \<exists>w. liftB x @ liftA y = liftB w@liftA va)=y"
  apply(rule_tac
      a="y"
      in HOL.theI2)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa w)(*strict*)
   apply (metis setA_liftB liftA_vs_filterA setB_liftA liftB_liftA_split)
  apply(rename_tac xa)(*strict*)
  apply (metis setA_liftB liftA_vs_filterA setB_liftA liftB_liftA_split)
  done

lemma teA_not_in_liftB: "
  teA A \<notin> set (liftB w)"
  apply (metis setA_liftB setA_set_not empty_iff)
  done

lemma liftB_unfold: "
  liftB w = a@b
  \<Longrightarrow> \<exists>a' b'. w=a'@b' \<and> liftB a'=a \<and> liftB b'=b"
  apply(rule_tac
      x="take (length a) w"
      in exI)
  apply(rule_tac
      x="drop (length a) w"
      in exI)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply (metis takePrecise take_liftB)
  apply (metis liftB_distributes_over_drop dropPrecise)
  done

lemma filterA_liftB: "
  filterA (liftB w) = []"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma filterA_nonempty_setA_nonempty: "
  length (filterA w) > 0
  \<Longrightarrow> setA w \<noteq> {}"
  apply (metis filterA_liftB liftBDeConv2 less_not_refl list.size(3))
  done

lemma equal_simp_triv: "
  a@[teA A]@b=x@[teA B]@y
  \<Longrightarrow> setA b={}
  \<Longrightarrow> setA y={}
  \<Longrightarrow> a=x \<and> A=B \<and> b=y"
  apply(subgoal_tac "b=y")
   prefer 2
   apply(rule terminalTailEquals1)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma filterB_liftA: "
  filterB (liftA w) = []"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma liftB_eq_by_liftA_append: "
  (liftB w1)@(liftA v1)=(liftB w2)@(liftA v2)
  \<Longrightarrow> liftB w1 = liftB w2"
  apply (metis liftBDeConv1 filterB_liftA filterB_commutes_over_concat append_Nil2)
  done

lemma filterA_setA: "
  filterA l = []
  \<Longrightarrow> setA l = {}"
  apply(induct l)
   apply(clarsimp)
  apply(rename_tac a l)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a l aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l b)(*strict*)
  apply(clarsimp)
  done

lemma liftB_suffix_setA: "
  liftB a=liftB b @ v
  \<Longrightarrow> setA v={}"
  apply (metis setAConcat setA_liftB Un_empty)
  done

lemma liftB_suffix_setA2: "
  liftB a=liftB b @ v
  \<Longrightarrow> \<exists>l'. a=b@l' \<and> liftB l'=v"
  apply(subgoal_tac "\<exists>l'. liftB l' = v")
   prefer 2
   apply(rule_tac
      x="filterB v"
      in exI)
   apply (rule liftBDeConv2)
   apply(rule liftB_suffix_setA)
   apply(force)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(rule_tac
      x="l'"
      in exI)
  apply(clarsimp)
  apply(rule liftB_inj)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma setB_liftB: "
  setB (liftB w) = set w"
  apply(rule sym)
  apply(rule set_setB_liftB)
  done

lemma setA_liftA: "
  setA(liftA w)=set w"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma filterA_distrib_append: "
  filterA (w1@w2) = (filterA w1)@(filterA w2)"
  apply(induct w1 arbitrary: w2)
   apply(rename_tac w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(clarsimp)
  done

lemmas simpX = filterA_liftB setA_liftB setAConcat filterA_distrib_append filterB_commutes_over_concat liftBDeConv1 liftB_commutes_over_concat setBConcat

lemma filterA_liftA: "
  filterA (liftA w) = w"
  apply(rule liftA_vs_filterA)
  done

lemma liftA_commutes_over_concat: "
  liftA (w1@w2) = (liftA w1) @ (liftA w2)"
  apply(induct w1 arbitrary: w2)
   apply(rename_tac w2)(*strict*)
   apply(auto)
  done

lemmas simpY =
  setB_liftB
  setB_liftA
  setA_liftA
  simpX
  liftA_commutes_over_concat
  filterA_liftA

lemma unequal_by_setA_X: "
  w=v
  \<Longrightarrow> setA w={}
  \<Longrightarrow> A  \<in> setA v
  \<Longrightarrow> Q"
  apply(force)
  done

lemma setB_decompose: "
  setB w={}
  \<Longrightarrow> w=(a@b@c)
  \<Longrightarrow> setB b={}"
  apply(simp add: simpY)
  done

lemma leading_liftB_prefix_eq: "
  liftB w1 @ teA A1 # v1 = liftB w2 @ teA A2 # v2
  \<Longrightarrow> w1=w2"
  apply(induct "length w1" arbitrary: w1 w2)
   apply(rename_tac w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2)(*strict*)
   apply(case_tac w2)
    apply(rename_tac w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac w2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac x w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w2 a list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w2 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w2 a list aa lista)(*strict*)
  apply(clarsimp)
  done

lemma setA_liftA_set_drop_subset: "
  setA (liftA (drop n w))
  \<subseteq> setA (liftA w)"
  apply(rule_tac
      t="setA (liftA (drop n w))"
      and s="set(drop n w)"
      in ssubst)
   apply(rule setA_liftA)
  apply(rule_tac
      t="setA (liftA w)"
      and s="set w"
      in ssubst)
   apply(rule setA_liftA)
  apply (metis set_drop_subset)
  done

lemma setB_set_elem: "
  x  \<in> setB w
  \<Longrightarrow> \<exists>y \<in> set w. teB x=y"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma setA_foldl_take: "
  setA (foldl (@) [] (take k fw)) \<subseteq> setA (foldl (@) [] fw)"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k x)(*strict*)
  apply(rule_tac
      t="fw"
      and s="take (Suc k) fw @ (drop (Suc k) fw)"
      in ssubst)
   apply(rename_tac k x)(*strict*)
   apply(force)
  apply(rename_tac k x)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take (Suc k) fw @ drop (Suc k) fw)"
      and s="foldl (@) [] (take (Suc k) fw) @ (foldl (@) [] (drop (Suc k) fw))"
      in ssubst)
   apply(rename_tac k x)(*strict*)
   apply(simp add: foldl_append_distrib setAConcat)
  apply(rename_tac k x)(*strict*)
  apply(simp add: setAConcat)
  done

lemma setB_foldl_take: "
  setB (foldl (@) [] (take k fw)) \<subseteq> setB (foldl (@) [] fw)"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k x)(*strict*)
  apply(rule_tac
      t="fw"
      and s="take (Suc k) fw @ (drop (Suc k) fw)"
      in ssubst)
   apply(rename_tac k x)(*strict*)
   apply(force)
  apply(rename_tac k x)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take (Suc k) fw @ drop (Suc k) fw)"
      and s="foldl (@) [] (take (Suc k) fw) @ (foldl (@) [] (drop (Suc k) fw))"
      in ssubst)
   apply(rename_tac k x)(*strict*)
   apply(simp add: foldl_append_distrib setBConcat)
  apply(rename_tac k x)(*strict*)
  apply(simp add: setBConcat)
  done

lemma setA_empty_from_greater_set: "
  set w \<subseteq> set v
  \<Longrightarrow> setA v={}
  \<Longrightarrow> setA w={}"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w v aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w v aa)(*strict*)
   apply (metis ex_in_conv set_setA)
  apply(rename_tac a w v b)(*strict*)
  apply(clarsimp)
  done

lemma setA_empty_foldl: "
  setA (foldl (@) [] fw) = {}
  \<Longrightarrow> \<forall>i<length fw. setA (fw ! i) = {}"
  apply(induct fw)
   apply(clarsimp)
  apply(rename_tac a fw)(*strict*)
  apply(clarsimp)
  apply(rename_tac a fw i)(*strict*)
  apply(case_tac i)
   apply(rename_tac a fw i)(*strict*)
   apply(clarsimp)
   apply(rename_tac a fw)(*strict*)
   apply (metis setATakeIndexSubset2 empty_subsetI equalityI foldl_first takePrecise)
  apply(rename_tac a fw i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a fw nat)(*strict*)
  apply (metis setA_empty_from_greater_set foldl_first set_append2)
  done

lemma setA_empty_foldl2: "
  \<forall>i<length fw. setA (fw ! i) = {}
  \<Longrightarrow> setA (foldl (@) [] fw) = {}"
  apply(induct fw)
   apply(clarsimp)
  apply(rename_tac a fw)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) a fw"
      and s="a@foldl (@) [] fw"
      in ssubst)
   apply(rename_tac a fw)(*strict*)
   apply (metis foldl_first)
  apply(rename_tac a fw)(*strict*)
  apply(simp add: setAConcat)
  apply(rule conjI)
   apply(rename_tac a fw)(*strict*)
   apply(erule_tac
      x="0"
      in allE)
   apply(force)
  apply(rename_tac a fw)(*strict*)
  apply(force)
  done

lemma teA_liftA_nth: "
  n<length w
  \<Longrightarrow> teA (w ! n) = liftA w ! n"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n nat)(*strict*)
  apply(clarsimp)
  done

lemma filterB_foldl: "
  filterB(foldl (@) [] w) = foldl (@) [] (map filterB w)"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(simp add: simpX)
  done

lemma setA_filterA2: "
  filterA w \<noteq> []
  \<Longrightarrow> setA w \<noteq> {}"
  apply(case_tac "setA w = {}")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>l'. liftB l' = w")
   prefer 2
   apply(rule_tac
      x="filterB w"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(simp add: simpX)
  done

lemma filterA_preserves_setA: "
  set (filterA l) = setA l"
  apply(induct l)
   apply(clarsimp)
  apply(rename_tac a l)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a l aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l b)(*strict*)
  apply(clarsimp)
  done

lemma setA_filterA: "
  setA l = {}
  \<Longrightarrow> filterA l=[]"
  apply (metis setA_empty_liftB_construct filterA_liftB)
  done

lemma teB_in_setB_nth: "
  i < length w
  \<Longrightarrow> w ! i = teB b
  \<Longrightarrow> b  \<in> setB w"
  apply (metis nth_mem set_setB)
  done

lemma distrib_liftB_foldl: "
  liftB (foldl (@) [] \<alpha>) = foldl (@) [] (map liftB \<alpha>)"
  apply(induct \<alpha> rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma set_subset_to_setB_subset: "
  set w \<subseteq> set v
  \<Longrightarrow> setB w \<subseteq> setB v"
  apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check two_elements_construct_domain_setB equalityE subset_trans)
  done

lemma hlp2: "
  i < length (liftB w)
  \<Longrightarrow> liftB w ! i = teA A
  \<Longrightarrow> Q"
  apply(induct w arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w i nat)(*strict*)
  apply(clarsimp)
  done

lemma setA_append: "
  setA (a@b@c) ={}
  \<Longrightarrow> setA b ={}"
  apply(simp add: setAConcat)
  done

lemma last_nonterm_exists: "
  setA w' \<noteq> {}
  \<Longrightarrow> \<exists>v1 A v2. w' = v1 @ teA A # liftB v2"
  apply(induct w' rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(case_tac x)
   apply(rename_tac x xs a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs a)(*strict*)
   apply(rule_tac
      x="xs"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rename_tac x xs b)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs b)(*strict*)
  apply(simp add: setAConcat)
  apply(clarsimp)
  apply(rename_tac b v1 A v2)(*strict*)
  apply(rule_tac
      x="v1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="v2@[b]"
      in exI)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma filterA_empty_setA: "
  filterA l = []
  \<Longrightarrow> setA l = {}"
  apply(induct l)
   apply(force)
  apply(rename_tac a l)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a l aa)(*strict*)
   apply(force)
  apply(rename_tac a l b)(*strict*)
  apply(clarsimp)
  done

lemma setA_nonempty_has_last_nonterm: "
  setA w \<noteq> {}
  \<Longrightarrow> \<exists>w1 A w2. w=w1@teA A#liftB w2"
  apply(rule last_nonterm_exists)
  apply(force)
  done

lemma setA_nonempty_has_first_nonterm: "
  setA w \<noteq> {}
  \<Longrightarrow> \<exists>w1 A w2. w=liftB w1@teA A#w2"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b w1 A w2)(*strict*)
  apply(rule_tac
      x="b#w1"
      in exI)
  apply(clarsimp)
  done

lemma setA_foldl: "
  (\<And>x. x \<in> set w\<Longrightarrow>setA x={})
  \<Longrightarrow> setA (foldl (@) [] w) = {}"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(simp add: setAConcat)
  done

lemma filterA_setA_renamed: "
  set (filterA l) \<subseteq> setA l"
  apply(induct l)
   apply(clarsimp)
  apply(rename_tac a l)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac a l)(*strict*)
   apply(case_tac a)
    apply(rename_tac a l aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a l b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a l)(*strict*)
  apply(force)
  done

lemma maximalPrefixB_drop_liftA: "
  maximalPrefixB (liftA w) = []"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_prefix2: "
  maximalPrefixB (liftB x @ [teA A] @ w) = x"
  apply(induct x)
   apply(clarsimp)
  apply(rename_tac a x)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_prefix2_prime: "
  maximalPrefixB (liftB x @ teA A # w) = x"
  apply(induct x)
   apply(clarsimp)
  apply(rename_tac a x)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_front: "
  maximalPrefixB (teA A # w) = []"
  apply(simp add: maximalPrefixB_def)
  done

lemma maximalPrefixB_liftA: "
  maximalPrefixB (liftA w) = []"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma setA_elem_at_nth: "
  x  \<in> setA w
  \<Longrightarrow> \<exists>k<length w. w!k = teA x"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma setA_Cons: "
  setA (a#y) = setA ([a]) \<union> setA y"
  apply(force)
  done

lemma setB_Cons: "
  setB (a#y) = setB ([a]) \<union> setB y"
  apply(force)
  done

lemma setA_subset: "
  setA v={}
  \<Longrightarrow> set w \<subseteq> set v
  \<Longrightarrow> setA w={}"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w v aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w v aa)(*strict*)
   apply (metis ex_in_conv set_setA)
  apply(rename_tac a w v b)(*strict*)
  apply(clarsimp)
  done

lemma LRP_determ_hlp1: "
  DO \<notin> A
  \<Longrightarrow> w @ take n [X] = w1 @ [DO] @ w2 @ [Y]
  \<Longrightarrow> set w \<subseteq> set (liftB v)
  \<Longrightarrow> set (liftB v) \<subseteq> A
  \<Longrightarrow> P"
  apply(case_tac n)
   apply(clarsimp)
   apply (metis subsetD)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply (metis subsetD)
  done

lemma setA_drop: "
  setA w={}
  \<Longrightarrow> setA (drop k w)={}"
  apply (metis setADropIndexSubset2 subset_empty)
  done

lemma filterB_inj: "
  setA w={}
  \<Longrightarrow> setA v={}
  \<Longrightarrow> filterB w=filterB v
  \<Longrightarrow> w=v"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(case_tac v)
    apply(rename_tac v)(*strict*)
    apply(force)
   apply(rename_tac v a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w v aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w v b)(*strict*)
  apply(case_tac v)
   apply(rename_tac w v b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w v b a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w b a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac w b a list ba)(*strict*)
  apply(clarify)
  apply(erule_tac
      x="list"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac w b a list ba)(*strict*)
   apply(force)
  apply(rename_tac w b a list ba)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac w b a list ba)(*strict*)
   apply(force)
  apply(rename_tac w b a list ba)(*strict*)
  apply(clarsimp)
  done



end
