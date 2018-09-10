section {*sets\_in\_example\_are\_disjoint*}
theory sets_in_example_are_disjoint
  imports Main

begin

lemma length_compare: "
  length w1 = length w2 \<or> length w1 < length w2 \<or> length w2 < length w1"
  apply(force)
  done

lemma eq_prefix: "
  w1 @ w2 = w3 @ w4
  \<Longrightarrow> length w1 = length w3
  \<Longrightarrow> w1 = w3"
  apply(clarsimp)
  done

lemma sync_at_c: "
  w1 @ [c] @ w2 = w3 @ [c] @ w4
  \<Longrightarrow> c \<notin> set w2
  \<Longrightarrow> c \<notin> set w4
  \<Longrightarrow> w1 = w3"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?w1.0="w1" and ?w2.0="w3" in length_compare)
  apply(erule disjE)
   apply(subgoal_tac "w1 = w3")
    apply(clarsimp)
   apply(clarsimp)
  apply(rule_tac eq_prefix)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(subgoal_tac "drop (length w1) (w1 @ c # w2) = drop (length w1) (w3 @ c # w4)") 
    apply(thin_tac "w1 @ c # w2 = w3 @ c # w4")
    apply(clarsimp)
    apply(case_tac "drop (length w1) w3")
     apply(clarsimp)
    apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "drop (length w3) (w1 @ c # w2) = drop (length w3) (w3 @ c # w4)") 
   apply(thin_tac "w1 @ c # w2 = w3 @ c # w4")
   apply(clarsimp)
   apply(case_tac "drop (length w3) w1")
    apply(clarsimp)
   apply(clarsimp)
  apply(force)
  done

definition 
  set1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set1 a b c d e u \<equiv> {[c]}"

definition 
  set2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set2 a b c d e u \<equiv> {[a]@aLIST@[c]| aLIST. set aLIST = {a}}"

definition 
  set3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set3 a b c d e u \<equiv> {w@[b,a]@aLIST| w aLIST. set aLIST = {a} \<and> set w \<subseteq> {a,b}}"

definition 
  set4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set4 a b c d e u \<equiv> {[a]@aLIST1@aLIST2@[c]@udLIST2| aLIST1 aLIST2 udLIST2 m. 
  set aLIST1 = {a}
  \<and> set aLIST2 = {a}
  \<and> length aLIST2 = m + 1
  \<and> length udLIST2 = 2 * (m + 1)
  \<and> (\<forall>n. n \<le> m \<longrightarrow> take 2 (drop (2 * n) udLIST2) = [u,d])}"

definition 
  set5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set5 a b c d e u \<equiv> {aLIST2@[c]@udLIST2| aLIST2 udLIST2 m. 
  set aLIST2 = {a}
  \<and> length aLIST2 = m + 1
  \<and> length udLIST2 = 2 * (m + 1)
  \<and> (\<forall>n. n \<le> m \<longrightarrow> take 2 (drop (2 * n) udLIST2) = [u,d])}"

definition 
  set6 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set6 a b c d e u \<equiv> {w@[b,a]@aLIST1@aLIST2@[c]@udLIST2| w aLIST1 aLIST2 udLIST2 m. 
  set w \<subseteq> {a,b}
  \<and> set aLIST1 = {a}
  \<and> set aLIST2 = {a}
  \<and> length aLIST2 = m + 1
  \<and> length udLIST2 = 2 * (m + 1)
  \<and> (\<forall>n. n \<le> m \<longrightarrow> take 2 (drop (2 * n) udLIST2) = [u,d])}"

definition 
  set7 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where
    "set7 a b c d e u \<equiv> {w@[b,a]@aLIST2@[c]@udLIST2@[u,e]| w aLIST2 udLIST2 m. 
  set w \<subseteq> {a,b}
  \<and> set aLIST2 = {a}
  \<and> length aLIST2 = m
  \<and> length udLIST2 = 2 * m
  \<and> (\<forall>n. n < m \<longrightarrow> take 2 (drop (2 * n) udLIST2) = [u,d])}"

lemma set1_set2: "set1 a b c d e u \<inter> set2 a b c d e u = {}"
  apply(simp add: set1_def set2_def)
  done

lemma set1_set3: "set1 a b c d e u \<inter> set3 a b c d e u = {}"
  apply(simp add: set1_def set3_def)
  done

lemma set1_set4: "set1 a b c d e u \<inter> set4 a b c d e u = {}"
  apply(simp add: set1_def set4_def)
  done

lemma set1_set5: "set1 a b c d e u \<inter> set5 a b c d e u = {}"
  apply(simp add: set1_def set5_def)
  apply(clarsimp)
  apply(case_tac aLIST2)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set1_set6: "set1 a b c d e u \<inter> set6 a b c d e u = {}"
  apply(simp add: set1_def set6_def)
  done

lemma set1_set7: "set1 a b c d e u \<inter> set7 a b c d e u = {}"
  apply(simp add: set1_def set7_def)
  done


lemma disjointI: "(\<exists>w. w \<in> A \<and> w \<in> B \<Longrightarrow> False) \<Longrightarrow> A \<inter> B = {}"
  apply(force)
  done

lemma disjointI2: "(\<forall>w. w \<in> A \<longrightarrow> w \<notin> B) \<Longrightarrow> A \<inter> B = {}"
  apply(force)
  done

lemma set2_set3: "
  a \<noteq> b
  \<Longrightarrow> a \<noteq> c
  \<Longrightarrow> set2 a b c d e u \<inter> set3 a b c d e u = {}"
  apply(simp add: set2_def set3_def)
  apply(rule disjointI2)
  apply(clarsimp)
  apply(subgoal_tac "last (a # aLIST @ [c]) = last (wa @ b # a # aLISTa)")
   prefer 2
   apply(force)
  apply(thin_tac "a # aLIST @ [c] = wa @ b # a # aLISTa")
  apply(clarsimp)
  apply(rule_tac xs="aLISTa" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set2_set4: "
  a \<noteq> c
  \<Longrightarrow> set2 a b c d e u \<inter> set4 a b c d e u = {}"
  apply(simp add: set2_def set4_def)
  apply(rule disjointI2)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set2_set5: "
  a \<noteq> c 
  \<Longrightarrow> set2 a b c d e u \<inter> set5 a b c d e u = {}"
  apply(simp add: set2_def set5_def)
  apply(rule disjointI2)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "tl ( a # aLIST) = tl(aLIST2 @ c # ys)")
   prefer 2
   apply(force)
  apply(thin_tac " a # aLIST = aLIST2 @ c # ys")
  apply(clarsimp)
  apply(case_tac aLIST2)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set2_set6: "
  a \<noteq> c
  \<Longrightarrow> set2 a b c d e u \<inter> set6 a b c d e u = {}"
  apply(simp add: set2_def set6_def)
  apply(rule disjointI2)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "tl ( a # aLIST) = tl(wa @ b # a # aLIST1 @ aLIST2 @ c # ys)")
   prefer 2
   apply(force)
  apply(thin_tac " a # aLIST = wa @ b # a # aLIST1 @ aLIST2 @ c # ys")
  apply(clarsimp)
  apply(case_tac aLIST2)
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac wa)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set2_set7: "
  a \<noteq> u
  \<Longrightarrow> set2 a b c d e u \<inter> set7 a b c d e u = {}"
  apply(simp add: set2_def set7_def)
  apply(rule disjointI2)
  apply(clarsimp)
  apply(rule_tac xs="aLIST" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma set3_set4: "
  a \<noteq> c
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> set3 a b c d e u \<inter> set4 a b c d e u = {}"
  apply(simp add: set3_def set4_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac xs="aLIST" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(erule_tac x="m" in allE)
  apply(clarsimp)
  done

lemma set3_set5: "
  a \<noteq> c 
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> set3 a b c d e u \<inter> set5 a b c d e u = {}"
  apply(simp add: set3_def set5_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac xs="aLIST" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(erule_tac x="m" in allE)
  apply(clarsimp)
  done

lemma set3_set6: "
  d \<noteq> c
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> set3 a b c d e u \<inter> set6 a b c d e u = {}"
  apply(simp add: set3_def set6_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac xs="aLIST" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(erule_tac x="m" in allE)
  apply(clarsimp)
  done

lemma set3_set7: "
  a \<noteq> u
  \<Longrightarrow> set3 a b c d e u \<inter> set7 a b c d e u = {}"
  apply(simp add: set3_def set7_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac xs="aLIST" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac xs="ysa" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma udLIST_no_c: "
  \<forall>n\<le>m. take 2 (drop (2 * n) udLIST2) = [u, d]
  \<Longrightarrow> length udLIST2 = Suc (Suc (2 * m))
  \<Longrightarrow> c \<in> set udLIST2
  \<Longrightarrow> c \<notin> {u, d}
  \<Longrightarrow> False"
  apply(subgoal_tac "\<exists>w1 w2. udLIST2 = w1 @[c]@w2")
   prefer 2
   apply (metis append_Cons append_Nil in_set_conv_decomp)
  apply(clarsimp)
  apply(case_tac "\<exists>n. length w1 = 2 * n")
   apply(clarsimp)
   apply(erule_tac x="n" in allE)
   apply(clarsimp)
  apply(case_tac "\<exists>n. length w1 = 2 * n +1 ")
   apply(clarsimp)
   apply(erule_tac x="n" in allE)
   apply(clarsimp)
  apply(arith)
  done

lemma set4_set5: "
  a \<noteq> c 
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> c \<noteq> u
  \<Longrightarrow> c \<noteq> d
  \<Longrightarrow> set4 a b c d e u \<inter> set5 a b c d e u = {}"
  apply(simp add: set4_def set5_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?w1.0="aLIST2" and ?w2.0="udLIST2" and ?w3.0="a # aLIST1 @ aLIST2a" and ?w4.0="udLIST2a" and c="c" in sync_at_c)
     apply(force)
    apply(clarsimp)
    apply(rule_tac ?m="m" and c="c" in udLIST_no_c)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac ?m="ma" and c="c" in udLIST_no_c)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma set5_set6: "
  d \<noteq> c
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> a \<noteq> c
  \<Longrightarrow> b \<noteq> c
  \<Longrightarrow> c \<noteq> u
  \<Longrightarrow> set5 a b c d e u \<inter> set6 a b c d e u = {}"
  apply(simp add: set5_def set6_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?w1.0="aLIST2" and ?w2.0="udLIST2" and ?w3.0="wa @ b # a # aLIST1 @ aLIST2a" and ?w4.0="udLIST2a" and c="c" in sync_at_c)
     apply(force)
    apply(clarsimp)
    apply(rule_tac ?m="m" and c="c" and ?udLIST2.0="udLIST2" in udLIST_no_c)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac ?m="ma" and c="c" and ?udLIST2.0="udLIST2a" in udLIST_no_c)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma set5_set7: "
  d \<noteq> c
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> a \<noteq> c
  \<Longrightarrow> b \<noteq> c
  \<Longrightarrow> c \<noteq> e
  \<Longrightarrow> c \<noteq> u
  \<Longrightarrow> a \<noteq> u
  \<Longrightarrow> set5 a b c d e u \<inter> set7 a b c d e u = {}"
  apply(simp add: set5_def set7_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?w1.0="aLIST2" and ?w2.0="udLIST2" and ?w3.0="wa @ b # a # aLIST2a" and ?w4.0="udLIST2a @ [u, e]" and c="c" in sync_at_c)
     apply(force)
    apply(clarsimp)
    apply(rule_tac ?m="m" and c="c" and ?udLIST2.0="udLIST2" in udLIST_no_c)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   prefer 2
   apply(clarsimp)
  apply(subgoal_tac "c \<notin> set udLIST2a")
   apply(force)
  apply(case_tac aLIST2a)
   apply(clarsimp)
  apply(case_tac "c \<notin> set udLIST2a")
   apply(blast)
  apply(subgoal_tac "False")
   apply(force)
  apply(rule_tac ?m="length list" and c="c" and ?udLIST2.0="udLIST2a" and u="u" and d="d" in udLIST_no_c)
     prefer 2
     apply(clarsimp)
    prefer 2
    apply(blast)
   prefer 2
   apply(blast)
  apply(rule_tac allI)
  apply(erule_tac P="%n. n<length aLIST2a \<longrightarrow> take 2 (drop (2 * n) udLIST2a) = [u, d]" and x="n" in allE)
  apply(rule impI)
  apply(erule impE)
   prefer 2
   apply(force)
  apply(force)
  done

lemma set6_set7: "
  d \<noteq> c
  \<Longrightarrow> a \<noteq> d
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> a \<noteq> c
  \<Longrightarrow> b \<noteq> c
  \<Longrightarrow> c \<noteq> u
  \<Longrightarrow> e \<noteq> d
  \<Longrightarrow> a \<noteq> u
  \<Longrightarrow> set6 a b c d e u \<inter> set7 a b c d e u = {}"
  apply(simp add: set6_def set7_def)
  apply(rule disjointI)
  apply(clarsimp)
  apply(rule_tac xs="udLIST2a" in rev_cases)
   prefer 2
   apply(clarsimp)
   apply(erule_tac x="m" in allE)+
   apply(clarsimp)
  apply(clarsimp)
  done

end
