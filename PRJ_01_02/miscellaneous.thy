section {*miscellaneous*}
theory
  miscellaneous

imports
  partial_functions

begin

definition list_to_option :: "
  'a list
  \<Rightarrow> 'a option"
  where
    "list_to_option w \<equiv>
  case w of [] \<Rightarrow> None | a # w' \<Rightarrow> Some a"

definition option_to_set :: "
  'a option
  \<Rightarrow> 'a set"
  where
    "option_to_set x =
  {y. Some y = x}"

definition option_to_setMap :: "
  'a option set
  \<Rightarrow> 'a set"
  where
    "option_to_setMap X =
  {x. \<exists>y  \<in> X. Some x = y}"

definition option_to_list :: "
  'a option
  \<Rightarrow> 'a list"
  where
    "option_to_list X =
  (case X of None \<Rightarrow> [] | Some A \<Rightarrow> [A])"

definition WrapInSome :: "'a set \<Rightarrow> 'a option set" where
  "WrapInSome A \<equiv> {None}\<union>{Some y |y. y  \<in> A}"

lemma option_to_setMapSubset: "
  A\<subseteq>B
  \<Longrightarrow> option_to_setMap A \<subseteq> option_to_setMap B"
  apply(simp add: option_to_setMap_def)
  apply(auto)
  done

lemma finite_diff_WrapInSome: "
  finite X
  \<Longrightarrow> finite (WrapInSome X - A)"
  apply(simp add: WrapInSome_def)
  done

lemma only_some_in_option_to_set: "
  x  \<in> option_to_set y
  \<Longrightarrow> y = Some x"
  apply(simp add: option_to_set_def)
  done

lemma only_some_in_option_to_set_prime: "
  y = Some x
  \<Longrightarrow> x  \<in> option_to_set y"
  apply(simp add: option_to_set_def)
  done

lemma none_makes_empty_option_to_set: "
  option_to_set y = {}
  \<Longrightarrow> y = None"
  apply(simp add: option_to_set_def)
  apply(case_tac y)
   apply(auto)
  done

lemma none_makes_empty_option_to_set_prime: "
  y = None
  \<Longrightarrow> option_to_set y = {}"
  apply(simp add: option_to_set_def)
  done

lemma only_proper_some_elems_in_option_to_setMap: "
  x  \<in> option_to_setMap Y
  \<Longrightarrow> \<exists>y  \<in> Y. y = Some x"
  apply(simp add: option_to_setMap_def)
  done

lemma only_proper_some_elems_in_option_to_setMap_prime: "
  y  \<in> Y
  \<Longrightarrow> y = Some x
  \<Longrightarrow> x  \<in> option_to_setMap Y"
  apply(simp add: option_to_setMap_def)
  done

lemma empty_set_and_none_make_empty_option_to_setMap: "
  option_to_setMap Y = {}
  \<Longrightarrow> Y = {} \<or> Y = {None}"
  apply(simp add: option_to_setMap_def)
  apply(auto)
  apply(rename_tac xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac xa)(*strict*)
   apply(auto)
  done

lemma empty_set_and_none_make_empty_option_to_setMap_prime: "
  Y = {}
  \<Longrightarrow> option_to_setMap Y = {}"
  apply(simp add: option_to_setMap_def)
  done

lemma empty_set_and_none_make_empty_option_to_setMap_prime_prime: "
  Y = {None}
  \<Longrightarrow> option_to_setMap Y = {}"
  apply(simp add: option_to_setMap_def)
  done

definition mset :: "'\<Sigma> list \<Rightarrow> ('\<Sigma> \<Rightarrow> nat)" where
  "mset w = (\<lambda>x. card{i| i. i < length w \<and> w!i = x})"

lemma mset0_to_set: "
  mset w a = 0
  \<Longrightarrow> a \<notin> set w"
  apply(simp add: mset_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1 w2. w = w1@a#w2")
   prefer 2
   apply(rule split_list)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(erule_tac
      x = "length w1"
      in allE)
  apply(clarsimp)
  done

lemma mset1: "
  mset [a] a = Suc 0"
  apply(simp only: mset_def)
  apply(rule_tac
      t = "{i |i::nat. i < length [a] \<and> [a] ! i = a}"
      and s = "{0}"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma mset1_prime: "
  a \<noteq> x
  \<Longrightarrow> mset [a] x = 0"
  apply(simp only: mset_def)
  apply(rule_tac
      t = "{i |i::nat. i < length [a] \<and> [a] ! i = a}"
      and s = "{0}"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma mset0: "
  mset [] a = 0"
  apply(simp only: mset_def)
  apply(rule_tac
      t = "{i |i::nat. i < length [] \<and> [] ! i = a}"
      and s = "{}"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma mset_Cons_eq: "
  mset (a # v) a = Suc (mset v a)"
  apply(simp add: mset_def)
  apply(rule_tac
      t = "{x. x < Suc (length v) \<and> (a # v) ! x = a}"
      and s = "{0}\<union>{(Suc x)| x. x < length v \<and> v ! x = a}"
      in ssubst)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      x = "x - 1"
      in exI)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(case_tac x)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x nat)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(rule_tac
      t = "card ({0} \<union> {Suc x |x. x < length v \<and> v ! x = a})"
      and s = "card ({0::nat}) + card {Suc x |x. x < length v \<and> v ! x = a}"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "card {0}"
      and s = "Suc 0"
      in ssubst)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      t = "{Suc x |x. x < length v \<and> v ! x = a}"
      and s = "(\<lambda>x. Suc x) ` {z. z < length v \<and> v ! z = a}"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "{t. t < length v \<and> v ! t = a}"
      and s = "{z. z < length v \<and> v ! z = a}"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "card (Suc ` {z. z < length v \<and> v ! z = a}) = card {z. z < length v \<and> v ! z = a}"
      and s = "inj_on Suc {z. z < length v \<and> v ! z = a}"
      in ssubst)
   apply(rule sym)
   apply(rule_tac
      f = "\<lambda>x. Suc x"
      in inj_on_iff_eq_card)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma mset_Cons_neq: "
  a \<noteq> z
  \<Longrightarrow> mset (a # v) z = mset v z"
  apply(simp add: mset_def)
  apply(rule_tac
      t = "{x. x < Suc (length v) \<and> (a # v) ! x = z}"
      and s = "{(Suc x)| x. x < length v \<and> v ! x = z}"
      in ssubst)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      x = "x - 1"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(case_tac x)
      apply(rename_tac x)(*strict*)
      apply(clarsimp)
     apply(rename_tac x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(case_tac x)
      apply(rename_tac x)(*strict*)
      apply(clarsimp)
     apply(rename_tac x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(case_tac x)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x nat)(*strict*)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule_tac
      t = "{t. t < length v \<and> v ! t = z}"
      and s = "{k. k < length v \<and> v ! k = z}"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "{Suc x |x. x < length v \<and> v ! x = z}"
      and s = " Suc ` {t. t < length v \<and> v ! t = z}"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "card (Suc ` {t. t < length v \<and> v ! t = z}) = card {t. t < length v \<and> v ! t = z}"
      and s = "inj_on Suc {t. t < length v \<and> v ! t = z}"
      in ssubst)
   apply(rule sym)
   apply(rule_tac
      f = "\<lambda>x. Suc x"
      in inj_on_iff_eq_card)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma mset_Cons: "
  mset (a # v) = (\<lambda>x. if x = a then Suc (mset v x) else mset v x)"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x = a")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rule mset_Cons_eq)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule mset_Cons_neq)
  apply(force)
  done

lemma mset_split: "
  mset (w @ a # v) = (\<lambda>x. if x = a then Suc (mset (w @ v) x) else mset (w@v) x)"
  apply(induct w arbitrary: a v)
   apply(rename_tac a v)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "[]@v"
      and s = "v"
      in ssubst)
    apply(rename_tac a v)(*strict*)
    apply(force)
   apply(rename_tac a v)(*strict*)
   apply(rule mset_Cons)
  apply(rename_tac a w aa v)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x = "aa"
      in meta_allE)
  apply(erule_tac
      x = "v"
      in meta_allE)
  apply(rule_tac
      t = "mset (a # w @ aa # v)"
      and s = "(\<lambda>x. if x = a then Suc (mset (w @ aa # v) x) else mset (w @ aa # v) x)"
      in ssubst)
   apply(rename_tac a w aa v)(*strict*)
   apply(rule mset_Cons)
  apply(rename_tac a w aa v)(*strict*)
  apply(rule ext)
  apply(rename_tac a w aa v x)(*strict*)
  apply(case_tac "x = a")
   apply(rename_tac a w aa v x)(*strict*)
   apply(case_tac "x = aa")
    apply(rename_tac a w aa v x)(*strict*)
    apply(clarsimp)
    apply(rename_tac a w v)(*strict*)
    apply(rule sym)
    apply(rule mset_Cons_eq)
   apply(rename_tac a w aa v x)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w aa v)(*strict*)
   apply(rule sym)
   apply(rule mset_Cons_eq)
  apply(rename_tac a w aa v x)(*strict*)
  apply(case_tac "x = aa")
   apply(rename_tac a w aa v x)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w aa v)(*strict*)
   apply(rule sym)
   apply(rule mset_Cons_neq)
   apply(force)
  apply(rename_tac a w aa v x)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule mset_Cons_neq)
  apply(force)
  done

lemma mset_drop_part: "
  mset (w1 @ x @ v1) = mset (w2 @ x @ v2)
  \<Longrightarrow> mset (w1 @ v1) = mset (w2 @ v2)"
  apply(induct x arbitrary: w1 v1 w2 v2)
   apply(rename_tac w1 v1 w2 v2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(erule_tac
      x = "w1"
      in meta_allE)
  apply(erule_tac
      x = "v1"
      in meta_allE)
  apply(erule_tac
      x = "w2"
      in meta_allE)
  apply(erule_tac
      x = "v2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a x w1 v1 w2 v2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(rule ext)
  apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
  apply(subgoal_tac "(\<lambda>y. if y = a then Suc (mset (w1 @ x @ v1) y) else mset (w1 @ x @ v1) y) xa = (\<lambda>y. if y = a then Suc (mset (w2 @ x @ v2) y) else mset (w2 @ x @ v2) y) xa")
   apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
   apply(case_tac "xa = a")
    apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
  apply(rule_tac
      t = "\<lambda>xa. (if xa = a then Suc (mset (w1 @ x @ v1) xa) else mset (w1 @ x @ v1) xa)"
      and s = "mset (w1 @ a # x @ v1)"
      in subst)
   apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
   apply(rule mset_split)
  apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
  apply(rule_tac
      t = "\<lambda>xa. (if xa = a then Suc (mset (w2 @ x @ v2) xa) else mset (w2 @ x @ v2) xa)"
      and s = "mset (w2 @ a # x @ v2)"
      in subst)
   apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
   apply(rule mset_split)
  apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
  apply(force)
  done

lemma mset_add_part: "
  mset (w1 @ v1) = mset (w2 @ v2)
  \<Longrightarrow> mset (w1 @ x @ v1) = mset (w2 @ x @ v2)"
  apply(induct x arbitrary: w1 v1 w2 v2)
   apply(rename_tac w1 v1 w2 v2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      s = "\<lambda>xa. (if xa = a then Suc (mset (w1 @ x @ v1) xa) else mset (w1 @ x @ v1) xa)"
      and t = "mset (w1 @ a # x @ v1)"
      in ssubst)
   apply(rename_tac a x w1 v1 w2 v2)(*strict*)
   apply(rule mset_split)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(rule_tac
      s = "\<lambda>xa. (if xa = a then Suc (mset (w2 @ x @ v2) xa) else mset (w2 @ x @ v2) xa)"
      and t = "mset (w2 @ a # x @ v2)"
      in ssubst)
   apply(rename_tac a x w1 v1 w2 v2)(*strict*)
   apply(rule mset_split)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(erule_tac
      x = "w1"
      in meta_allE)
  apply(erule_tac
      x = "v1"
      in meta_allE)
  apply(erule_tac
      x = "w2"
      in meta_allE)
  apply(erule_tac
      x = "v2"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac a x w1 v1 w2 v2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w1 v1 w2 v2)(*strict*)
  apply(rule ext)
  apply(rename_tac a x w1 v1 w2 v2 xa)(*strict*)
  apply(clarsimp)
  done

lemma foldl_option_to_list_shorter: "
  length (foldl (@) [] (map (option_to_list) w')) \<le> length w'"
  apply(induct w' rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(case_tac x)
   apply(rename_tac x xs)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac x xs a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs a)(*strict*)
  apply(simp add: option_to_list_def)
  done

theorem decompose_sequential_execution_input_output_specification2: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X Y)
  \<Longrightarrow> (SPi_H X Y \<Longrightarrow> SPo_H X (H X Y))
  \<Longrightarrow> (SPo_H X (H X Y) \<Longrightarrow> SPi_FH (H X Y))
  \<Longrightarrow> (\<And>P. SPo_H X (H X Y) \<Longrightarrow> SPo_FH (H X Y) (P (H X Y)) \<Longrightarrow> SPo_F X (P (H X Y)))
  \<Longrightarrow> (\<And>X. SPi_FH X \<Longrightarrow> SPo_FH X (G X))
  \<Longrightarrow> SPo_F X (G (H X Y))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X)
  \<Longrightarrow> (SPi_H X \<Longrightarrow> SPo_H X (H X))
  \<Longrightarrow> (SPo_H X (H X) \<Longrightarrow> SPi_FH (H X))
  \<Longrightarrow> (\<And>P. SPo_H X (H X) \<Longrightarrow> SPo_FH (H X) (P (H X)) \<Longrightarrow> SPo_F X (P (H X)))
  \<Longrightarrow> (\<And>X. SPi_FH X \<Longrightarrow> SPo_FH X (G X))
  \<Longrightarrow> SPo_F X (G (H X))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification3: "
  SPi_F X Y
  \<Longrightarrow> (SPi_F X Y \<Longrightarrow> SPi_H X Z)
  \<Longrightarrow> (SPi_H X Z \<Longrightarrow> SPo_H X Y (H X Z))
  \<Longrightarrow> (SPo_H X Y (H X Z) \<Longrightarrow> SPi_FH (H X Z) Z)
  \<Longrightarrow> (\<And>P. SPo_H X Y (H X Z) \<Longrightarrow> SPo_FH (H X Z) Y (P (H X Z)) \<Longrightarrow> SPo_F X Y (P (H X Z)))
  \<Longrightarrow> SEL Y = Z
  \<Longrightarrow> (\<And>X. SPi_FH X Z \<Longrightarrow> SPo_FH X Y (G X))
  \<Longrightarrow> SPo_F X Y (G (H X Z))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification4: "
  SPi_F X Z
  \<Longrightarrow> (SPi_F X Z \<Longrightarrow> SPi_H X Z)
  \<Longrightarrow> (SPi_H X Z \<Longrightarrow> SPo_H X Y (H X))
  \<Longrightarrow> (SPo_H X Y (H X) \<Longrightarrow> SPi_FH (H X) Z)
  \<Longrightarrow> (\<And>P. SPo_H X Y (H X) \<Longrightarrow> SPo_FH (H X) Y (P (H X)) \<Longrightarrow> SPo_F X Y (P (H X)))
  \<Longrightarrow> SEL Y = Z
  \<Longrightarrow> (\<And>X. SPi_FH X Z \<Longrightarrow> SPo_FH X Y (G X))
  \<Longrightarrow> SPo_F X Y (G (H X))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification_simp: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X)
  \<Longrightarrow> (SPi_H X \<Longrightarrow> SPo_H X (H X))
  \<Longrightarrow> (SPo_H X (H X) \<Longrightarrow> SPi_FH (H X))
  \<Longrightarrow> (\<And>A. SPo_H X (H X) \<Longrightarrow> SPo_FH (H X) A \<Longrightarrow> SPo_F X A)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification2_simp: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X Y)
  \<Longrightarrow> (SPi_H X Y \<Longrightarrow> SPo_H X (H X Y))
  \<Longrightarrow> (SPo_H X (H X Y) \<Longrightarrow> SPi_FH (H X Y))
  \<Longrightarrow> (\<And>A. SPo_H X (H X Y) \<Longrightarrow> SPo_FH (H X Y) A \<Longrightarrow> SPo_F X A)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X Y))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification_simp2: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X)
  \<Longrightarrow> (SPi_H X \<Longrightarrow> SPo_H X (H X))
  \<Longrightarrow> (SPo_H X (H X) \<Longrightarrow> SPi_FH (H X))
  \<Longrightarrow> (\<And>A B. SPo_H X A \<Longrightarrow> SPo_FH A B \<Longrightarrow> SPo_F X B)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification2_simp2: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X Y)
  \<Longrightarrow> (SPi_H X Y \<Longrightarrow> SPo_H X (H X Y))
  \<Longrightarrow> (SPo_H X (H X Y) \<Longrightarrow> SPi_FH (H X Y))
  \<Longrightarrow> (\<And>A B. SPo_H X A \<Longrightarrow> SPo_FH A B \<Longrightarrow> SPo_F X B)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X Y))"
  apply(force)
  done

(*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification2_simp
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification_simp
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification4
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification3
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification2
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification_simp2
  (*deprecated theorem*)
hide_fact decompose_sequential_execution_input_output_specification2_simp2


theorem decompose_sequential_execution_input_output_specification_simp3: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X)
  \<Longrightarrow> (SPi_H X \<Longrightarrow> SPo_H X (H X))
  \<Longrightarrow> (SPo_H X (H X) \<Longrightarrow> SPi_FH (H X))
  \<Longrightarrow> (\<And>A B C. SPo_H A B \<Longrightarrow> SPo_FH B C \<Longrightarrow> SPo_F A C)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification2_simp3: "
  SPi_F X
  \<Longrightarrow> (SPi_F X \<Longrightarrow> SPi_H X Y)
  \<Longrightarrow> (SPi_H X Y \<Longrightarrow> SPo_H X (H X Y))
  \<Longrightarrow> (SPo_H X (H X Y) \<Longrightarrow> SPi_FH (H X Y))
  \<Longrightarrow> (\<And>A B C. SPo_H A B \<Longrightarrow> SPo_FH B C \<Longrightarrow> SPo_F A C)
  \<Longrightarrow> (\<And>A. SPi_FH A \<Longrightarrow> SPo_FH A (G A))
  \<Longrightarrow> SPo_F X (G (H X Y))"
  apply(force)
  done

end
