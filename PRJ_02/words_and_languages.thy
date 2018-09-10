section {*words\_and\_languages*}
theory
  words_and_languages

imports
  PRJ_02__ENTRY

begin

lemma example_alphabet: "
  { 0, 1 }  \<in> (UNIV :: nat set set)"
  apply(force)
  done

lemma example_word: "
  [ 0, 1 ]  \<in> (UNIV :: nat list set)"
  apply(force)
  done

lemma example_language: "
  { [ 0, 1 ] }  \<in> (UNIV :: nat list set set )"
  apply(force)
  done

definition alphabet_to_language :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set" ("\<langle>_\<rangle>") where
  "alphabet_to_language A \<equiv>
  {w. \<exists>v  \<in> A. w = [v]}"

lemma example_alphabet_to_language: "
  alphabet_to_language {0, 1} = {[0], [1]}"
  apply(simp add: alphabet_to_language_def)
  apply(force)
  done

definition append_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" ("(_ @\<^sub>L\<^sub>L _)") where
  "append_language A B \<equiv>
  {w. \<exists>a  \<in> A. \<exists>b  \<in> B. w = a @ b}"

lemma example_append_language: "
  append_language {[0], [1]} {[2], [3]} = {[0, 2], [0, 3], [1, 2], [1, 3]}"
  apply(simp add: append_language_def)
  apply(force)
  done

definition append_alphabet :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set" ("(_ @\<^sub>L\<^sub>A _)") where
  "append_alphabet L \<Sigma> \<equiv>
  append_language L (alphabet_to_language \<Sigma>)"

lemma example_append_alphabet: "
  append_alphabet { [ 0 ] , [ 1 ] } { 2, 3 } = { [ 0, 2 ] , [ 0, 3 ] , [ 1, 2 ] , [ 1, 3 ] } "
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(force)
  done

definition kleene_star :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set" ("(_\<^sup>\<star>)") where
  "kleene_star A \<equiv>
  {w. set w \<subseteq> A}"

lemma example1_kleene_star: "
  {[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]} \<subseteq> kleene_star {0, 1}"
  apply(simp add: kleene_star_def)
  done

definition prefix :: "
  '\<Sigma> list
  \<Rightarrow> '\<Sigma> list
  \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "prefix a b \<equiv>
  \<exists>c. a @ c = b"

lemma example1_prefix: "
  prefix [0, 1] [0, 1, 2, 3]"
  apply(simp add: prefix_def)
  done

lemma prefix_take_prime: "
  i\<le>length w
  \<Longrightarrow> prefix (take i w) w"
  apply (metis append_take_drop_id_hlp prefix_def)
  done

definition strict_prefix :: "
  '\<Sigma> list
  \<Rightarrow> '\<Sigma> list
  \<Rightarrow> bool" ("_ \<sqsubset> _" 100) where
  "strict_prefix a b \<equiv>
  \<exists>c. c \<noteq> [] \<and> a @ c = b"

lemma example1_strict_prefix: "
  strict_prefix [0, 1] [0, 1, 2]"
  apply(simp add: strict_prefix_def)
  done

lemma example2_strict_prefix: "
  \<not> (strict_prefix [0, 1, 2] [0, 1, 2])"
  apply(simp add: strict_prefix_def)
  done

definition prefix_closure :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "prefix_closure L \<equiv>
  {w. \<exists>v. v  \<in> L \<and> prefix w v}"

lemma example1_prefix_closure: "
  prefix_closure {[0], [0, 1, 2] } = {[], [0], [0, 1], [0, 1, 2]}"
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(erule disjE)
    apply(rename_tac x c)(*strict*)
    apply(case_tac x)
     apply(rename_tac x c)(*strict*)
     apply(clarsimp)
    apply(rename_tac x c a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(case_tac x)
    apply(rename_tac x c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac c list)(*strict*)
   apply(case_tac list)
    apply(rename_tac c list)(*strict*)
    apply(clarsimp)
   apply(rename_tac c list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac c lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac c lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac c lista a list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(force)
  done

lemma prefix_vs_take: "
  prefix w1 w2 \<longleftrightarrow> (\<exists>k. w1 = take k w2)"
  apply(simp add: prefix_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      x = "length w1"
      in exI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      x = "drop k w2"
      in exI)
  apply(force)
  done

definition suffix :: "
  '\<Sigma> list
  \<Rightarrow> '\<Sigma> list
  \<Rightarrow> bool" (infixl "\<sqsupseteq>" 150) where
  "suffix a b \<equiv>
  \<exists>c. a = c @ b"

definition suffix_closure :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "suffix_closure A \<equiv>
  {w. \<exists>v. v \<in> A \<and> v \<sqsupseteq> w}"

lemma mutual_prefix_prefix_hlp: "
  length a \<le> length c
  \<Longrightarrow> a @ b = c @ d
  \<Longrightarrow> prefix a c"
  apply(simp add: prefix_def)
  apply(rule_tac
      x = "take (length c - length a) b"
      in exI)
  apply (metis append_eq_conv_conj take_all take_append)
  done

lemma mutual_prefix_prefix: "
  a @ b = c @ d
  \<Longrightarrow> prefix a c \<or> prefix c a"
  apply(case_tac "length a \<le> length c")
   apply(rule disjI1)
   apply(rule mutual_prefix_prefix_hlp)
    apply(force)
   apply(force)
  apply(rule disjI2)
  apply(rule mutual_prefix_prefix_hlp)
   apply(force)
  apply(rule sym)
  apply(force)
  done

lemma mutual_prefix_equal_suffix: "
  suffix (x#w1) (y#w2) \<or> suffix (y#w2) (x#w1)
  \<Longrightarrow> length w1 = length w2
  \<Longrightarrow> w1 = w2 \<and> x = y"
  apply(erule disjE)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply (metis length_shorter_append2 list.sel(1) list.sel(3) list.size(4) order_refl self_append_conv2)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply (metis length_shorter_append2 list.sel(1) list.sel(3) list.size(4) order_refl self_append_conv2)
  done

lemma mutual_prefix_equal_prefix: "
  prefix (x#w1) (y#w2) \<or> prefix (y#w2) (x#w1)
  \<Longrightarrow> length w1 = length w2
  \<Longrightarrow> w1 = w2 \<and> x = y"
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma mutual_suffix_suffix: "
  a @ b = c @ d
  \<Longrightarrow> suffix b d \<or> suffix d b"
  apply(subgoal_tac "prefix a c \<or> prefix c a")
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(force)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma mutual_prefix_strict_prefix: "
  w1 @ w2 = w3 @ w4
  \<Longrightarrow> prefix w1 w3 \<or> strict_prefix w3 w1"
  apply(case_tac "w1 = w3")
   apply(simp add: prefix_def)
  apply(subgoal_tac "prefix w1 w3 \<or> prefix w3 w1")
   prefer 2
   apply (metis mutual_prefix_prefix)
  apply(erule disjE)
   apply(force)
  apply(simp add: strict_prefix_def)
  apply(rule disjI2)
  apply(simp add: prefix_def)
  apply(force)
  done

lemma mutual_strict_prefix_prefix: "
  a @ b = c @ d
  \<Longrightarrow> strict_prefix a c \<or> prefix c a"
  apply(subgoal_tac "prefix a c \<or> prefix c a")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(erule exE) +
   apply(rename_tac ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac ca)(*strict*)
    apply(rule disjI2)
    apply(simp add: prefix_def)
   apply(rename_tac ca aa list)(*strict*)
   apply(rule disjI1)
   apply(simp add: strict_prefix_def)
   apply(force)
  apply(rule disjI2)
  apply(simp add: prefix_def)
  done

lemma mutual_suffix_suffix2: "
  a @ b @ c = d @ e @ f
  \<Longrightarrow> c = f
  \<Longrightarrow> suffix b e \<or> suffix e b"
  apply(subgoal_tac "prefix a d \<or> prefix d a")
   apply(erule disjE)
    apply(rule disjI1)
    apply(clarsimp)
    apply(simp add: prefix_def suffix_def)
    apply(clarsimp)
   apply(simp add: prefix_def suffix_def)
   apply(force)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma mutual_prefix_prefix_with_left_context: "
  w@v1@w'@v1' = w@v2@w'@v2'
  \<Longrightarrow> prefix v1 v2 \<or> prefix v2 v1"
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma mutual_strict_prefix_strict_prefix2: "
  px @ pa @ pb = py @ qa @ qb
  \<Longrightarrow> px = py
  \<Longrightarrow> strict_prefix pa qa \<or> strict_prefix qa pa \<or> pa = qa"
  apply(subgoal_tac "prefix pa qa \<or> prefix qa pa")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def strict_prefix_def)
   apply(force)
  apply(simp add: prefix_def strict_prefix_def)
  apply(force)
  done

lemma mutual_strict_prefix_strict_prefix: "
  a @ x = b @ y
  \<Longrightarrow> strict_prefix a b \<or> strict_prefix b a \<or> a = b"
  apply(subgoal_tac "prefix a b \<or> prefix b a")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(case_tac "a = b")
   apply(force)
  apply(erule disjE)
   apply(rule disjI1)
   apply(simp add: prefix_def strict_prefix_def)
   apply(force)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(simp add: prefix_def strict_prefix_def)
  apply(force)
  done

lemma equal_prefix_removal: "
  prefix v w1
  \<Longrightarrow> prefix v w2
  \<Longrightarrow> drop (length v) w1 = drop (length v) w2
  \<Longrightarrow> w1 = w2"
  apply (metis append_take_drop_id dropPrecise prefix_def takePrecise)
  done

lemma suffix_trans: "
  suffix a b
  \<Longrightarrow> suffix b c
  \<Longrightarrow> suffix a c"
  apply(simp add: suffix_def)
  apply(force)
  done

lemma drop_suffix_closure: "
  w  \<in> A
  \<Longrightarrow> drop n w  \<in> suffix_closure A"
  apply(simp add: suffix_closure_def suffix_def)
  apply (metis append_take_drop_id)
  done

lemma prefix_drop_none: "
  prefix v w
  \<Longrightarrow> drop (length w) v = []"
  apply(simp add: prefix_def)
  apply(force)
  done

lemma drop_preserves_prefix: "
  prefix w v
  \<Longrightarrow> prefix (drop n w) (drop n v)"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma prefix_reflexive: "
  prefix x x"
  apply(simp add: prefix_def)
  done

lemma prefix_closure_single_prefix: "
  prefix_closure {w} \<subseteq> prefix_closure {v}
  \<Longrightarrow> prefix w v"
  apply(simp add: prefix_closure_def)
  apply(subgoal_tac "w \<in> {wa. wa \<sqsubseteq> w}")
   apply(force)
  apply(thin_tac "{wa. wa \<sqsubseteq> w} \<subseteq> {w. w \<sqsubseteq> v}")
  apply(clarsimp)
  apply(rule prefix_reflexive)
  done

lemma prefix_transitive: "
  prefix x y
  \<Longrightarrow> prefix y z
  \<Longrightarrow> prefix x z"
  apply(simp add: prefix_def)
  apply(force)
  done

lemma prefix_append: "
  prefix x (x @ y)"
  apply(simp add: prefix_def)
  done

lemma strict_prefix_is_shorter: "
  A \<inter> B = {}
  \<Longrightarrow> w  \<in> A
  \<Longrightarrow> v  \<in> B
  \<Longrightarrow> w \<sqsubseteq> v
  \<Longrightarrow> length w < length v"
  apply(simp add: prefix_def)
  apply(auto)
  done

lemma strict_prefix_is_shorter2: "
  w \<noteq> v
  \<Longrightarrow> prefix w v
  \<Longrightarrow> length w < length v"
  apply(rule_tac A = "{w}" and B = "{v}" in strict_prefix_is_shorter,simp + )
  done

lemma non_empty_extension_exists: "
  A\<subseteq>prefix_closure B
  \<Longrightarrow> A\<inter>B = {}
  \<Longrightarrow> \<forall>w \<in> A.\<exists>v \<in> B.(prefix w v \<and> length w < length v)"
  apply(rule ballI)
  apply(rename_tac w)(*strict*)
  apply(simp add: prefix_closure_def)
  apply(subgoal_tac "\<exists>v. v \<in> B \<and> prefix w v")
   apply(rename_tac w)(*strict*)
   apply(erule exE)
   apply(rename_tac w v)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "v"
      in bexI)
    apply(rename_tac w v)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      A = "A"
      and B = "B"
      in strict_prefix_is_shorter)
       apply(rename_tac w v)(*strict*)
       apply(auto)
  done

lemma mutual_prefix_implies_equality: "
  prefix a b
  \<Longrightarrow> prefix b a
  \<Longrightarrow> a = b"
  apply(simp add: prefix_def)
  apply(auto)
  done

lemma prefix_closure_single_eq: "
  prefix_closure {w} = prefix_closure {v}
  \<Longrightarrow> w = v"
  apply(rule mutual_prefix_implies_equality)
   apply(rule prefix_closure_single_prefix)
   apply(force)
  apply(rule prefix_closure_single_prefix)
  apply(force)
  done

lemma mutual_prefix_implies_equality2: "
  prefix a b
  \<Longrightarrow> length b \<le> length a
  \<Longrightarrow> a = b"
  apply(simp add: prefix_def)
  apply(auto)
  done

lemma prefix_common_max: "
  prefix w1 w
  \<Longrightarrow> prefix w2 w
  \<Longrightarrow> length w1 \<le> length w2
  \<Longrightarrow> prefix w1 w2"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply (metis mutual_prefix_prefix mutual_prefix_implies_equality2 prefix_reflexive prefix_def)
  done

lemma prefix_closure_subset: "
  A \<subseteq> prefix_closure A"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_vs_take: "
  prefix_closure L = {take k w| k w. w  \<in> L}"
  apply(simp add: prefix_closure_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(subgoal_tac "(\<exists>k. x = take k v)")
    apply(rename_tac x v)(*strict*)
    apply(force)
   apply(rename_tac x v)(*strict*)
   apply(simp add: prefix_vs_take)
  apply(clarsimp)
  apply(rename_tac k w)(*strict*)
  apply(rule_tac
      x = "w"
      in exI)
  apply(simp add: prefix_vs_take)
  apply(force)
  done

lemma prefix_closure_idempotent: "
  prefix_closure A = prefix_closure (prefix_closure A)"
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(force)
  done

lemma prefix_closure_preserves_subseteq: "
  A \<subseteq> B
  \<Longrightarrow> prefix_closure A \<subseteq> prefix_closure B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_preserves_union: "
  (prefix_closure (A \<union> B)) = (prefix_closure A) \<union> prefix_closure B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_intersection: "
  (prefix_closure (A \<inter> B)) \<subseteq> (prefix_closure A) \<inter> prefix_closure B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_intersection2: "
  A = (prefix_closure A)
  \<Longrightarrow> B = (prefix_closure B)
  \<Longrightarrow> (prefix_closure (A \<inter> B)) = (prefix_closure A) \<inter> prefix_closure B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_intersection3: "
  A = (prefix_closure A)
  \<Longrightarrow> B = (prefix_closure B)
  \<Longrightarrow> (prefix_closure (A \<inter> B)) = A \<inter> B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closure_subset2: "
  A \<subseteq> B
  \<Longrightarrow> B = (prefix_closure B)
  \<Longrightarrow> (prefix_closure A) \<subseteq> B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefixExists: "
  L = prefix_closure L
  \<Longrightarrow> w @ v  \<in> L
  \<Longrightarrow> w  \<in> L"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefixExists2: "
  L = prefix_closure L
  \<Longrightarrow> prefix w v
  \<Longrightarrow> v \<in> L
  \<Longrightarrow> w  \<in> L"
  apply(simp add: prefix_def)
  apply(erule exE)
  apply(rename_tac c)(*strict*)
  apply(rule prefixExists)
   apply(rename_tac c)(*strict*)
   apply(blast)
  apply(rename_tac c)(*strict*)
  apply(blast)
  done

lemma pcAbsorb: "
  A = prefix_closure A
  \<Longrightarrow> (prefix_closure(A\<inter>B))\<inter>A = prefix_closure(A\<inter>B)"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closureEQ: "
  B\<subseteq>A
  \<Longrightarrow> B = prefix_closure B
  \<Longrightarrow> (prefix_closure(A\<inter>B)) = B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma ensureNBpreservesPC: "
  A = prefix_closure A
  \<Longrightarrow> A \<inter> (prefix_closure (A \<inter> B)) = (prefix_closure (A \<inter> prefix_closure (A \<inter> B)))"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefix_closureDecomp: "
  (prefix_closure{w@[a]}) = (prefix_closure{w})\<union>{w@[a]}"
  apply(rule_tac
      xs = "w"
      in rev_induct)
   apply(simp)
   apply(simp add: prefix_closure_def prefix_def)
   apply(rule equalityI)
    apply(rule subsetI)
    apply(rename_tac x)(*strict*)
    apply(simp)
    apply(erule exE)
    apply(rename_tac x c)(*strict*)
    apply(case_tac "c")
     apply(rename_tac x c)(*strict*)
     apply(simp)
    apply(rename_tac x c aa list)(*strict*)
    apply(case_tac "x")
     apply(rename_tac x c aa list)(*strict*)
     apply(clarsimp) +
  apply(rename_tac x xs)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
   apply(rename_tac x xs xa c)(*strict*)
   apply(case_tac "\<exists>v a. c = v@[a]")
    apply(rename_tac x xs xa c)(*strict*)
    apply(erule_tac exE)
    apply(rename_tac x xs xa c v)(*strict*)
    apply(erule_tac exE)
    apply(rename_tac x xs xa c v aa)(*strict*)
    apply(rule_tac
      x = "v"
      in exI)
    apply(simp)
   apply(rename_tac x xs xa c)(*strict*)
   prefer 2
   apply(rule_tac
      x = "c@[a]"
      in exI)
   apply(simp)
  apply(rename_tac x xs xa c)(*strict*)
  apply(case_tac "c = []")
   apply(rename_tac x xs xa c)(*strict*)
   apply(simp)
  apply(rename_tac x xs xa c)(*strict*)
  apply(subgoal_tac "\<exists>v a. c = v@[a]")
   apply(rename_tac x xs xa c)(*strict*)
   apply(simp)
  apply(rename_tac x xs xa c)(*strict*)
  apply(rule emptyString)
  apply(simp)
  done

lemma strict_prefix_to_prefix: "
  strict_prefix a b
  \<Longrightarrow> prefix a b"
  apply(simp add: strict_prefix_def prefix_def)
  apply(auto)
  done

lemma starSubset: "
  A \<subseteq> B
  \<Longrightarrow> kleene_star A \<subseteq> kleene_star B"
  apply(simp add: kleene_star_def)
  apply(auto)
  done

lemma emptyIsInkleene_star: "
  [] \<notin> kleene_star A
  \<Longrightarrow> P"
  apply(simp add: kleene_star_def)
  done

lemma StarPrefixClosed: "
  a @ b  \<in> kleene_star S
  \<Longrightarrow> a  \<in> kleene_star S"
  apply(simp add: kleene_star_def)
  done

lemma fromStrans: "
  A \<subseteq> kleene_star S
  \<Longrightarrow> x  \<in> A
  \<Longrightarrow> set x \<subseteq> S"
  apply(simp add: kleene_star_def)
  apply(auto)
  done

lemma splitLangSet: "
  {w  \<in> kleene_star S. length w \<le> Suc n} = {w  \<in> kleene_star S. length w \<le> n} \<union> append_language {w  \<in> kleene_star S. length w = n} (alphabet_to_language S)"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(case_tac "length x = Suc n")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(simp add: append_language_def alphabet_to_language_def)
    apply(rule_tac
      x = "take n x"
      in exI)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(simp add: kleene_star_def)
     apply(rule_tac
      B = "set x"
      in subset_trans)
      apply(rename_tac x)(*strict*)
      apply(rule subsetI)
      apply(rename_tac x xa)(*strict*)
      apply(rule in_set_takeD)
      apply(blast)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(rule conjI)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
     apply(simp add: ord_class.min_def)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "\<exists>xp xa. x = xp@[xa]")
     apply(rename_tac x)(*strict*)
     apply(erule exE) +
     apply(rename_tac x xp xa)(*strict*)
     apply(rule_tac
      x = "[xa]"
      in exI)
     apply(rule conjI)
      apply(rename_tac x xp xa)(*strict*)
      apply(rule_tac
      x = "xa"
      in bexI)
       apply(rename_tac x xp xa)(*strict*)
       apply(clarsimp)
      apply(rename_tac x xp xa)(*strict*)
      apply(simp add: kleene_star_def)
     apply(rename_tac x xp xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule existenceOfLast)
    apply(arith)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: kleene_star_def alphabet_to_language_def append_language_def)
  apply(clarsimp)
  done

lemma numberOfWordsUpToLength1: "
  card {w. w \<in> kleene_star {} \<and> length w \<le> n} = (\<Sum>i = 0..n. (card {})^i)"
  apply(auto)
  apply(simp add: kleene_star_def)
  apply(rule_tac
      s = "{[]}"
      and t = "{w. w = [] \<and> length w \<le> n}"
      in ssubst)
   apply(auto)
  apply(induct_tac n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma numberOfWordsUpToLength2: "
  card S >0
  \<Longrightarrow> card {w. w \<in> (kleene_star S) \<and> length w \<le> n} = (\<Sum>i = 0..n. (card S)^i)"
  apply(induct_tac n)
   apply(clarsimp)
   apply(rule_tac
      s = "{[]}"
      and t = "{w. w = [] \<and> w  \<in> (kleene_star S)}"
      in ssubst)
    apply(rule equalityI)
     apply(clarsimp)
    apply(clarsimp)
    apply(simp add: kleene_star_def)
   apply(rule card1Elem1)
    (*#(S^ \<le> n + 1) = SUM i 0 (n + 1) (#S)^i*)
    (*split SUM *)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "sum ((^) (card S)) {0..n} + (card S)^(n + 1)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
    (*#(S^ \<le> n + 1) = SUM i 0 n (#S)^i + (#S)^(n + 1) *)
    (*use Induction Hypothesis *)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "card{w  \<in> kleene_star S. length w \<le> n}"
      and t = "sum ((^) (card S)) {0..n}"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule sym)
   apply(blast)
    (*#(S^ \<le> n + 1) = #(S^ \<le> n) + (#S)^(n + 1) *)
    (*split S^ \<le> n + 1 *)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "{w  \<in> kleene_star S. length w \<le> n} \<union> (append_language {w  \<in> kleene_star S. length w = n}((alphabet_to_language S)))"
      and t = "{w  \<in> kleene_star S. length w \<le> Suc n}"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule splitLangSet)
    (*#(S^ \<le> n + S^nS) = #(S^ \<le> n) + (#S)^(n + 1) *)
    (*from the Induction Hypothsis we also get the finiteness*)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "finite {w  \<in> kleene_star S. length w \<le> n}")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(case_tac "finite {w  \<in> kleene_star S. length w \<le> n}")
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "card ({w  \<in> kleene_star S. length w \<le> n}) = 0")
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
    (*no change *)
    (*extract the (disjoint) union from the card *)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "card (append_language {w  \<in> kleene_star S. length w = n} (alphabet_to_language S))"
      and t = "card S ^ (n + 1)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   defer
   apply(rule Finite_Set.card_Un_disjoint)
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    defer
    apply(rule showDisj)
     apply(rename_tac n x)(*strict*)
     apply(clarsimp)
     apply(simp add: alphabet_to_language_def append_language_def)
     apply(clarsimp)
    apply(rename_tac n x)(*strict*)
    apply(simp add: alphabet_to_language_def append_language_def)
    apply(clarsimp)
    (*(#S)^(n + 1) = #(S^ = nS) *)
    (*finite (S^ = nS) *)
    (*obtain finite(S^ = n \<times> S)*)
   apply(rename_tac n)(*strict*)
   defer
   apply(subgoal_tac "finite ({w  \<in> kleene_star S. length w = n} \<times> ((alphabet_to_language S)))")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule Finite_Set.finite_cartesian_product)
     apply(rename_tac n)(*strict*)
     apply(rule_tac
      B = "{w  \<in> kleene_star S. length w \<le> n}"
      in Finite_Set.finite_subset)
      apply(rename_tac n)(*strict*)
      apply(clarsimp)
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(simp add: alphabet_to_language_def)
    apply(rule_tac
      s = "{[x]| x. x \<in> S}"
      and t = "{w. \<exists>v \<in> S. w = [v]}"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule equalityI)
      apply(rename_tac n)(*strict*)
      apply(clarsimp)
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      f = "\<lambda>x. [x]"
      in Finite_Set.finite_image_set)
    apply(clarsimp)
    apply(case_tac "finite S")
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    (*finite (S^ = nS) *)
    (*(#S)^(n + 1) = #(S^ = nS) *)
    (*eliminate using some injection *)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      f = "\<lambda>x. (butlast x,[last x])"
      in Finite_Set.finite_imageD)
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "(\<lambda>x. (butlast x,[last x])) ` append_language {w  \<in> kleene_star S. length w = n} (alphabet_to_language S) = {w  \<in> kleene_star S. length w = n} \<times> (alphabet_to_language S)")
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(rule equalityI)
     apply(rename_tac n)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x)(*strict*)
     apply(simp add: alphabet_to_language_def append_language_def)
     apply(clarsimp)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(rule showInImage)
    apply(rule_tac
      x = "a@b"
      in bexI)
     apply(rename_tac a b)(*strict*)
     apply(clarsimp)
     apply(simp add: alphabet_to_language_def)
     apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(simp add: alphabet_to_language_def append_language_def)
    apply(clarsimp)
    apply(rename_tac a v)(*strict*)
    apply(rule_tac
      x = "a"
      in exI)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(simp add: inj_on_def)
   apply(clarsimp)
   apply(rename_tac n x y)(*strict*)
   apply(simp add: alphabet_to_language_def append_language_def)
   apply(clarsimp)
    (*(#S)^(n + 1) = #(S^ = nS) *)
    (*start induction on n*)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "card {w  \<in> kleene_star S. length w \<le> n} = sum ((^) (card S)) {0..n}")
  apply(thin_tac "finite {w  \<in> kleene_star S. length w \<le> n}")
  apply(induct_tac n)
    (*(#S)^(0 + 1) = #(S^ = 0S) *)
    (*(#S)^(na + 1) = #(S^ = na S) *)
    (*do IA*)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      s = "{[]}"
      and t = "{w. w = [] \<and> w  \<in> (kleene_star S)}"
      in ssubst)
    apply(rule equalityI)
     apply(clarsimp)
    apply(clarsimp)
    apply(simp add: kleene_star_def)
   apply(simp add: append_language_def)
    (*(#S) = #((alphabet_to_language S))*)
    (*(#S)^(na + 1) = #(S^ = na S) *)
    (*give bijection*)
   apply(rule_tac
      s = "\<exists>f. bij_betw f S ((alphabet_to_language S))"
      in ssubst)
    apply(rule sym)
    apply(rule Set_Interval.bij_betw_iff_card)
     apply(rule card_ge_0_finite)
     apply(blast)
    (*finite ((alphabet_to_language S))*)
    (*\<exists>f. bij_betw f S ((alphabet_to_language S))*)
    (*(#S)^(na + 1) = #(S^ = na S) *)
    (*give injection*)
    apply(rule_tac
      f = "\<lambda>x. hd x"
      in Finite_Set.finite_imageD)
     apply(rule_tac
      s = "S"
      and t = "hd ` ((alphabet_to_language S))"
      in ssubst)
      apply(simp add: alphabet_to_language_def)
      apply(rule equalityI)
       apply(clarsimp)
      apply(clarsimp)
      apply(rename_tac x)(*strict*)
      apply(rule showInImage)
      apply(clarsimp)
      apply(rule_tac
      x = "[x]"
      in exI)
      apply(clarsimp)
     apply(rule card_ge_0_finite)
     apply(blast)
    apply(simp add: inj_on_def)
    apply(clarsimp)
    apply(rename_tac x y)(*strict*)
    apply(simp add: alphabet_to_language_def)
    apply(clarsimp)
    (*\<exists>f. bij_betw f S ((alphabet_to_language S))*)
    (*(#S)^(na + 1) = #(S^ = na S) *)
    (*continue to give bijection*)
   apply(simp add: bij_betw_def)
   apply(rule_tac
      x = "\<lambda>x. [x]"
      in exI)
   apply(rule conjI)
    apply(simp add: inj_on_def)
   apply(rule_tac
      s = "S"
      and t = "hd ` (alphabet_to_language S)"
      in ssubst)
    apply(simp add: alphabet_to_language_def)
    apply(rule equalityI)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule showInImage)
    apply(clarsimp)
    apply(rule_tac
      x = "[x]"
      in exI)
    apply(clarsimp)
   apply(rule equalityI)
    apply(clarsimp)
    apply(rename_tac xa)(*strict*)
    apply(simp add: alphabet_to_language_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule showInImage)
   apply(simp add: alphabet_to_language_def)
   apply(clarsimp)
    (*(#S)^(na + 1) = #(S^ = na S) *)
    (*unfold ^ on lhs*)
  apply(rename_tac n na)(*strict*)
  apply(simp)
    (*(#S) * (#S)^na = #(S^ = na S) *)
    (*in between there is: #(S\<times>S^ = na S)*)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      s = "card (S \<times> (append_language {w  \<in> kleene_star S. length w = na} ((alphabet_to_language S))))"
      and t = "card S * card (append_language {w  \<in> kleene_star S. length w = na} (alphabet_to_language S))"
      in ssubst)
   apply(rename_tac na)(*strict*)
   apply(rule sym)
   apply(rule Groups_Big.card_cartesian_product)
    (*#(S \<times> (S^ = na S) = #(S^ = na + 1 S) *)
    (*obtain finite (S \<times> (S^ = na S) *)
  apply(rename_tac na)(*strict*)
  apply(subgoal_tac "finite (S \<times> append_language {w  \<in> kleene_star S. length w = na} (alphabet_to_language S))")
   apply(rename_tac na)(*strict*)
   prefer 2
   apply(rule Finite_Set.finite_cartesian_product)
    apply(rename_tac na)(*strict*)
    apply(rule card_ge_0_finite)
    apply(blast)
    (*finite (S^ = na S) *)
    (*#(S \<times> (S^ = na S) = #(S^ = na + 1 S) *)
    (*from Induction Hypothesis*)
   apply(rename_tac na)(*strict*)
   apply(rule card_ge_0_finite)
   apply(rule_tac
      y = "card S * card S ^ na"
      in less_le_trans)
    apply(rename_tac na)(*strict*)
    apply(rule trivMult)
    apply(simp)
   apply(rename_tac na)(*strict*)
   apply(simp)
    (*#(S \<times> (S^ = na S) = #(S^ = na + 1 S) *)
    (*give a bijection*)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      s = "\<exists>f. bij_betw f (S \<times> append_language {w  \<in> kleene_star S. length w = na} (alphabet_to_language S)) (append_language {w  \<in> kleene_star S. length w = Suc na} (alphabet_to_language S))"
      in ssubst)
   apply(rename_tac na)(*strict*)
   apply(rule sym)
   apply(rule Set_Interval.bij_betw_iff_card)
    apply(rename_tac na)(*strict*)
    apply(simp)
   apply(rename_tac na)(*strict*)
   defer
    (*\<exists>f. bij_betw (S \<times> (S^ = na S)) (S^ = na + 1 S) *)
    (*finite (S^ = na + 1 S) *)
    (*show is bijection*)
   apply(rename_tac na)(*strict*)
   apply(simp add: bij_betw_def)
   apply(rule_tac
      x = "\<lambda>x. (snd x)@[fst x]"
      in exI)
   apply(rule conjI)
    apply(rename_tac na)(*strict*)
    apply(simp add: inj_on_def)
   apply(rename_tac na)(*strict*)
   apply(rule equalityI)
    apply(rename_tac na)(*strict*)
    apply(clarsimp)
    apply(rename_tac na a b)(*strict*)
    apply(simp add: kleene_star_def alphabet_to_language_def append_language_def)
    apply(clarsimp)
    apply(rename_tac a aa v)(*strict*)
    apply(rule_tac
      x = "aa@[v]"
      in exI)
    apply(clarsimp)
   apply(rename_tac na)(*strict*)
   apply(clarsimp)
   apply(rename_tac na x)(*strict*)
   apply(rule showInImage)
   apply(clarsimp)
   apply(simp add: kleene_star_def alphabet_to_language_def append_language_def)
   apply(clarsimp)
   apply(rename_tac na a v)(*strict*)
   apply(rule_tac
      x = "butlast a"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac na a v)(*strict*)
    apply(rule_tac
      B = "set a"
      in subset_trans)
     apply(rename_tac na a v)(*strict*)
     apply(rule trivButLast)
    apply(rename_tac na a v)(*strict*)
    apply(clarsimp)
   apply(rename_tac na a v)(*strict*)
   apply(rule_tac
      x = "[last a]"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac na a v)(*strict*)
    apply(rule_tac
      A = "set a"
      in set_mp)
     apply(rename_tac na a v)(*strict*)
     apply(simp add: kleene_star_def)
    apply(rename_tac na a v)(*strict*)
    apply(rule last_in_set)
    apply(clarsimp)
   apply(rename_tac na a v)(*strict*)
   apply(subgoal_tac "\<exists>xp xa. a = xp @ [xa]")
    apply(rename_tac na a v)(*strict*)
    apply(clarsimp)
   apply(rename_tac na a v)(*strict*)
   apply(rule existenceOfLast)
   apply(clarsimp)
    (*finite (S^ = na + 1 S) *)
    (*from product finite (S\<times> (S^ = na S))*)
  apply(rename_tac na)(*strict*)
  apply(subgoal_tac "finite (S \<times> append_language {w  \<in> kleene_star S. length w = na} (alphabet_to_language S))")
   apply(rename_tac na)(*strict*)
   apply(rule_tac
      f = "\<lambda>x. (last x,butlast x)"
      in Finite_Set.finite_imageD)
    apply(rename_tac na)(*strict*)
    apply(rule_tac
      s = "(S \<times> (append_language {w  \<in> kleene_star S. length w = na} (alphabet_to_language S)))"
      and t = "((\<lambda>x. (last x, butlast x)) ` append_language {w  \<in> kleene_star S. length w = Suc na} (alphabet_to_language S))"
      in ssubst)
     apply(rename_tac na)(*strict*)
     apply(rule equalityI)
      apply(rename_tac na)(*strict*)
      apply(clarsimp)
      apply(rename_tac na x)(*strict*)
      apply(simp add: append_language_def alphabet_to_language_def kleene_star_def)
      apply(clarsimp)
      apply(rename_tac na a v)(*strict*)
      apply(rule_tac
      x = "butlast a"
      in exI)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac na a v)(*strict*)
       apply(rule_tac
      B = "set a"
      in subset_trans)
        apply(rename_tac na a v)(*strict*)
        apply(rule trivButLast)
       apply(rename_tac na a v)(*strict*)
       apply(clarsimp)
      apply(rename_tac na a v)(*strict*)
      apply(rule_tac
      x = "[last a]"
      in exI)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac na a v)(*strict*)
       apply(rule_tac
      A = "set a"
      in set_mp)
        apply(rename_tac na a v)(*strict*)
        apply(simp add: kleene_star_def)
       apply(rename_tac na a v)(*strict*)
       apply(rule last_in_set)
       apply(clarsimp)
      apply(rename_tac na a v)(*strict*)
      apply(subgoal_tac "\<exists>xp xa. a = xp @ [xa]")
       apply(rename_tac na a v)(*strict*)
       apply(clarsimp)
      apply(rename_tac na a v)(*strict*)
      apply(rule existenceOfLast)
      apply(clarsimp)
     apply(rename_tac na)(*strict*)
     apply(clarsimp)
     apply(rename_tac na a b)(*strict*)
     apply(rule showInImage)
     apply(simp add: alphabet_to_language_def append_language_def kleene_star_def)
     apply(clarsimp)
     apply(rename_tac a aa v)(*strict*)
     apply(rule_tac
      x = "aa@[v]@[a]"
      in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac a aa v)(*strict*)
      apply(rule_tac
      x = "aa@[v]"
      in exI)
      apply(clarsimp)
     apply(rename_tac a aa v)(*strict*)
     apply(rule butLastSimp)
    apply(rename_tac na)(*strict*)
    apply(clarsimp)
   apply(rename_tac na)(*strict*)
   apply(simp add: inj_on_def)
   apply(clarsimp)
   apply(rename_tac na x y)(*strict*)
   apply(simp add: alphabet_to_language_def append_language_def kleene_star_def)
   apply(clarsimp)
  apply(rename_tac na)(*strict*)
  apply(simp)
  done

theorem numberOfWordsUpToLength: "
  finite S
  \<Longrightarrow> card {w. w \<in> kleene_star S \<and> length w \<le> n} = (\<Sum>i = 0..n. (card S)^i)"
  apply(case_tac "card S > 0")
   apply(rule numberOfWordsUpToLength2)
   apply(clarsimp)
  apply(case_tac "S = {}")
   apply(rule_tac
      s = "{}"
      and t = "S"
      in ssubst)
    apply(simp)
   apply(rule numberOfWordsUpToLength1)
  apply(clarsimp)
  done

theorem wordsUpToLengthFinite: "
  finite S
  \<Longrightarrow> finite {w. w \<in> kleene_star S \<and> length w \<le> n}"
  apply(case_tac "S = {}")
   apply(clarsimp)
   apply(simp add: kleene_star_def)
  apply(rule card_ge_0_finite)
  apply(rule_tac
      s = "(\<Sum>i = 0..n. (card S)^i)"
      in ssubst)
   apply(rule numberOfWordsUpToLength)
   apply(clarsimp)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "0"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(arith)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma set_take_subset2: "
  set w \<subseteq> A
  \<Longrightarrow> set(take n w) \<subseteq> A"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w n x)(*strict*)
  apply(case_tac n)
   apply(rename_tac a w n x)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n x nat)(*strict*)
  apply(force)
  done

lemma wordsUpToLengthFinite2: "
  finite S
  \<Longrightarrow> finite {take k w | w. set w \<subseteq> S}"
  apply(rule_tac
      s="{w. w \<in> kleene_star S \<and> length w\<le>k}"
      and t="{take k w | w. set w \<subseteq> S}"
      in ssubst)
   apply(simp add: kleene_star_def)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(rule_tac A="set (take k w)" in set_mp)
     apply(rename_tac w x)(*strict*)
     apply(rule set_take_subset2)
     apply(blast)
    apply(rename_tac w x)(*strict*)
    apply(force)
   apply(force)
  apply(rule wordsUpToLengthFinite)
  apply(force)
  done

lemma wordsOfLangUpToLengthFinite: "
  finite S
  \<Longrightarrow> A\<subseteq>kleene_star S
  \<Longrightarrow> finite {w \<in> A. length w \<le> n}"
  apply(rule_tac
      B = "{w. w \<in> kleene_star S \<and> length w \<le> n}"
      in Finite_Set.finite_subset)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule set_mp)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(rule wordsUpToLengthFinite)
  apply(blast)
  done

lemma prefixAndNotStrictPrefixIsEQI: "
  w' \<sqsubseteq> (v @ [s])
  \<Longrightarrow> \<not> w' \<sqsubseteq> v
  \<Longrightarrow> w' = v @ [s]"
  apply(rule mutual_prefix_implies_equality)
   apply(simp)
  apply(simp only: prefix_def)
  apply(erule exE)
  apply(rename_tac c)(*strict*)
  apply(fold prefix_def)
  apply(subgoal_tac "((v @ [s]) \<sqsubseteq> w') \<or> (w' \<sqsubseteq> (v@[s]))")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule_tac
      a = "v@[s]"
      and b = "[]"
      and c = "w'"
      and d = "c"
      in mutual_prefix_prefix)
   apply(simp)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  apply(erule_tac exE)
  apply(rename_tac c ca)(*strict*)
  apply(case_tac "ca")
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ca a list)(*strict*)
  apply(auto)
  apply(rename_tac c a list)(*strict*)
  apply(subgoal_tac "\<exists>ca'. ca'@[s] = a#list")
   apply(rename_tac c a list)(*strict*)
   apply(erule exE)
   apply(rename_tac c a list ca')(*strict*)
   apply(erule_tac
      x = "ca'"
      in allE)
   apply(rule_tac
      a = "w'@ca'"
      and s = "s"
      and b = "v"
      in shorterEQ)
    apply(rename_tac c a list ca')(*strict*)
    apply(clarsimp) +
  apply(rename_tac c a list)(*strict*)
  apply(rule_tac
      b = "a"
      and c = "list"
      and a = "w'"
      and d = "v"
      in dropLast)
  apply(clarsimp)
  done

lemma prefixSubsetnonblockingness_language: "
  A\<subseteq>B
  \<Longrightarrow> A\<subseteq>C
  \<Longrightarrow> x \<in> A
  \<Longrightarrow> x \<in> prefix_closure(B\<inter>C)"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefixSubsetnonblockingness_language2: "
  A\<subseteq>prefix_closure(B\<inter>A)
  \<Longrightarrow> A\<subseteq>C
  \<Longrightarrow> A\<subseteq> prefix_closure(B\<inter>C)"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> prefix_closure(B\<inter>A)")
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(auto)
  done

lemma prefixAlsoIn: "
  A = prefix_closure A
  \<Longrightarrow> w \<in> A
  \<Longrightarrow> prefix v w
  \<Longrightarrow> v \<in> A"
  apply(simp add: prefix_closure_def prefix_def)
  apply(auto)
  done

lemma prefixSubsetnonblockingness_language3: "
  A\<subseteq>prefix_closure(B\<inter>A)
  \<Longrightarrow> A\<subseteq>C
  \<Longrightarrow> A\<subseteq> prefix_closure(B\<inter>(A\<inter>C))"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> prefix_closure(B\<inter>A)")
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(auto)
  done

lemma prefixSubsetnonblockingness_language4: "
  Ba \<subseteq> (prefix_closure B)
  \<Longrightarrow> Ba\<subseteq>C
  \<Longrightarrow> C = prefix_closureC
  \<Longrightarrow> C\<subseteq>B
  \<Longrightarrow> (Ba \<subseteq> (prefix_closure (B \<inter> C)))"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> prefix_closure B")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x \<in> prefix_closureC")
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(auto)
  done

lemma tmp00xx: "
  card (prefix_closure{w}) = Suc (length w)"
  apply(rule rev_induct)
   apply(simp)
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac x xs)(*strict*)
  apply(rule_tac
      P = "\<lambda>y. (card y = Suc(length (xs@[x])))"
      and t = "prefix_closure{xs@[x]}"
      and s = "(prefix_closure{xs})\<union>{xs@[x]}"
      in ssubst)
   apply(rename_tac x xs)(*strict*)
   apply(rule prefix_closureDecomp)
  apply(rename_tac x xs)(*strict*)
  apply(simp)
  apply(rule_tac
      P = "\<lambda>y. (y = Suc (Suc (length xs)))"
      and s = "Suc(card (prefix_closure{xs}))"
      in ssubst)
   apply(rename_tac x xs)(*strict*)
   apply(rule Finite_Set.card_insert_disjoint)
    apply(rename_tac x xs)(*strict*)
    prefer 2
    apply(simp add: prefix_closure_def prefix_def)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(simp)
  apply(rename_tac x xs)(*strict*)
  apply(simp add: card_def)
  apply(rename_tac xs)(*strict*)
  apply(case_tac "finite (prefix_closure{xs})")
   apply(rename_tac xs)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs)(*strict*)
  apply(metis card_def card_infinite old.nat.distinct(2))
  done

definition kPrefix :: "
  nat
  \<Rightarrow> '\<Sigma> list
  \<Rightarrow> '\<Sigma> list"
  where
    "kPrefix k w =
  take k w"

lemma set_kPrefix_subset: "
  set w \<subseteq> A
  \<Longrightarrow> set (kPrefix n w) \<subseteq> A"
  apply(simp add: kPrefix_def)
  apply (metis set_take_subset subset_trans)
  done

lemma kPrefix_in_set: "
  X  \<in> A
  \<Longrightarrow> set wb \<subseteq> A - {X}
  \<Longrightarrow> set (kPrefix k (wb @ [X])) \<subseteq> A"
  apply(simp add: kPrefix_def)
  apply(rule conjI)
   apply(rule_tac
      B = "set wb"
      in subset_trans)
    apply(rule set_take_subset)
   apply(force)
  apply(case_tac "k - length wb")
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma kPrefix_Shorter: "
  kPrefix k w = w
  \<Longrightarrow> length w \<le> k"
  apply(simp add: kPrefix_def)
  apply(rule_tac
      t = "w"
      and s = "take k w"
      in ssubst)
   apply(force)
  apply(rule takeShorter)
  done

lemma kPrefix_append: "
  kPrefix k (w@v) = kPrefix k (w @ (kPrefix k v))"
  apply(simp add: kPrefix_def)
  apply(induct v arbitrary: w)
   apply(rename_tac w)(*strict*)
   apply(auto)
  apply(rename_tac a v w)(*strict*)
  apply(rule_tac
      t = "ord_class.min (k - length w) k"
      and s = "k - length w"
      in ssubst)
   apply(rename_tac a v w)(*strict*)
   apply(auto)
  done

lemma kPrefix_append2: "
  kPrefix k (w@v) = kPrefix k ((kPrefix k w)@v)"
  apply(simp add: kPrefix_def)
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(auto)
  apply(rename_tac w v)(*strict*)
  apply(case_tac "Suc(length w) \<le> k")
   apply(rename_tac w v)(*strict*)
   apply(auto)
  apply(rename_tac w v)(*strict*)
  apply(rule_tac
      t = "ord_class.min (Suc (length w)) k"
      and s = "Suc (length w)"
      in ssubst)
   apply(rename_tac w v)(*strict*)
   apply(auto)
  done

lemma kPrefix_idemp: "
  kPrefix k (kPrefix k v) = kPrefix k v"
  apply(induct v)
   apply(simp add: kPrefix_def) +
  done

primrec suffixes :: "
  'a list
  \<Rightarrow> 'a list set"
  where
    "suffixes [] = {[]}"
  | "suffixes (x # w) = {x # w} \<union> suffixes w"

lemma suffixes_intro1: "
  v  \<in> suffixes (w @ v)"
  apply(induct_tac w)
   apply(auto)
  apply(induct_tac v)
   apply(auto)
  done

lemma suffixes_intro2: "
  w  \<in> suffixes w"
  apply(induct_tac w)
   apply(auto)
  done

lemma suffixes_contra1: "
  a # w  \<in> suffixes v
  \<Longrightarrow> w \<notin> suffixes v
  \<Longrightarrow> P"
  apply(subgoal_tac "a # w  \<in> suffixes v \<longrightarrow> w \<notin> suffixes v \<longrightarrow> P")
   apply(clarsimp)
  apply(thin_tac "a # w  \<in> suffixes v")
  apply(thin_tac "w \<notin> suffixes v")
  apply(induct_tac v)
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(auto)
  apply(subgoal_tac "w  \<in> suffixes w")
   apply(blast)
  apply(rule suffixes_intro2)
  done

lemma suffixes_intro2_prime: "
  []  \<in> suffixes x"
  apply(induct_tac x)
   apply(simp add: suffixes_def)
  apply(rename_tac a list)(*strict*)
  apply(simp add: suffixes_def)
  done

lemma suffixes_intro2_rev: "
  w  \<in> suffixes v
  \<Longrightarrow> \<exists>x. x @ w = v"
  apply(subgoal_tac " w  \<in> suffixes v \<longrightarrow> (\<exists>x. x @ w = v)")
   apply(blast)
  apply(rule_tac list.induct)
   apply(auto)
  done

lemma suffixes_finite: "
  finite (suffixes w)"
  apply(rule list.induct)
   apply(auto)
  done

primrec insertMultiple :: "'\<Sigma> list list \<Rightarrow> '\<Sigma> list \<Rightarrow> '\<Sigma> list" where
  "insertMultiple W [] = (case W of [] \<Rightarrow> [] | v#V \<Rightarrow> v)"
| "insertMultiple W (a#w) = (case W of [] \<Rightarrow> a#w | v#V \<Rightarrow> a#v@(insertMultiple V w))"

primrec filterMultiple :: "nat set \<Rightarrow> nat \<Rightarrow> '\<Sigma> list \<Rightarrow> '\<Sigma> list" where
  "filterMultiple M n [] = []"
| "filterMultiple M n (a#w) = (if n \<in> M then [a] else [])@(filterMultiple M (Suc n) w)"

lemma insertMultiple_end: "
  insertMultiple [] w = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma insertMultiple_append1: "
  \<exists>M1 M2 m. \<forall>b. M = M1@(if m \<noteq> [] then [m] else [])@M2 \<and> insertMultiple M (a@b) = (insertMultiple M1 a)@m@(insertMultiple M2 b)"
  apply(induct a arbitrary: M)
   apply(rename_tac M)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x = "M"
      in exI)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(force)
  apply(rename_tac a1 a2 M)(*strict*)
  apply(case_tac M)
   apply(rename_tac a1 a2 M)(*strict*)
   apply(clarsimp)
   apply(rename_tac a2 b)(*strict*)
   apply(rule sym)
   apply(rule insertMultiple_end)
  apply(rename_tac a1 a2 M a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a1 a2 a list)(*strict*)
  apply(erule_tac
      x = "list"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac a1 a2 a M1 M2 m)(*strict*)
  apply(rule conjI)
   apply(rename_tac a1 a2 a M1 M2 m)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rename_tac a1 a2 a M1 M2)(*strict*)
   apply(rule_tac
      x = "a#M1"
      in exI)
   apply(clarsimp)
   apply(rename_tac a2 M1 M2)(*strict*)
   apply(rule_tac
      x = "M2"
      in exI)
   apply(clarsimp)
  apply(rename_tac a1 a2 a M1 M2 m)(*strict*)
  apply(rule_tac
      x = "a#M1"
      in exI)
  apply(clarsimp)
  apply(rename_tac a2 M1 M2 m)(*strict*)
  apply(rule_tac
      x = "M2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x = "m"
      in exI)
  apply(clarsimp)
  done

definition butn :: "'\<Sigma> list \<Rightarrow> nat \<Rightarrow> '\<Sigma> list" where
  "butn w n = take (length w - n) w"

lemma butn_prefix_closureise: "
  butn (w@v) (length v) = w"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(simp add: butn_def)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  done

lemma butn_empty: "
  length w \<le> n
  \<Longrightarrow> butn w n = []"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: butn_def)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  done

lemma butn_empty_prime: "
  butn w n = []
  \<Longrightarrow> length w \<le> n"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(simp add: butn_def)
  done

lemma butn_empty_prime_prime: "
  butn w (length w) = []"
  apply(simp add: butn_def)
  done

lemma set_butn_subset: "
  set (butn w n) \<subseteq> set w"
  apply(simp add: butn_def)
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(rule set_take_subset)
  done

lemma set_butn_subset_prime: "
  set w \<subseteq> A
  \<Longrightarrow> set (butn w n) \<subseteq> A"
  apply (metis set_butn_subset subset_trans)
  done

lemma butn_shift: "
  length v \<ge> n
  \<Longrightarrow> butn (w@v) n = w @ (butn v n)"
  apply(simp add: butn_def)
  done

lemma butn_take: "
  length w \<ge> n
  \<Longrightarrow> butn w (length w - n) = take n w"
  apply(simp add: butn_def)
  done

lemma butn_drop_prime: "
  butn (w@v@[a]) (Suc(length v)) = w"
  apply(simp add: butn_def)
  done

lemma take_butn: "
  n + m \<le> length w
  \<Longrightarrow> take n (butn w m) = take n w"
  apply(simp add: butn_def)
  apply(case_tac "n \<le> length w - m")
   apply(rule_tac
      t = "min n (length w - m)"
      and s = "n"
      in ssubst)
    apply(force)
   apply(force)
  apply(rule_tac
      t = "min n (length w - m)"
      and s = "length w - m"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma take_butn_prime: "
  length w \<ge> n + m
  \<Longrightarrow> take n w = take n (butn w m)"
  apply(induct w arbitrary: n m)
   apply(rename_tac n m)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n m)(*strict*)
  apply(case_tac n)
   apply(rename_tac a w n m)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n m nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w m nat)(*strict*)
  apply(simp add: butn_def)
  apply(case_tac "nat \<le> (length w - m)")
   apply(rename_tac a w m nat)(*strict*)
   apply(rule_tac
      t = "min nat (length w - m)"
      and s = "nat"
      in ssubst)
    apply(rename_tac a w m nat)(*strict*)
    apply(force)
   apply(rename_tac a w m nat)(*strict*)
   apply(rule_tac
      t = "min (Suc nat) (Suc (length w) - m)"
      and s = "Suc nat"
      in ssubst)
    apply(rename_tac a w m nat)(*strict*)
    apply(force)
   apply(rename_tac a w m nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w m nat)(*strict*)
  apply(force)
  done

lemma butn_length: "
  length (butn w n) = length w - n"
  apply(simp add: butn_def)
  done

lemma butn_zero: "
  butn w 0 = w"
  apply(simp add: butn_def)
  done

lemma butn_drop: "
  length v \<le> n
  \<Longrightarrow> butn (w@v) n = (butn w (n - length v))"
  apply(simp add: butn_def)
  done

definition right_quotient_word :: "'\<Sigma> list \<Rightarrow> '\<Sigma> list \<Rightarrow> '\<Sigma> list option" where
  "right_quotient_word w1 w2 \<equiv> (if \<exists>v. w1 = v@w2 then Some (THE v. w1 = v@w2) else None)"

lemma right_quotient_word_neutral: "
  (\<forall>s. right_quotient_word s [] = Some s)"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_neutral_prime: "
  (\<forall>s. (\<exists>s'. right_quotient_word [] s = Some s') \<longrightarrow> s = [])"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_neutral_prime_prime: "
  (\<forall>s. right_quotient_word [] s = None \<longrightarrow> s \<noteq> [])"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_full: "
  (\<forall>s. right_quotient_word s s = Some [])"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_removes_right_addition_hlp: "
  right_quotient_word (s @ s') s' = Some s"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_removes_right_addition: "
  (\<forall>s s'. right_quotient_word (s @ s') s' = Some s)"
  apply(simp add: right_quotient_word_def)
  done

lemma right_quotient_word_drop: "
  right_quotient_word w (drop n w) = Some (take n w)"
  apply (metis right_quotient_word_removes_right_addition append_take_drop_id)
  done

lemma right_quotient_word_Some_by_append: "
  w = x@v
  \<Longrightarrow> right_quotient_word w v = Some x"
  apply(simp add: right_quotient_word_def)
  done

definition left_quotient_word :: "'\<Sigma> list \<Rightarrow> '\<Sigma> list \<Rightarrow> '\<Sigma> list option" where
  "left_quotient_word w1 w2 = (if \<exists>v. w2 = w1@v then Some (THE v. w2 = w1@v) else None)"

lemma left_quotient_word_neutral: "
  (\<forall>s. left_quotient_word [] s = Some s)"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_neutral_prime: "
  (\<forall>s. (\<exists>s'. left_quotient_word s [] = Some s') \<longrightarrow> s = [])"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_neutral_prime_prime: "
  (\<forall>s. left_quotient_word s [] = None \<longrightarrow> s \<noteq> [])"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_full: "
  (\<forall>s. left_quotient_word s s = Some [])"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_removes_right_addition_hlp: "
  left_quotient_word s' (s' @ s) = Some s"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_removes_right_addition: "
  (\<forall>s s'. left_quotient_word s' (s' @ s) = Some s)"
  apply(simp add: left_quotient_word_def)
  done

lemma left_quotient_word_drop: "
  left_quotient_word (take n w) w = Some (drop n w)"
  apply (metis left_quotient_word_removes_right_addition append_take_drop_id)
  done

lemma left_quotient_word_Some_by_append: "
  w@x = v
  \<Longrightarrow> left_quotient_word w v = Some x"
  apply(simp add: prefix_def left_quotient_word_def)
  apply(clarsimp)
  done

lemma example: "
  U = {u}
  \<Longrightarrow> X = {[],[u]}
  \<Longrightarrow> L = {[],[u],[u,u]}
  \<Longrightarrow> [] \<notin> {w. w  \<in> X \<and> (\<forall>w'. prefix w' w \<longrightarrow> (\<not>(\<exists>x. set x \<subseteq> U \<and> w'@x  \<in> L - prefix_closure X)))} \<and> []  \<in> {w. w  \<in> X \<and> (\<forall>w'. prefix w' w \<longrightarrow> (\<not>(\<exists>x \<in> U. w'@[x]  \<in> L - prefix_closure X)))}"
  apply(rule conjI)
   apply(clarsimp)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(rule_tac
      x = "[u,u]"
      in exI)
   apply(clarsimp)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(erule_tac
      x = "[u]"
      in allE)
  apply(clarsimp)
  done

definition butlast_if_match :: "'\<Sigma> list \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma> list" where
  "butlast_if_match w s \<equiv> case w of [] \<Rightarrow> [] | x#y \<Rightarrow> if last w = s then butlast w else w"

lemma butlast_if_match_direct: "
  v@[x] = w
  \<Longrightarrow> butlast_if_match w x = v"
  apply(simp add: butlast_if_match_def)
  apply(clarsimp)
  apply(case_tac "v@[x]")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case v @ [x] of [] \<Rightarrow> [] | xa # y \<Rightarrow> butlast (v @ [x])"
      and s = " butlast (v @ [x])"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(simp (no_asm))
  done

lemma butlast_if_match_direct2: "
  v@[y] = w
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> butlast_if_match w x = w"
  apply(simp add: butlast_if_match_def)
  apply(clarsimp)
  apply(case_tac "v@[y]")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case v @ [y] of [] \<Rightarrow> [] | x # ya \<Rightarrow> v @ [y]"
      and s = " v @ [y]"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(simp (no_asm))
  done

lemma butlast_if_match_direct2_prime: "
  x\<notin>set w
  \<Longrightarrow> butlast_if_match w x = w"
  apply(simp add: butlast_if_match_def)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | x # y \<Rightarrow> butlast w"
      and s = "butlast w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | x # y \<Rightarrow> w"
      and s = "w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma set_butlast_if_match_is_subset: "
  set (butlast_if_match w x) \<subseteq> set w"
  apply(unfold butlast_if_match_def)
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | xa # y \<Rightarrow> if last w = x then butlast w else w"
      and s = "if last w = x then butlast w else w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w = a#list")
  apply(clarsimp)
  done

lemma butlast_only_tail_contra: "
  x  \<in> set (butlast (kPrefix k (wb @ [x])))
  \<Longrightarrow> x \<notin> set wb
  \<Longrightarrow> P"
  apply (metis List.butlast_append ListMem_iff append_take_drop_id butlast_snoc in_set_butlastD kPrefix_def set_append_contra1)
  done

lemma butlast_if_match_length_le: "
  length (butlast_if_match w x) \<le> length w"
  apply(unfold butlast_if_match_def)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | xa # y \<Rightarrow> if last w = x then butlast w else w"
      and s = "if last w = x then butlast w else w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w = a#list")
  apply(clarsimp)
  done

lemma drop_butlast_if_match_distrib: "
  drop (length w) (butlast_if_match (w @ v) X) = butlast_if_match v X"
  apply(unfold butlast_if_match_def)
  apply(case_tac "w@v")
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w @ v of [] \<Rightarrow> [] | x # y \<Rightarrow> if last (w @ v) = X then butlast (w @ v) else w @ v"
      and s = "if last (w @ v) = X then butlast (w @ v) else w @ v"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(case_tac v)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list aa lista)(*strict*)
  apply(rule_tac
      t = "case v of [] \<Rightarrow> [] | x # y \<Rightarrow> if last v = X then butlast v else v"
      and s = "if last v = X then butlast v else v"
      in ssubst)
   apply(rename_tac a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac a list aa lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w@v = w' @ [x']")
   apply(rename_tac a list aa lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list aa lista)(*strict*)
  apply(thin_tac "w@v = a#list")
  apply(subgoal_tac "\<exists>w' x'. v = w' @ [x']")
   apply(rename_tac a list aa lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list aa lista)(*strict*)
  apply(thin_tac "v = aa#lista")
  apply(clarsimp)
  apply(rename_tac w'\<Sigma>)(*strict*)
  apply(rule_tac
      t = "w @ w'\<Sigma> @ [X]"
      and s = "(w @ w'\<Sigma>) @ [X]"
      in ssubst)
   apply(rename_tac w'\<Sigma>)(*strict*)
   apply(force)
  apply(rename_tac w'\<Sigma>)(*strict*)
  apply(rule_tac
      t = "butlast ((w @ w'\<Sigma>) @ [X])"
      and s = "w@w'\<Sigma>"
      in ssubst)
   apply(rename_tac w'\<Sigma>)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac w'\<Sigma>)(*strict*)
  apply(clarsimp)
  done

lemma butlast_if_match_prefix: "
  prefix (butlast_if_match w x) w"
  apply(simp add: prefix_def butlast_if_match_def)
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | x # y \<Rightarrow> butlast w"
      and s = "butlast w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t = "case w of [] \<Rightarrow> [] | x # y \<Rightarrow> w"
      and s = "w"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w = a#list")
  apply(clarsimp)
  done

lemma butlast_if_match_reduces: "
  butlast_if_match w x \<noteq> w
  \<Longrightarrow> \<exists>X. X@[x] = w"
  apply(simp add: butlast_if_match_def)
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "(if last w = x then butlast w else w) \<noteq> w")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "(case w of [] \<Rightarrow> [] | xa # y \<Rightarrow> if last w = x then butlast w else w) \<noteq> w")
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w = a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(case_tac "x' = x")
   apply(rename_tac w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(clarsimp)
  done

lemma drop_entire_butlast_if_match: "
  length w \<le> n
  \<Longrightarrow> drop n (butlast_if_match w x) = []"
  apply (metis butlast_if_match_length_le drop_eq_Nil le_trans)
  done

lemma butlast_if_match_pull_out: "
  w \<noteq> []
  \<Longrightarrow> butlast_if_match (v@w) x = v @ butlast_if_match w x"
  apply (metis List.last_append append_assoc butlast_if_match_direct butlast_if_match_reduces butlast_snoc_2 last_snoc rev_cases snoc_eq_iff_butlast)
  done

lemma butlast_if_match_pull_out_prime: "
  x \<notin> set w
  \<Longrightarrow> s = w@v
  \<Longrightarrow> w @ butlast_if_match v x = butlast_if_match s x"
  apply (metis butlast_if_match_direct2_prime butlast_if_match_pull_out in_set_takeD self_append_conv take_0)
  done

lemma butlast_if_match_take: "
  \<exists>w'. w = w'@[x] \<and> x \<notin> set w'
  \<Longrightarrow> butlast_if_match (take n w) x = take n (butlast w)"
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(case_tac "n - length w'")
   apply(rename_tac w')(*strict*)
   apply(clarsimp)
   apply (metis butlast_if_match_direct2_prime in_set_takeD)
  apply(rename_tac w' nat)(*strict*)
  apply(clarsimp)
  apply (metis butlast_if_match_direct)
  done

lemma butlast_if_match_preserves_prefix: "
  prefix w v
  \<Longrightarrow> prefix (butlast_if_match w x) (butlast_if_match v x)"
  apply (metis append_self_conv butlast_if_match_prefix butlast_if_match_pull_out prefix_reflexive prefix_transitive prefix_def)
  done

lemma equal_suffix_removal1: "
  suffix w1 [X]
  \<Longrightarrow> suffix w2 [X]
  \<Longrightarrow> butlast_if_match w1 X = butlast_if_match w2 X
  \<Longrightarrow> w1 = w2"
  apply (metis butlast_if_match_direct butlast_snoc suffix_def)
  done

definition may_terminated_by :: "'\<Sigma> set \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma> list set" where
  "may_terminated_by A x = append_language (kleene_star (A - {x})) {[x],[]}"

definition must_terminated_by :: "'\<Sigma> set \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma> list set" where
  "must_terminated_by A x = append_language (kleene_star (A - {x})) {[x]}"

definition not_terminated_by :: "'\<Sigma> set \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma> list set" where
  "not_terminated_by A x = kleene_star (A - {x})"

lemma may_terminated_by_decompose2: "
  a  \<in> set w
  \<Longrightarrow> w  \<in> may_terminated_by A X
  \<Longrightarrow> X  \<in> A
  \<Longrightarrow> a  \<in> A"
  apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac aa)(*strict*)
  apply(force)
  done

definition ssuffix :: "'\<Sigma> list \<Rightarrow> '\<Sigma> list \<Rightarrow> bool" where
  "ssuffix w v = (\<exists>x. w = x@v \<and> x \<noteq> [])"

lemma suffix_last_eq: "
  suffix w1 w2 \<or> suffix w2 w1
  \<Longrightarrow> w1 \<noteq> []
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> last w1 = last w2"
  apply(case_tac w2)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w2 = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w2 = a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(case_tac w1)
   apply(rename_tac w' x')(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w1 = w' @ [x']")
   apply(rename_tac w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "w1 = a#list")
  apply(clarsimp)
  apply(rename_tac w' x' w'\<Sigma> x'\<Sigma>)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' x' w'\<Sigma> x'\<Sigma>)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac w' x' w'\<Sigma> x'\<Sigma>)(*strict*)
  apply(simp add: suffix_def)
  done

lemma may_terminated_by_decompose: "
  w  \<in> may_terminated_by A X
  \<Longrightarrow> w = v1 @ v2 @ v3
  \<Longrightarrow> v2  \<in> may_terminated_by A X"
  apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(case_tac v3)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(case_tac "v2")
     apply(rename_tac a)(*strict*)
     apply(clarsimp)
    apply(rename_tac a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. v2 = w' @ [x']")
     apply(rename_tac a aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac a aa list)(*strict*)
    apply(thin_tac "v2= aa # list")
    apply(clarsimp)
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. v3 = w' @ [x']")
    apply(rename_tac a aa list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac a aa list)(*strict*)
   apply(thin_tac "v3= aa # list")
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

lemma may_terminated_by_decompose4: "
  w  \<in> may_terminated_by A X
  \<Longrightarrow> Suc n < length w
  \<Longrightarrow> w ! n  \<in> A - {X}"
  apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(a@[X])!n"
      and s="a!n"
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma take_complex: "
  dhn \<le> k
  \<Longrightarrow> Suc (length wb) - dhn \<le> Suc (wa + length wb) - dhi
  \<Longrightarrow> take (dhi - wa) wb = take (dhi - wa) (butn wb (length wb - k))"
  apply(simp add: butn_def)
  apply(case_tac "dhi - wa \<le> length wb - (length wb - k)")
   apply(rule_tac
      t = "(min (dhi - wa) (length wb - (length wb - k)))"
      and s = "dhi - wa"
      in ssubst)
    apply(rule Orderings.min_absorb1)
    apply(force)
   apply(force)
  apply(rule_tac
      t = "min (dhi - wa) (length wb - (length wb - k))"
      and s = "(length wb - (length wb - k))"
      in ssubst)
   apply(rule Orderings.min_absorb2)
   apply(force)
  apply(case_tac "dhi - wa")
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma mutual_prefix_implies_mutual_length: "
  length w \<ge> length v
  \<Longrightarrow> w@a = v@b
  \<Longrightarrow> length a \<le> length b"
  apply(subgoal_tac "prefix w v \<or> prefix v w")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(force)
  apply(simp add: prefix_def)
  apply(force)
  done

lemma length_append_equal: "
  length w1 = length w2
  \<Longrightarrow> w1@v1 = w2@v2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "(prefix w1 w2) \<or> (prefix w2 w1)")
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma suffix_closure_finite: "
  finite (suffix_closure {x})"
  apply(induct x)
   apply(simp add: suffix_closure_def suffix_def)
  apply(rename_tac a x)(*strict*)
  apply(rule_tac
      t="suffix_closure {a#x}"
      and s="{a#x}\<union>(suffix_closure {x})"
      in ssubst)
   apply(rename_tac a x)(*strict*)
   apply(simp add: suffix_closure_def suffix_def)
   apply(rule order_antisym)
    apply(rename_tac a x)(*strict*)
    apply(clarsimp)
    apply(rename_tac a x xa c)(*strict*)
    apply(case_tac c)
     apply(rename_tac a x xa c)(*strict*)
     apply(force)
    apply(rename_tac a x xa c aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a x)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x)(*strict*)
  apply(clarsimp)
  done

lemma right_quotient_hlp1: "
  suffix z2 w
  \<Longrightarrow> the(right_quotient_word z2 w) = x
  \<Longrightarrow> w=v
  \<Longrightarrow> the (right_quotient_word (a # z2) v)= a # x"
  apply(clarsimp)
  apply(simp add: right_quotient_word_def)
  apply(simp add: suffix_def)
  apply(clarsimp)
  done

lemma prefix_to_suffix: "
  (prefix a b) \<longleftrightarrow> (suffix (rev b) (rev a))"
  apply(simp add: prefix_def suffix_def)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      x="rev c"
      in exI)
  apply(rule rev_inj2)
  apply(clarsimp)
  done

lemma length_foldl_prefix: "
  prefix w v
  \<Longrightarrow> length (foldl (@) [] w) \<le> length (foldl (@) [] v)"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply (metis foldl_append le_iff_add length_foldl length_splice)
  done

lemma map_prefix: "
  prefix w v
  \<Longrightarrow> prefix (map f w) (map f v)"
  apply (metis map_append prefix_def)
  done

lemma prefix_take: "
  i\<le>j
  \<Longrightarrow> prefix (take i w) (take j w)"
  apply (metis append_take_drop_id_hlp kPrefix_def prefix_def take_take_prime)
  done

lemma prefix_pre_append: "
  prefix (x@a) (x@b)
  \<Longrightarrow> prefix a b"
  apply(simp add: prefix_def)
  done

lemma equal_by_seperator: "
  w1@a1#v1 = w2@a2#v2
  \<Longrightarrow> a1 \<notin> set w2
  \<Longrightarrow> a2 \<notin> set w1
  \<Longrightarrow> w1=w2"
  apply(subgoal_tac "prefix w1 w2 \<or> prefix w2 w1")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
  apply(rename_tac c a list)(*strict*)
  apply(clarsimp)
  done

lemma equal_by_seperator_prime: "
  w1@a1#v1 = w2@a2#v2
  \<Longrightarrow> a1 \<notin> set v2
  \<Longrightarrow> a2 \<notin> set v1
  \<Longrightarrow> v1=v2"
  apply(subgoal_tac "prefix w1 w2 \<or> prefix w2 w1")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
  apply(rename_tac c a list)(*strict*)
  apply(clarsimp)
  done

lemma in_either_of_append: "
  w1@a#w2 = v1@v2
  \<Longrightarrow> a \<in> set v1 \<or> a \<in> set v2"
  apply(subgoal_tac "prefix w1 v1 \<or> prefix v1 w1")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
   apply(rename_tac c aa list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma butlast_if_match_idemp_if_ignore: "
  butlast_if_match w x = w
  \<Longrightarrow> butlast_if_match w x = butlast_if_match (butlast_if_match w x) x"
  apply(force)
  done

lemma prefix_length_eq: "
  length a = length b
  \<Longrightarrow> prefix a z
  \<Longrightarrow> prefix b z
  \<Longrightarrow> a=b"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma prefix_closure_preserves_finiteness: "
  finite X
  \<Longrightarrow> finite A
  \<Longrightarrow> A \<subseteq> kleene_star X
  \<Longrightarrow> finite (prefix_closure A)"
  apply(rule_tac
      t="prefix_closure A"
      and s="\<Union>{prefix_closure{w}| w. w \<in> A}"
      in ssubst)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x c)(*strict*)
    apply(rule_tac
      x="prefix_closure{x@c}"
      in exI)
    apply(simp add: prefix_closure_def prefix_def)
    apply(rule_tac
      x="x@c"
      in exI)
    apply(simp add: prefix_closure_def prefix_def)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(rule_tac
      x="x@c"
      in exI)
   apply(clarsimp)
  apply(rule finite_big_union)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply (metis Suc_neq_Zero card_infinite tmp00xx)
  done

lemma substitution_can_me_simulated_somewhere_with_context: "
  \<forall>l r. l @ teA A # r \<noteq> w1
  \<Longrightarrow> w1 @ l @ teA A # r = la @ teA A # ra
  \<Longrightarrow> (\<exists>l r. la @ w @ ra = w1 @ l @ w @ r)"
  apply(subgoal_tac "\<exists>z. w1 @ z = la")
   apply(auto)
   apply(rename_tac z)(*strict*)
   apply(rule_tac
      x = "z"
      in exI)
   apply(rule_tac
      x = "ra"
      in exI)
   apply(auto)
  apply(subgoal_tac "w1 \<sqsubseteq> la \<or> la \<sqsubseteq> w1")
   defer
   apply(rule mutual_prefix_prefix)
   apply(blast)
  apply(erule disjE)
   apply(simp add: prefix_def)
  apply(simp add: prefix_def)
  apply(auto)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(auto)
  done

lemma terminalHeadEquals1: "
  setA v1 = {}
  \<Longrightarrow> setA v2 = {}
  \<Longrightarrow> v1@[teA A]@w1 = v2@[teA B]@w2
  \<Longrightarrow> v1 = v2"
  apply(subgoal_tac "prefix v1 v2 \<or> prefix v2 v1")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(clarsimp)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma suffixes_setB_1: "
  teB b # w  \<in> suffixes v
  \<Longrightarrow> b  \<in> setB v"
  apply(induct v)
   apply(force)
  apply(rename_tac a v)(*strict*)
  apply(force)
  done

lemma suffixes_setA_1: "
  teA A # w  \<in> suffixes v
  \<Longrightarrow> A  \<in> setA v"
  apply(induct v)
   apply(auto)
  done

lemma suffixes_setA_2: "
  setA v \<subseteq> X
  \<Longrightarrow> w1 @ teA A # w2  \<in> suffixes v
  \<Longrightarrow> A  \<in> X"
  apply (metis suffixes_intro1 suffixes_intro2_rev concat_asso elemInsetA subsetE)
  done

lemma identical_temrinal_maximal_prefix: "
  liftB (w1::'b list)@teA (A::'a)#v1 = liftB w2@teA B#v2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "liftB w2 = liftB w1@(drop (length (liftB w1)) (liftB w2))")
   prefer 2
   apply(rule border_left)
    apply(rule setA_liftB)
   apply(force)
  apply(subgoal_tac "liftB w1 = liftB w2@(drop (length (liftB w2)) (liftB w1))")
   prefer 2
   apply(rule border_left)
    apply(rule setA_liftB)
   apply(rule sym)
   apply(force)
  apply(subgoal_tac "length (liftB w2) \<ge> length (liftB w1)")
   prefer 2
   apply(rule append_length_inc)
   apply(force)
  apply(subgoal_tac "length (liftB w1) \<ge> length (liftB w2)")
   prefer 2
   apply(rule_tac
      r = "drop (length (liftB w2)) (liftB w1)"
      in append_length_inc)
   apply(simp (no_asm))
  apply(rule liftB_inj)
  apply(rule length_append_equal)
   apply(rule order_antisym)
    apply(simp (no_asm_use))
   apply(simp (no_asm_use))
  apply(force)
  done

lemma maximal_terminal_prefix_THE: "
  setA x = {}
  \<Longrightarrow> res = filterB x
  \<Longrightarrow> (THE y. (\<exists>w. liftB y @ w = x @ teA A # v) \<and> (\<forall>w. liftB y @ w = x @ teA A # v \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))) = res"
  apply(rule the_equality)
   apply(rule conjI)
    apply(rule_tac
      x = "teA A # v"
      in exI)
    apply(clarsimp)
    apply(rule liftBDeConv2)
    apply(force)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(case_tac w)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b)(*strict*)
   apply(subgoal_tac "liftB (filterB x) = x")
    apply(rename_tac list b)(*strict*)
    apply(force)
   apply(rename_tac list b)(*strict*)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  apply(rename_tac y w)(*strict*)
  apply(erule_tac
      x = "w"
      in allE)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac y w)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(subgoal_tac "x @ teA A # v \<noteq> liftB y")
    apply(rename_tac y)(*strict*)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(rule_tac
      A = "A"
      in unequal_by_setA)
    apply(rename_tac y)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(rule_tac
      t = "setA (liftB y)"
      and s = "{}"
      in ssubst)
    apply(rename_tac y)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac y a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac y a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y list aa)(*strict*)
   apply(rule_tac
      A = "aa"
      in identical_temrinal_maximal_prefix)
   apply(rule_tac
      t = "liftB (filterB x)"
      and s = "x"
      in ssubst)
    apply(rename_tac y list aa)(*strict*)
    apply(rule liftBDeConv2)
    apply(force)
   apply(rename_tac y list aa)(*strict*)
   apply(force)
  apply(rename_tac y a list b)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_ex1: "
  \<exists>!y. (\<exists>wa. liftB y @ wa = w) \<and> (\<forall>wa. liftB y @ wa = w \<longrightarrow> (case wa of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      a = "[]"
      in ex1I)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a y wa)(*strict*)
  apply(case_tac a)
   apply(rename_tac a y wa aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y wa aa)(*strict*)
   apply(rule_tac
      a = "[]"
      in ex1I)
    apply(rename_tac y wa aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac y wa aa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac y wa aa x waa)(*strict*)
   apply(case_tac x)
    apply(rename_tac y wa aa x waa)(*strict*)
    apply(clarsimp)
   apply(rename_tac y wa aa x waa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a y wa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y wa b)(*strict*)
  apply(rule_tac
      a = "b#y"
      in ex1I)
   apply(rename_tac y wa b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y wa b x)(*strict*)
  apply(clarsimp)
  apply(rename_tac y wa b x waa)(*strict*)
  apply(case_tac x)
   apply(rename_tac y wa b x waa)(*strict*)
   apply(clarsimp)
  apply(rename_tac y wa b x waa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac y wa waa list)(*strict*)
  apply(erule_tac
      x = "waa"
      in allE)
  apply(clarsimp)
  apply(case_tac wa)
   apply(rename_tac y wa waa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac y waa list)(*strict*)
   apply(case_tac waa)
    apply(rename_tac y waa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac y waa list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac y list a lista)(*strict*)
   apply(case_tac a)
    apply(rename_tac y list a lista aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac y list lista aa)(*strict*)
    apply(subgoal_tac "liftB list @ teA aa # lista \<noteq> liftB y")
     apply(rename_tac y list lista aa)(*strict*)
     apply(force)
    apply(rename_tac y list lista aa)(*strict*)
    apply(rule_tac
      A = "aa"
      in unequal_by_setA)
     apply(rename_tac y list lista aa)(*strict*)
     apply(rule elemInsetA)
    apply(rename_tac y list lista aa)(*strict*)
    apply(rule_tac
      t = "setA (liftB y)"
      and s = "{}"
      in ssubst)
     apply(rename_tac y list lista aa)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac y list lista aa)(*strict*)
    apply(force)
   apply(rename_tac y list a lista b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y wa waa list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac y waa list a lista)(*strict*)
  apply(case_tac a)
   apply(rename_tac y waa list a lista aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y waa list lista aa)(*strict*)
   apply(case_tac waa)
    apply(rename_tac y waa list lista aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac y waa list lista aa a listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac y list lista aa a listb)(*strict*)
   apply(case_tac a)
    apply(rename_tac y list lista aa a listb ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac y list lista aa listb ab)(*strict*)
    apply(rule identical_temrinal_maximal_prefix)
    apply(force)
   apply(rename_tac y list lista aa a listb b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y waa list a lista b)(*strict*)
  apply(clarsimp)
  done

lemma maxTermPrefix_pull_out2: "
  maxTermPrefix w = a#v
  \<Longrightarrow> \<exists>y. w = (teB a)#y \<and> (maxTermPrefix y = v)"
  apply(simp add: maxTermPrefix_def)
  apply(subgoal_tac "\<exists>!y. (\<exists>wa. liftB y @ wa = w) \<and> (\<forall>wa. liftB y @ wa = w \<longrightarrow> (case wa of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))")
   prefer 2
   apply(rule maximalPrefixB_ex1)
  apply(subgoal_tac "(\<exists>wa. liftB (a#v) @ wa = w) \<and> (\<forall>wa. liftB (a#v) @ wa = w \<longrightarrow> (case wa of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))")
   prefer 2
   apply(rule_tac
      P = "\<lambda>y. (\<exists>wa. liftB y @ wa = w) \<and> (\<forall>wa. liftB y @ wa = w \<longrightarrow> (case wa of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))"
      in THE_eq_prop)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac y wa waa)(*strict*)
  apply(subgoal_tac "\<exists>!y. (\<exists>w. liftB y @ w = liftB v @ wa) \<and> (\<forall>w. liftB y @ w = liftB v @ wa \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False))")
   apply(rename_tac y wa waa)(*strict*)
   prefer 2
   apply(rule maximalPrefixB_ex1)
  apply(rename_tac y wa waa)(*strict*)
  apply(rule the1_equality)
   apply(rename_tac y wa waa)(*strict*)
   apply(force)
  apply(rename_tac y wa waa)(*strict*)
  apply(clarsimp)
  done

lemma maxTermPrefixS_from_maxTermPrefix: "
  maxTermPrefix w = v
  \<Longrightarrow> maxTermPrefixS w v"
  apply(simp add: maxTermPrefix_def maxTermPrefixS_def)
  apply(rule_tac
      z = "v"
      in THE_eq_prop)
   apply(rule maximalPrefixB_ex1)
  apply(force)
  done

lemma maxTermPrefix_from_maxTermPrefixS: "
  maxTermPrefixS w v
  \<Longrightarrow> maxTermPrefix w = v"
  apply(simp add: maxTermPrefix_def maxTermPrefixS_def)
  apply(rule the1_equality)
   apply(rule maximalPrefixB_ex1)
  apply(force)
  done

lemma maxTermPrefix_pull_out_mult: "
  maxTermPrefixS w (x@v)
  \<Longrightarrow> \<exists>y. w = liftB x @ y \<and> (maxTermPrefixS y v)"
  apply(induct x arbitrary: w v)
   apply(rename_tac w v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w v)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>z. w = (teB a)#z \<and> (maxTermPrefix z = x@v)")
   apply(rename_tac a x w v)(*strict*)
   apply(clarsimp)
   apply(rename_tac a x v z)(*strict*)
   apply(erule_tac
      x = "z"
      in meta_allE)
   apply(erule_tac
      x = "v"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac a x v z)(*strict*)
    apply(rule maxTermPrefixS_from_maxTermPrefix)
    apply(force)
   apply(rename_tac a x v z)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x w v)(*strict*)
  apply(rule maxTermPrefix_pull_out2)
  apply(rule maxTermPrefix_from_maxTermPrefixS)
  apply(force)
  done

lemma maxTermPrefix_term_string: "
  maxTermPrefix (liftB w) = w"
  apply(simp add: maxTermPrefix_def)
  apply(rule the1_equality)
   apply(rule maximalPrefixB_ex1)
  apply(force)
  done

lemma maxTermPrefix_mixed_string: "
  maxTermPrefix (liftB w @ teA A # v) = w"
  apply(simp add: maxTermPrefix_def)
  apply(rule the1_equality)
   apply(rule maximalPrefixB_ex1)
  apply(force)
  done

lemma maxTermPrefix_one_nonterm: "
  maxTermPrefix [teA A] = []"
  apply(simp add: maxTermPrefix_def)
  apply(rule the1_equality)
   apply(rule maximalPrefixB_ex1)
  apply(force)
  done

lemma maxTermPrefix_shift: "
  maxTermPrefix (liftB w @ v) = w@(maxTermPrefix v)"
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = v \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   prefer 2
   apply(rule maxSplit)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1)"
      and s = "w1"
      in ssubst)
    apply(rename_tac w1)(*strict*)
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac w1)(*strict*)
   apply(rule_tac
      t = "liftB w @ liftB w1"
      and s = "liftB (w@w1)"
      in subst)
    apply(rename_tac w1)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac w1)(*strict*)
   apply(rule maxTermPrefix_term_string)
  apply(rename_tac w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w1 a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 list aa)(*strict*)
   defer
   apply(rename_tac w1 a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 list aa)(*strict*)
  apply(rule_tac
      t = "maxTermPrefix (liftB w1 @ teA aa # list)"
      and s = "w1"
      in ssubst)
   apply(rename_tac w1 list aa)(*strict*)
   apply(rule maxTermPrefix_mixed_string)
  apply(rename_tac w1 list aa)(*strict*)
  apply(rule_tac
      t = "liftB w @ liftB w1 @ teA aa # list"
      and s = "(liftB w @ liftB w1) @ teA aa # list"
      in ssubst)
   apply(rename_tac w1 list aa)(*strict*)
   apply(force)
  apply(rename_tac w1 list aa)(*strict*)
  apply(rule_tac
      t = "liftB w @ liftB w1"
      and s = "liftB (w@w1)"
      in subst)
   apply(rename_tac w1 list aa)(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac w1 list aa)(*strict*)
  apply(rule maxTermPrefix_mixed_string)
  done

lemma maxTermPrefix_drop_tail: "
  maxTermPrefix (w @ (teA A) # v) = maxTermPrefix w"
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = w \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   prefer 2
   apply(rule maxSplit)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1 @ teA A # v)"
      and s = "w1"
      in ssubst)
    apply(rename_tac w1)(*strict*)
    apply(rule maxTermPrefix_mixed_string)
   apply(rename_tac w1)(*strict*)
   apply(rule sym)
   apply(rule maxTermPrefix_term_string)
  apply(rename_tac w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w1 a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 list aa)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1 @ teA aa # list @ teA A # v)"
      and s = "w1"
      in ssubst)
    apply(rename_tac w1 list aa)(*strict*)
    apply(rule maxTermPrefix_mixed_string)
   apply(rename_tac w1 list aa)(*strict*)
   apply(rule sym)
   apply(rule maxTermPrefix_mixed_string)
  apply(rename_tac w1 a list b)(*strict*)
  apply(clarsimp)
  done

lemma maxTermPrefix_distrib_append: "
  setA w = {}
  \<Longrightarrow> maxTermPrefix (w @ v) = maxTermPrefix w @ (maxTermPrefix v)"
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = w \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   prefer 2
   apply(rule maxSplit)
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = v \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   prefer 2
   apply(rule maxSplit)
  apply(clarsimp)
  apply(rename_tac w1 w1a w2 w2a)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w1 w1a w2 w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w1a w2a)(*strict*)
   apply(case_tac w2a)
    apply(rename_tac w1 w1a w2a)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 w1a)(*strict*)
    apply(rule_tac
      t = "liftB w1 @ liftB w1a"
      and s = "liftB (w1 @ w1a)"
      in subst)
     apply(rename_tac w1 w1a)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac w1 w1a)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB (w1 @ w1a))"
      and s = "w1@w1a"
      in ssubst)
     apply(rename_tac w1 w1a)(*strict*)
     apply(rule maxTermPrefix_term_string)
    apply(rename_tac w1 w1a)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB w1)"
      and s = "w1"
      in ssubst)
     apply(rename_tac w1 w1a)(*strict*)
     apply(rule maxTermPrefix_term_string)
    apply(rename_tac w1 w1a)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB w1a)"
      and s = "w1a"
      in ssubst)
     apply(rename_tac w1 w1a)(*strict*)
     apply(rule maxTermPrefix_term_string)
    apply(rename_tac w1 w1a)(*strict*)
    apply(force)
   apply(rename_tac w1 w1a w2a a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w1a a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac w1 w1a a list aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(rule_tac
      t = "liftB w1 @ liftB w1a @ teA aa # list"
      and s = "(liftB w1 @ liftB w1a) @ teA aa # list"
      in ssubst)
     apply(rename_tac w1 w1a list aa)(*strict*)
     apply(force)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(rule_tac
      t = "liftB w1 @ liftB w1a"
      and s = "liftB (w1 @ w1a)"
      in subst)
     apply(rename_tac w1 w1a list aa)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB (w1 @ w1a) @ teA aa # list)"
      and s = "w1@w1a"
      in ssubst)
     apply(rename_tac w1 w1a list aa)(*strict*)
     apply(rule maxTermPrefix_mixed_string)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB w1a @ teA aa # list)"
      and s = "w1a"
      in ssubst)
     apply(rename_tac w1 w1a list aa)(*strict*)
     apply(rule maxTermPrefix_mixed_string)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(rule_tac
      t = "maxTermPrefix (liftB w1)"
      and s = "w1"
      in ssubst)
     apply(rename_tac w1 w1a list aa)(*strict*)
     apply(rule maxTermPrefix_term_string)
    apply(rename_tac w1 w1a list aa)(*strict*)
    apply(force)
   apply(rename_tac w1 w1a a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 w1a w2 w2a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w1a w2a a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w1 w1a w2a a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w1a w2a list aa)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(force)
  apply(rename_tac w1 w1a w2a a list b)(*strict*)
  apply(force)
  done

lemma maxTermPrefix_on_maxSplit: "
  (case w2a of [] \<Rightarrow> True | ((teA aa) # list) \<Rightarrow> True | ((teB b) # list) \<Rightarrow> False)
  \<Longrightarrow> (maxTermPrefix ((liftB w1a) @ w2a)) = w1a"
  apply(case_tac w2a)
   apply(clarsimp)
   apply(rule maxTermPrefix_term_string)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(rule maxTermPrefix_mixed_string)
  apply(rename_tac a list b)(*strict*)
  apply(force)
  done

lemma maxTermPrefix_prefix: "
  \<exists>z. liftB (maxTermPrefix w) @ z = w"
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = w \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   prefer 2
   apply(rule maxSplit)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1)"
      and s = "w1"
      in ssubst)
    apply(rename_tac w1)(*strict*)
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac w1)(*strict*)
   apply(force)
  apply(rename_tac w1 w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w1 a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 list aa)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1 @ teA aa # list)"
      and s = "w1"
      in ssubst)
    apply(rename_tac w1 list aa)(*strict*)
    apply(rule maxTermPrefix_mixed_string)
   apply(rename_tac w1 list aa)(*strict*)
   apply(force)
  apply(rename_tac w1 a list b)(*strict*)
  apply(force)
  done

lemma maxTermPrefixS_maxTermPrefix: "
  maxTermPrefixS w (maxTermPrefix w)"
  apply(simp add: maxTermPrefixS_def)
  apply(rule conjI)
   apply(rule maxTermPrefix_prefix)
  apply(clarsimp)
  apply(rename_tac wa)(*strict*)
  apply(case_tac wa)
   apply(rename_tac wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = w \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   apply(rename_tac list b)(*strict*)
   prefer 2
   apply(rule maxSplit)
  apply(rename_tac list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b w1 w2)(*strict*)
  apply(case_tac w2)
   apply(rename_tac list b w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b w1)(*strict*)
   apply(subgoal_tac "liftB (maxTermPrefix (liftB w1)) @ teB b # list \<noteq> liftB w1")
    apply(rename_tac list b w1)(*strict*)
    apply(force)
   apply(rename_tac list b w1)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1)"
      and s = "w1"
      in ssubst)
    apply(rename_tac list b w1)(*strict*)
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac list b w1)(*strict*)
   apply(force)
  apply(rename_tac list b w1 w2 a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b w1 a lista)(*strict*)
  apply(case_tac a)
   apply(rename_tac list b w1 a lista aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b w1 lista aa)(*strict*)
   apply(subgoal_tac "liftB (maxTermPrefix (liftB w1 @ teA aa # lista)) @ teB b # list \<noteq> liftB w1 @ teA aa # lista")
    apply(rename_tac list b w1 lista aa)(*strict*)
    apply(force)
   apply(rename_tac list b w1 lista aa)(*strict*)
   apply(rule_tac
      t = "maxTermPrefix (liftB w1 @ teA aa # lista)"
      and s = "w1"
      in ssubst)
    apply(rename_tac list b w1 lista aa)(*strict*)
    apply(rule maxTermPrefix_mixed_string)
   apply(rename_tac list b w1 lista aa)(*strict*)
   apply(force)
  apply(rename_tac list b w1 a lista ba)(*strict*)
  apply(force)
  done

lemma maxTermPrefix_on_term_string_prime: "
  setA w = {}
  \<Longrightarrow> maxTermPrefix w = filterB w"
  apply(subgoal_tac "\<exists>v. w = liftB v")
   apply(clarsimp)
   apply(rename_tac v)(*strict*)
   apply(rule_tac
      t = "filterB (liftB v)"
      and s = "v"
      in ssubst)
    apply(rename_tac v)(*strict*)
    apply(rule liftBDeConv1)
   apply(rename_tac v)(*strict*)
   apply(rule maxTermPrefix_term_string)
  apply(rule setA_liftB_exists)
  apply(force)
  done

lemma suffix_tails_terminal: "
  setA r = {}
  \<Longrightarrow> setA ra = {}
  \<Longrightarrow> l @ v @ r = w @ teA A # ra
  \<Longrightarrow> suffix ra r"
  apply(simp add: suffix_def)
  apply(subgoal_tac "prefix (l@v) (w@[teA A]) \<or> prefix (w@[teA A]) (l@v)")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
    apply(case_tac v)
     apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. v = w' @ [x']")
     apply(rename_tac a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(thin_tac "v = a#list")
    apply(clarsimp)
   apply(rename_tac c a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac c a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac c a list)(*strict*)
   apply(thin_tac "c = a#list")
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply (metis elemInsetA emptyE)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix (w@[teA A]) l \<or> prefix l (w@[teA A])")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac c ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac c ca a list)(*strict*)
  apply(thin_tac "ca = a#list")
  apply(clarsimp)
  done

lemma liftB_creates_suffix: "
  liftB x \<sqsupseteq> liftB w
  \<Longrightarrow> x \<sqsupseteq> w"
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      x = "filterB c"
      in exI)
  apply(rule_tac
      t = "x"
      and s = "filterB (liftB x)"
      in ssubst)
   apply(rename_tac c)(*strict*)
   apply (simp add: liftBDeConv1)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      t = "w"
      and s = "filterB (liftB w)"
      in ssubst)
   apply(rename_tac c)(*strict*)
   apply (simp add: liftBDeConv1)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      t = "filterB c @ filterB (liftB w)"
      and s = "filterB (c@ liftB w)"
      in ssubst)
   apply(rename_tac c)(*strict*)
   apply (simp add: liftBDeConv1 filterB_commutes_over_concat)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      t = "liftB x"
      and s = "c @ liftB w"
      in ssubst)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma THE_split3: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> (THE v. \<exists>w. l @ teA A # r = liftB w @ liftA v) = A # filterA r"
  apply(rule_tac
      a="[A]@(filterA r)"
      in HOL.theI2)
    apply(rule_tac
      x="filterB l"
      in exI)
    apply(clarsimp)
    apply (metis liftA.simps(2) setB_empty_then_liftA_vs_filterA liftBDeConv2)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(case_tac x)
    apply(rename_tac x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply (metis liftBDeConv2 append_self_conv list.simps(2) maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime maxTermPrefix_term_string)
   apply(rename_tac x w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(case_tac x)
    apply(rename_tac x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply (metis liftBDeConv2 append_self_conv list.simps(2) maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime maxTermPrefix_term_string)
   apply(rename_tac x w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply (metis liftA.simps(2) liftA_vs_filterA liftBDeConv2 append_Nil2 append_linj append_self_conv DT_two_elements.inject(1) list.sel maxTermPrefix_drop_tail maxTermPrefix_mixed_string maxTermPrefix_on_term_string_prime maxTermPrefix_shift)
  apply(rename_tac w a list)(*strict*)
  apply (metis liftA.simps(2) liftA_vs_filterA liftBDeConv2 append_Nil2 append_linj append_self_conv DT_two_elements.inject(1) list.sel maxTermPrefix_drop_tail maxTermPrefix_mixed_string maxTermPrefix_on_term_string_prime maxTermPrefix_shift)
  done

lemma THE_split3_prime: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> (THE v. \<exists>w. l @ teA A' # teA A # r = liftB w @ liftA v) = A' # A # filterA r"
  apply(rule_tac
      a="[A',A]@(filterA r)"
      in HOL.theI2)
    apply(rule_tac
      x="filterB l"
      in exI)
    apply(clarsimp)
    apply (metis liftA.simps(2) setB_empty_then_liftA_vs_filterA liftBDeConv2)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(case_tac x)
    apply(rename_tac x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply (metis liftBDeConv2 append_self_conv list.simps(2) maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime maxTermPrefix_term_string)
   apply(rename_tac x w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w)(*strict*)
   apply(case_tac x)
    apply(rename_tac x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply (metis liftBDeConv2 append_self_conv list.simps(2) maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime maxTermPrefix_term_string)
   apply(rename_tac x w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac w a)(*strict*)
    apply(case_tac r)
     apply(rename_tac w a)(*strict*)
     apply(clarsimp)
     apply(rename_tac w)(*strict*)
     apply (metis setA_liftB elemInsetA emptyE)
    apply(rename_tac w a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. r=w'@[x']")
     apply(rename_tac w a aa list)(*strict*)
     prefer 2
     apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w a aa list)(*strict*)
    apply(thin_tac "r=aa # list")
    apply(clarsimp)
    apply(rename_tac w a w')(*strict*)
    apply (metis setA_liftB elemInsetA emptyE)
   apply(rename_tac w a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a aa lista)(*strict*)
   apply (metis liftA.simps(2) liftA_vs_filterA liftBDeConv2 append_Nil2 append_linj append_self_conv DT_two_elements.inject(1) list.sel maxTermPrefix_drop_tail maxTermPrefix_mixed_string maxTermPrefix_on_term_string_prime maxTermPrefix_shift)
  apply(rename_tac w a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac w a)(*strict*)
   apply(case_tac r)
    apply(rename_tac w a)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply (metis setA_liftB elemInsetA emptyE)
   apply(rename_tac w a aa list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. r=w'@[x']")
    apply(rename_tac w a aa list)(*strict*)
    prefer 2
    apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w a aa list)(*strict*)
   apply(thin_tac "r=aa # list")
   apply(clarsimp)
   apply(rename_tac w a w')(*strict*)
   apply (metis setA_liftB elemInsetA emptyE)
  apply(rename_tac w a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac w a aa lista)(*strict*)
  apply (metis liftA.simps(2) liftA_vs_filterA liftBDeConv2 append_Nil2 append_linj append_self_conv DT_two_elements.inject(1) list.sel maxTermPrefix_drop_tail maxTermPrefix_mixed_string maxTermPrefix_on_term_string_prime maxTermPrefix_shift )
  done

lemma THE_split4: "
  setB r = {}
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> z = filterB l
  \<Longrightarrow> (THE w. \<exists>v. l @ teA A # r = liftB w @ liftA v) = z"
  apply(rule_tac
      a="z"
      in HOL.theI2)
    apply(rule_tac
      x="[A]@(filterA r)"
      in exI)
    apply(clarsimp)
    apply (metis liftA.simps(2) setB_empty_then_liftA_vs_filterA liftBDeConv2)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(case_tac v)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply (metis maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime maxTermPrefix_term_string)
   apply(rename_tac x v a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply (metis liftA.simps(2) maxTermPrefixS_maxTermPrefix maxTermPrefix_on_term_string maxTermPrefix_term_string split_decide1)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply (metis maxTermPrefixS_maxTermPrefix maxTermPrefix_on_term_string maxTermPrefix_term_string split_decide1)
  done

lemma THE_split3_X: "
  setA l = {}
  \<Longrightarrow> (THE v. \<exists>w. l @ [teA A] = liftB w @ liftA v) = [A]"
  apply(rule_tac
      t="(THE v. \<exists>w. l @ [teA A] = liftB w @ liftA v)"
      in ssubst)
   apply(rule THE_split3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma THE_split3_XX: "
  setA l = {}
  \<Longrightarrow> (THE v. \<exists>w. l @ [teA A, teA B] = liftB w @ liftA v) = [A, B]"
  apply(rule_tac
      t="(THE v. \<exists>w. l @ [teA A,teA B] = liftB w @ liftA v)"
      in ssubst)
   apply(rule THE_split3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma SPLIT_2_1: "
  (THE wa. \<exists>v. liftB wx @ teA A # liftA wv = liftB wa @ liftA v) = wx"
  apply(rule_tac
      a="wx"
      in HOL.theI2)
    apply(rule_tac
      x="A # wv"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(case_tac v)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply (metis setA_liftB liftA.simps(1) liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_Nil2 list.simps(2))
   apply(rename_tac x v a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x a list)(*strict*)
   apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_injective1 maxTermPrefix_shift)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(case_tac v)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply (metis setA_liftB liftA.simps(1) liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_Nil2 list.simps(2))
  apply(rename_tac x v a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x a list)(*strict*)
  apply (metis setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split append_injective1 maxTermPrefix_shift)
  done

lemma split1: "
  (THE v. \<exists>x. liftB w @ [teA A] = liftB x @ liftA v) = [A]"
  apply(rule_tac
      t="liftB w @ [teA A]"
      and s="liftB w @ [teA A] @ liftA([])"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="[A]"
      and s="[A]@[]"
      in ssubst)
   apply(force)
  apply (simp add: THE_split3_X setA_liftB_empty)
  done

lemma split2: "
  (THE x. \<exists>v. liftB w @ [teA A] = liftB x @ liftA v) = w"
  apply(rule_tac
      t="liftB w @ [teA A]"
      and s="liftB w @ [teA A] @ liftA([])"
      in ssubst)
   apply(force)
  apply (metis ConsApp SPLIT_2_1)
  done

lemma equal_front_by_liftB_setA: "
  liftB w1 @ teA xa # w2 = l @ teA x # w2a @ r
  \<Longrightarrow> setA l = {}
  \<Longrightarrow> liftB w1 = l"
  apply (metis setA_liftB append_Cons append_Nil terminalHeadEquals1)
  done

lemma prefix_of_terminalInitial: "
  liftB v1 @ teA B1 # liftA r1 =
  liftB w1 @ x @ liftA w2
  \<Longrightarrow> prefix w1 v1"
  apply (metis liftA.simps(2) maxTermPrefix_mixed_string maxTermPrefix_shift prefix_append)
  done

lemma SPLIT_4XX: "
  (THE w.
           \<exists>v. liftB w' @ [teA A, teA B] =
               liftB w @ liftA v) =
       w'"
  apply(rule_tac
      t="[teA A, teA B]"
      and s="liftA[A,B]"
      in ssubst)
   apply(force)
  apply (metis SPLIT_2_1 liftA.simps(2))
  done

lemma simple_identify: "
  liftB x1 @ teA A1 # r1 = liftB x2 @ teA A2 # r2
  \<Longrightarrow> x1=x2 \<and> A1=A2 \<and> r1=r2"
  apply(subgoal_tac "x1=x2")
   prefer 2
   apply (metis maxTermPrefix_drop_tail maxTermPrefix_term_string)
  apply(clarsimp)
  done

lemma hlpX: "
  liftB w @ c = liftB v @ teA A # r
  \<Longrightarrow> prefix w v"
  apply (metis maxTermPrefix_drop_tail maxTermPrefix_shift maxTermPrefix_term_string prefix_append)
  done

lemma split_setA_setB: "
  a@b=c@d
  \<Longrightarrow> setA a={}
  \<Longrightarrow> setA c={}
  \<Longrightarrow> setB [hd b]={}
  \<Longrightarrow> setB [hd d]={}
  \<Longrightarrow> a=c"
  apply(subgoal_tac "prefix a c \<or> prefix c a")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
   apply(rename_tac c aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa list)(*strict*)
   apply(case_tac aa)
    apply(rename_tac aa list aaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac list aa)(*strict*)
    apply(simp add: simpY)
   apply(rename_tac aa list b)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(simp add: simpY)
  apply(rename_tac a list ba)(*strict*)
  apply(clarsimp)
  done

lemma terminalTailEquals1_prime: "
  l @ teA A # liftB r = l' @ teA A' # liftB r'
  \<Longrightarrow> liftB r = liftB r'"
  apply (metis setA_liftB append_Cons append_Nil maxTermPrefix_term_string terminalTailEquals1)
  done

lemma maximalPrefixB_drop_liftB: "
  maximalPrefixB (liftB w @ r) = w @ (maximalPrefixB r)"
  apply (metis ConsApp maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string maximalPrefixB_select)
  done

lemma maximalPrefixB_drop_teB: "
  maximalPrefixB (teB b # r) = [b] @ (maximalPrefixB r)"
  apply(rule_tac
      t="teB b#r"
      and s="liftB [b] @ r"
      in ssubst)
   apply(force)
  apply (metis ConsApp maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string maximalPrefixB_select)
  done

lemma maximalPrefixB_prefix: "
  x \<sqsubseteq> maximalPrefixB (liftB x @ w)"
  apply(induct x)
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(rename_tac a x)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  done

lemma maxTermPrefix_pull_out: "
  maxTermPrefix (teB b # w) = b # maxTermPrefix w"
  apply(induct w)
   apply (metis liftB.simps(1) liftB.simps(2) maxTermPrefix_term_string)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply (metis ConsApp liftB.simps(1) liftB.simps(2) append_self_conv maxTermPrefix_drop_tail maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string)
  apply(rename_tac a w ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac w ba)(*strict*)
  apply (metis ConsApp liftB.simps(1) liftB.simps(2) maxTermPrefix_shift)
  done

lemma maxTermPrefix_vs_maximalPrefixB: "
  maxTermPrefix w = maximalPrefixB w"
  apply(induct w)
   apply(clarsimp)
   apply (metis liftB.simps(1) maxTermPrefix_term_string)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply(thin_tac "maxTermPrefix w = maximalPrefixB w")
   apply (metis setA.simps(1) filterB.simps(1) append_Nil maxTermPrefix_drop_tail maxTermPrefix_on_term_string_prime)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b)(*strict*)
  apply(rule_tac
      t="maximalPrefixB w"
      and s="maxTermPrefix w"
      in ssubst)
   apply(rename_tac w b)(*strict*)
   apply(force)
  apply(rename_tac w b)(*strict*)
  apply(thin_tac "maxTermPrefix w = maximalPrefixB w")
  apply(rule maxTermPrefix_pull_out)
  done

end
