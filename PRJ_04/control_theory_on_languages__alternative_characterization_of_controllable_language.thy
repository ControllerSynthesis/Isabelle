section {*control\_theory\_on\_languages\_\_alternative\_characterization\_of\_controllable\_language*}
theory
  control_theory_on_languages__alternative_characterization_of_controllable_language

imports
  control_theory_on_languages

begin

definition star_controllable_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "star_controllable_language A \<Sigma>UC L \<equiv>
  (append_language A (kleene_star \<Sigma>UC)) \<inter> L \<subseteq> A"

definition equal_star_controllable_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "equal_star_controllable_language A \<Sigma>UC L \<equiv>
  (append_language A (kleene_star \<Sigma>UC)) \<inter> L = A"

definition right_quotient :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "right_quotient L1 L2 \<equiv>
  {w . \<exists>v \<in> L2. w @ v \<in> L1}"

lemma example1_right_quotient: "
  right_quotient { [ (2::nat), 1, 0 ] , [ 1, 2 ] , [ 0, 2, 0 ] } { [ 0 ] , [ 1, 0 ] } = { [ 2, 1 ] , [ 0, 2 ] , [ 2 ] }"
  apply(simp add: right_quotient_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma example2_right_quotient : "
  right_quotient (append_language { [] } { [ 1 ] , [ 0, 1 ] }) { [ 1 ] , [ 0, 1 ] } = { [] , [ 0 ] }"
  apply(simp add: right_quotient_def append_language_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma example3_right_quotient: "
  right_quotient A (kleene_star B) \<supseteq> A"
  apply(simp add: right_quotient_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  done

lemma example4_right_quotient: "
  A = prefix_closure A
  \<Longrightarrow> B \<subseteq> A
  \<Longrightarrow> right_quotient B (kleene_star C) \<subseteq> A"
  apply(simp add: prefix_closure_def right_quotient_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(rule_tac
      A="{w. \<exists>v. v \<in> A \<and> w \<sqsubseteq> v}"
      in set_mp)
   apply(rename_tac x v)(*strict*)
   apply(force)
  apply(rename_tac x v)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
      x="x@v"
      in exI)
  apply(simp add: prefix_def)
  apply(force)
  done

definition left_quotient :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "left_quotient L1 L2 \<equiv>
  {w. \<exists>v \<in> L1. v @ w \<in> L2}"

definition right_quotient_controllable_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> bool" where
  "right_quotient_controllable_language L1 \<Sigma>UC L2 \<Sigma> \<equiv>
  right_quotient ((kleene_star \<Sigma> - L1) \<inter> L2) (kleene_star \<Sigma>UC)
    \<subseteq> (kleene_star \<Sigma> - L1 ) \<inter> L2"

definition equal_right_quotient_controllable_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> bool" where
  "equal_right_quotient_controllable_language L1 \<Sigma>UC L2 \<Sigma> \<equiv>
  right_quotient ((kleene_star \<Sigma> - L1) \<inter> L2) (kleene_star \<Sigma>UC)
    = (kleene_star \<Sigma> - L1 ) \<inter> L2"

lemma rev_inj: "
  rev a = rev b
  \<Longrightarrow> a = b"
  apply(induct a arbitrary: b)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac a1 a2 b)(*strict*)
  apply(clarsimp)
  apply(case_tac b)
   apply(rename_tac a1 a2 b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a1 a2 b a list)(*strict*)
  apply(clarsimp)
  done

lemma left_quotient_to_right_quotient: "
  left_quotient A B = rev ` (right_quotient (rev ` B) (rev ` A))"
  apply(simp add: left_quotient_def right_quotient_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="rev x"
      in bexI)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="v"
      in bexI)
    apply(rename_tac x v)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="v@x"
      in bexI)
     apply(rename_tac x v)(*strict*)
     apply(force)
    apply(rename_tac x v)(*strict*)
    apply(force)
   apply(rename_tac x v)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac xa v xb)(*strict*)
  apply(rule_tac
      x="v"
      in bexI)
   apply(rename_tac xa v xb)(*strict*)
   apply(rule_tac
      t="v@rev xa"
      and s="xb"
      in ssubst)
    apply(rename_tac xa v xb)(*strict*)
    apply(rule rev_inj)
    apply(clarsimp)
   apply(rename_tac xa v xb)(*strict*)
   apply(force)
  apply(rename_tac xa v xb)(*strict*)
  apply(clarsimp)
  done

lemma right_quotient_to_left_quotient: "
  right_quotient A B = rev ` (left_quotient (rev ` B) (rev ` A))"
  apply(simp add: left_quotient_def right_quotient_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="rev x"
      in bexI)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="v"
      in bexI)
    apply(rename_tac x v)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="x@v"
      in bexI)
     apply(rename_tac x v)(*strict*)
     apply(force)
    apply(rename_tac x v)(*strict*)
    apply(force)
   apply(rename_tac x v)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac xa v xb)(*strict*)
  apply(rule_tac
      x="v"
      in bexI)
   apply(rename_tac xa v xb)(*strict*)
   apply(rule_tac
      t="rev xa@v"
      and s="xb"
      in ssubst)
    apply(rename_tac xa v xb)(*strict*)
    apply(rule rev_inj)
    apply(clarsimp)
   apply(rename_tac xa v xb)(*strict*)
   apply(force)
  apply(rename_tac xa v xb)(*strict*)
  apply(clarsimp)
  done

lemma apply_controllability: "
  append_alphabet A \<Sigma>UC \<inter> L \<subseteq> A
  \<Longrightarrow> w \<in> A
  \<Longrightarrow> u \<in> \<Sigma>UC
  \<Longrightarrow> w @ [u] \<in> L
  \<Longrightarrow> w @ [u] \<in> A"
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(force)
  done

lemma star_controllable_language_vs_controllable_language_hlp2: "
  L = prefix_closure L
  \<Longrightarrow> (append_alphabet A \<Sigma>UC) \<inter> L \<subseteq> A
  \<Longrightarrow> a @ b \<in> L
  \<Longrightarrow> a \<in> A
  \<Longrightarrow> b \<in> (kleene_star \<Sigma>UC)
  \<Longrightarrow> a @ b \<in> L \<and> set b \<subseteq> \<Sigma>UC \<longrightarrow> a @ b \<in> A"
  apply(rule_tac
      P="\<lambda>v. a @ v \<in> L \<and> set v \<subseteq> \<Sigma>UC \<longrightarrow> a @ v \<in> A"
      in rev_induct)
   apply(simp)
  apply(rename_tac x xs)(*strict*)
  apply(rule impI)
  apply(erule conjE)
  apply(erule impE)
   apply(rename_tac x xs)(*strict*)
   apply(rule conjI)
    apply(rename_tac x xs)(*strict*)
    apply(rule_tac
      L="L"
      and w="a @ xs"
      and v="[x]"
      in prefixExists)
     apply(rename_tac x xs)(*strict*)
     apply(simp)
    apply(rename_tac x xs)(*strict*)
    apply(simp)
   apply(rename_tac x xs)(*strict*)
   apply(simp)
  apply(rename_tac x xs)(*strict*)
  apply(simp)
  apply(drule_tac
      A="A"
      and \<Sigma>UC="\<Sigma>UC"
      and L="L"
      and w="a @ xs"
      and u="x"
      in apply_controllability)
     apply(rename_tac x xs)(*strict*)
     apply(force)
    apply(rename_tac x xs)(*strict*)
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(force)
  done

lemma star_controllable_language_vs_controllable_language_hlp1: "
  L = prefix_closure L
  \<Longrightarrow> (append_alphabet A \<Sigma>UC) \<inter> L \<subseteq> A
  \<Longrightarrow> x \<in> append_language A (kleene_star \<Sigma>UC)
  \<Longrightarrow> x \<in> L
  \<Longrightarrow> x \<in> A"
  apply(simp add: append_alphabet_def append_language_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a b)(*strict*)
   prefer 2
   apply(rule_tac
      L="L"
      and A="A"
      in star_controllable_language_vs_controllable_language_hlp2)
       apply(rename_tac a b)(*strict*)
       apply(force)
      apply(rename_tac a b)(*strict*)
      apply(simp add: append_alphabet_def append_language_def)
     apply(rename_tac a b)(*strict*)
     apply(force)
    apply(rename_tac a b)(*strict*)
    apply(force)
   apply(rename_tac a b)(*strict*)
   apply(force)
  apply(rename_tac a b)(*strict*)
  apply(erule impE)
   apply(rename_tac a b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b x)(*strict*)
  apply(simp add: kleene_star_def)
  apply(force)
  done

corollary star_controllable_language_implies_controllable_language: "
  star_controllable_language A \<Sigma>UC L
  \<Longrightarrow> controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_language_def controllable_language_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac v s)(*strict*)
  apply(force)
  done

corollary controllable_language_implies_star_controllable_language: "
  L = prefix_closure L
  \<Longrightarrow> controllable_language A \<Sigma>UC L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_language_def controllable_language_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule star_controllable_language_vs_controllable_language_hlp1)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

corollary star_controllable_language_vs_controllable_language: "
  L = prefix_closure L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L \<longleftrightarrow> controllable_language A \<Sigma>UC L"
  apply(rule antisym)
   apply(clarsimp)
   apply(rule star_controllable_language_implies_controllable_language)
   apply(force)
  apply(clarsimp)
  apply(rule controllable_language_implies_star_controllable_language)
   apply(force)
  apply(force)
  done

corollary star_controllable_language_implies_equal_star_controllable_language: "
  A \<subseteq> L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L
  \<Longrightarrow> equal_star_controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_language_def equal_star_controllable_language_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

corollary equal_star_controllable_language_implies_star_controllable_language: "
  equal_star_controllable_language A \<Sigma>UC L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_language_def equal_star_controllable_language_def)
  done

corollary star_controllable_language_vs_equal_star_controllable_language: "
  A \<subseteq> L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L = equal_star_controllable_language A \<Sigma>UC L"
  apply(rule antisym)
   apply(clarsimp)
   apply(rule star_controllable_language_implies_equal_star_controllable_language)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule equal_star_controllable_language_implies_star_controllable_language)
  apply(force)
  done

corollary right_quotient_controllable_language_implies_star_controllable_language: "
  L \<subseteq> kleene_star \<Sigma>
  \<Longrightarrow> right_quotient_controllable_language A \<Sigma>UC L \<Sigma>
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_language_def right_quotient_controllable_language_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp only: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(simp)
  apply(erule bexE)
  apply(rename_tac x a)(*strict*)
  apply(erule bexE)
  apply(rename_tac x a b)(*strict*)
  apply(simp)
  apply(rule_tac
      A="kleene_star \<Sigma>"
      and x="a@b"
      and B="A"
      in complementA)
   apply(rename_tac x a b)(*strict*)
   apply(rule_tac
      A="L"
      and B="kleene_star \<Sigma>"
      in set_rev_mp)
    apply(rename_tac x a b)(*strict*)
    apply(simp)
   apply(rename_tac x a b)(*strict*)
   apply(force)
  apply(rename_tac x a b)(*strict*)
  apply(simp add: right_quotient_def append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(blast)
  done

corollary star_controllable_language_implies_equal_right_quotient_controllable_language: "
  L = prefix_closure L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L
  \<Longrightarrow> equal_right_quotient_controllable_language A \<Sigma>UC L \<Sigma>"
  apply(simp only: star_controllable_language_def equal_right_quotient_controllable_language_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(simp add: right_quotient_def append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac x v)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: right_quotient_def append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  done

corollary equal_right_quotient_controllable_language_implies_right_quotient_controllable_language: "
  equal_right_quotient_controllable_language A \<Sigma>UC L \<Sigma>
  \<Longrightarrow> right_quotient_controllable_language A \<Sigma>UC L \<Sigma>"
  apply(simp add: equal_right_quotient_controllable_language_def right_quotient_controllable_language_def)
  done

end
