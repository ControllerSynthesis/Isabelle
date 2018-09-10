section {*control\_theory\_on\_languages*}
theory control_theory_on_languages

imports 
  PRJ_04__ENTRY

begin

definition nonblockingness_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "nonblockingness_language A B \<equiv>
  A \<subseteq> prefix_closure B"

lemma example1_nonblockingness_language: "
  nonblockingness_language {[0], [0, 1]} {[0, 1, 2]}"
  apply(simp add: nonblockingness_language_def prefix_closure_def prefix_def)
  done

lemma example2_nonblockingness_language: "
  \<not> nonblockingness_language {[0, 1, 2, 3], [0, 1, 2]} {[0, 1, 2]}"
  apply(simp add: nonblockingness_language_def prefix_closure_def prefix_def)
  done

lemma example3_nonblockingness_language: "
  \<not> nonblockingness_language {[1::nat]} {[0, 1, 2]}"
  apply(simp add: nonblockingness_language_def prefix_closure_def prefix_def)
  done

definition controllable_language :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "controllable_language A \<Sigma>UC L \<equiv>
  (append_alphabet A \<Sigma>UC) \<inter> L \<subseteq> A"

lemma example2_controllable_language: "
  controllable_language { [] , [ 0 ] } { 0 } { [ 0 ] }"
  apply(simp add: _controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  done

lemma example3_controllable_language: "
  \<not> controllable_language { [] } { 0 } { [ 0 ] }"
  apply(simp add: _controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  done

lemma example4_controllable_language: "
  controllable_language { [] , [ 1 ] , [ 1, 0 ] , [ 1, 0, 2 ] } { 0 } { [ 1, 0 ] }"
  apply(simp add: _controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  done

lemma example5_controllable_language: "
  \<not> controllable_language { [] , [ 1 ] , [ 1, 0, 2 ] } { 0 } { [ 1, 0 ] }"
  apply(simp add: _controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  done

definition controllable_word :: "
  '\<Sigma> list
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "controllable_word w Luc L A \<equiv>
  \<forall>u  \<in> Luc. w @ u  \<in> L \<longrightarrow> w @ u  \<in> A"

lemma example1_controllable_word: "
  controllable_word [] {[0]} (kleene_star {0,1}) {[],[0]}"
  apply(simp add: controllable_word_def kleene_star_def)
  done

lemma example2_controllable_word: "
  \<not> controllable_word [] (kleene_star {0}) (kleene_star {0,1}) {[],[0]}"
  apply(simp add: controllable_word_def kleene_star_def)
  apply(rule_tac
      x = "[0,0]"
      in exI)
  apply(clarsimp)
  done

theorem Soundness_of_Controllable_Word: "
  (\<forall>w  \<in> A. controllable_word w (alphabet_to_language \<Sigma>UC) L A) \<longleftrightarrow> controllable_language A \<Sigma>UC L"
  apply(simp add: controllable_word_def controllable_language_def append_alphabet_def alphabet_to_language_def append_language_def)
  apply(force)
  done

definition controllable_sublanguage :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> bool" where
  "controllable_sublanguage A1 Luc L A2 \<equiv>
  \<forall>w  \<in> A1. controllable_word w Luc L A2"

theorem Soundness_of_Controllable_Sublanguage: "
  controllable_sublanguage A (alphabet_to_language SU) L A \<longleftrightarrow> controllable_language A SU L"
  apply(simp add: alphabet_to_language_def controllable_language_def controllable_sublanguage_def append_alphabet_def append_language_def controllable_word_def)
  apply(force)
  done

lemma nonblockingness_languageclosedUnderSubset: "
  A\<subseteq>B
  \<Longrightarrow> nonblockingness_language B C
  \<Longrightarrow> nonblockingness_language A C"
  apply(simp add: nonblockingness_language_def)
  done

lemma nonblockingness_languagetriv: "
  nonblockingness_language (prefix_closure B) B"
  apply(simp add: nonblockingness_language_def prefix_closure_def prefix_def)
  done

lemma nonblockingness_language_sym: "
  nonblockingness_language A (A\<inter>B)
  \<Longrightarrow> nonblockingness_language A (B\<inter>A)"
  apply(rule_tac
      s = "A\<inter>B"
      and t = "B\<inter>A"
      in ssubst)
   apply(auto)
  done

definition Nonblockingness :: "'\<Sigma> list set \<Rightarrow> '\<Sigma> list set \<Rightarrow> bool" where
  "Nonblockingness A B \<equiv> (A = prefix_closure B)"

definition Nonblockingness2 :: "'\<Sigma> list set \<Rightarrow> '\<Sigma> list set \<Rightarrow> bool" where
  "Nonblockingness2 A B \<equiv> (A\<supseteq> prefix_closure B)"

lemma nonblockingness_language_subset: "
  nonblockingness_language A' B
  \<Longrightarrow> A \<subseteq> A'
  \<Longrightarrow> nonblockingness_language A B"
  apply(simp add: nonblockingness_language_def)
  done

lemma NonblockingnessI: "
  nonblockingness_language A B
  \<Longrightarrow> Nonblockingness2 A B
  \<Longrightarrow> Nonblockingness A B"
  apply(simp add: Nonblockingness_def nonblockingness_language_def Nonblockingness2_def)
  done

lemma NonblockingnessE1: "
  Nonblockingness A B
  \<Longrightarrow> nonblockingness_language A B"
  apply(simp add: Nonblockingness_def nonblockingness_language_def)
  done

lemma NonblockingnessE2: "
  Nonblockingness A B
  \<Longrightarrow> Nonblockingness2 A B"
  apply(simp add: Nonblockingness_def Nonblockingness2_def)
  done

lemma nonblockingness_language_and_Nonblockingness2_EQ: "
  nonblockingness_language A B
  \<Longrightarrow> Nonblockingness2 A B
  \<Longrightarrow> A=prefix_closure B"
  apply(simp add: nonblockingness_language_def Nonblockingness2_def)
  done

lemma nonblockingness_language_to_perfect_langBF: "
  nonblockingness_language UM M
  \<Longrightarrow> M \<subseteq> UM
  \<Longrightarrow> prefix_closure UM = UM
  \<Longrightarrow> UM = prefix_closure M"
  apply(simp add: nonblockingness_language_def)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_closure_def)
  apply(force)
  done

lemma prefix_closure_closed_sets_closed_under_intersection: "
  A = prefix_closure A
  \<Longrightarrow> B = prefix_closure B
  \<Longrightarrow> prefix_closure (A \<inter> B) = A \<inter> B"
  apply(simp add: prefix_def prefix_closure_def)
  apply(rule order_antisym)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(force)
  done

lemma Cont_vs_controllable_word_strict_case: "
  controllable_sublanguage ((prefix_closure{x}) - {x}) X Y Z \<longleftrightarrow> (\<forall>w. strict_prefix w x \<longrightarrow> controllable_word w X Y Z) "
  apply(rule order_antisym)
   apply(simp add: controllable_sublanguage_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(erule_tac
      x="w"
      in ballE)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: prefix_closure_def prefix_def strict_prefix_def)
   apply(erule disjE)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(simp add: controllable_sublanguage_def)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(case_tac "strict_prefix w' x")
   apply(rename_tac w')(*strict*)
   apply(force)
  apply(rename_tac w')(*strict*)
  apply(simp add: prefix_closure_def prefix_def strict_prefix_def)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(rename_tac w')(*strict*)
   apply(force)
  apply(rename_tac w' ys y)(*strict*)
  apply(force)
  done

lemma controllable_sublanguage_vs_controllable_word_strict_case1: "
  controllable_sublanguage ((prefix_closure{x}) - {x}) X Y Z
  \<Longrightarrow> (\<forall>w. strict_prefix w x \<longrightarrow> controllable_word w X Y Z) "
  apply (metis Cont_vs_controllable_word_strict_case)
  done

lemma preserve_controllable_language: "
  (\<And>B. B \<in> C
    \<Longrightarrow> (append_alphabet (prefix_closure B) \<Sigma>UC) \<inter> L \<subseteq> (prefix_closure B))
  \<Longrightarrow> (append_alphabet (prefix_closure (\<Union> C)) \<Sigma>UC) \<inter> L \<subseteq> prefix_closure (\<Union> C)"
  apply(rule_tac
      P="\<lambda>x. (append_alphabet x \<Sigma>UC) \<inter> L \<subseteq> x"
      and t="prefix_closure (\<Union>C)"
      and s="prefix_closure (\<Union>{A. \<exists>B. B\<in> C \<and> A = B})"
      in ssubst)
   apply(force)
  apply(rule_tac
      P="\<lambda>x. (append_alphabet x \<Sigma>UC) \<inter> L \<subseteq> x"
      and t="prefix_closure (\<Union>{A. \<exists>B. B\<in> C \<and> A = B})"
      and s="\<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure B)}"
      in ssubst)
   apply(simp add: prefix_closure_def prefix_def)
   apply(thin_tac "(\<And>B. B \<in> C \<Longrightarrow> append_alphabet {w. \<exists>v. v \<in> B \<and> (\<exists>c. w @ c = v)} \<Sigma>UC \<inter> L \<subseteq> {w. \<exists>v. v \<in> B \<and> (\<exists>c. w @ c = v)})")
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x X c)(*strict*)
    apply(rule_tac
      x="{w. \<exists>v. v \<in> X \<and> (\<exists>c. w @ c = v)}"
      in exI)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x B c)(*strict*)
   apply(rule_tac
      x="x@c"
      in exI)
   apply(force)
  apply(rule_tac
      P="\<lambda>x. x \<inter> L \<subseteq> (\<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure B)})"
      and t="append_alphabet (\<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure B)}) \<Sigma>UC"
      and s="\<Union>{A. \<exists>B. B\<in> C \<and> A = append_alphabet (prefix_closure B) \<Sigma>UC}"
      in ssubst)
   apply (simp add: append_alphabet_def append_language_def alphabet_to_language_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac v B s)(*strict*)
    apply(rule_tac
      x="{w. \<exists>v\<in> prefix_closure B. \<exists>s\<in> \<Sigma>UC. w = v @ [s]}"
      in exI)
    apply(blast)
   apply(clarsimp)
   apply(rename_tac B v s)(*strict*)
   apply(rule_tac
      x="prefix_closure B"
      in exI)
   apply(blast)
  apply(rule_tac
      P="\<lambda>x. x \<subseteq> (\<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure B)})"
      and t="\<Union>{A. \<exists>B. B\<in> C \<and> A = append_alphabet (prefix_closure B) \<Sigma>UC} \<inter> L"
      and s="\<Union>{A. \<exists>B. B\<in> C \<and> A = (append_alphabet (prefix_closure B) \<Sigma>UC) \<inter> L}"
      in ssubst)
   apply (metis Int_commute UN_eq UN_extend_simps(4))
  apply(clarsimp)
  apply(rename_tac x B)(*strict*)
  apply(erule_tac
      x="B"
      in meta_allE)
  apply(clarsimp)
  apply(rule_tac
      x="(prefix_closure B)"
      in exI)
  apply(rule conjI)
   apply(rename_tac x B)(*strict*)
   apply(rule_tac
      x="B"
      in exI)
   apply(clarsimp)
  apply(rename_tac x B)(*strict*)
  apply(force)
  done

lemma preserve_controllable_language2: "
  (\<And>B. B \<in> C
    \<Longrightarrow> controllable_language (prefix_closure B) \<Sigma>UC L)
    \<Longrightarrow> controllable_language (prefix_closure (\<Union> C)) \<Sigma>UC L"
  apply(simp add: controllable_language_def)
  apply(rule preserve_controllable_language)
  apply(rename_tac B)(*strict*)
  apply(force)
  done

lemma Sup_Cont_contained_lang: "
  (\<And>X. X\<in> A \<Longrightarrow> controllable_language X SigmaUC P)
  \<Longrightarrow> controllable_language (Sup A) SigmaUC P"
  apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def append_alphabet_def append_language_def alphabet_to_language_def controllable_language_def)
  apply(clarsimp)
  apply(rename_tac a v s)(*strict*)
  apply(erule_tac
      x="a"
      in meta_allE)
  apply(clarsimp)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac a v s)(*strict*)
   apply(force)
  apply(rename_tac a v s)(*strict*)
  apply(force)
  done

lemma contSubset2: "
  controllable_language A \<Sigma>UC L
  \<Longrightarrow> controllable_language (A \<inter> L) \<Sigma>UC L"
  apply(simp add: controllable_language_def)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(force)
  done

lemma preservePrec: "
  (\<And>B. B \<in> C \<Longrightarrow> B = prefix_closure B)
  \<Longrightarrow> \<Union> C = prefix_closure (\<Union> C)"
  apply(subgoal_tac "\<Union>C = \<Union>{A. \<exists>B. B\<in> C \<and> A = B}")
   prefer 2
   apply(force)
  apply(subgoal_tac "prefix_closure (\<Union>{A. \<exists>B. B\<in> C \<and> A = B}) = \<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure B)}")
   prefer 2
   apply (simp add: prefix_closure_def prefix_def)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac x xa c)(*strict*)
    apply(erule_tac
      x="xa"
      in meta_allE)
    apply(clarsimp)
    apply(rule_tac
      x="{w. \<exists>v. v \<in> xa \<and> (\<exists>c. w @ c = v)}"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac x xa c)(*strict*)
     apply(rule_tac
      x="xa"
      in exI)
     apply(force)
    apply(rename_tac x xa c)(*strict*)
    apply(force)
   apply(force)
  apply(force)
  done

theorem precCanBePulledIn: "
  \<Union> {A. P A \<and> A = prefix_closure A}
  = prefix_closure (\<Union> {A. P (prefix_closure A)})"
  apply(rule_tac
      P="\<lambda>x. x=prefix_closure (\<Union>{A. P (prefix_closure A)})"
      and s="prefix_closure(\<Union>{A. P A \<and> A = prefix_closure A})"
      in ssubst)
   apply(rule preservePrec)
   apply(rename_tac B)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_closure_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x v xa)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(rule conjI)
    apply(rename_tac x v xa)(*strict*)
    apply(rule_tac
      x="xa"
      in exI)
    apply(simp)
   apply(rename_tac x v xa)(*strict*)
   apply(simp)
  apply(clarsimp)
  apply(rename_tac x v xa)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(rule conjI)
   apply(rename_tac x v xa)(*strict*)
   apply(rule_tac
      x="prefix_closure{w. \<exists>v. v \<in> xa \<and> w \<sqsubseteq> v}"
      in exI)
   apply(rule conjI)
    apply(rename_tac x v xa)(*strict*)
    apply(fold prefix_closure_def)
    apply(rule_tac
      P="\<lambda>x. P x"
      and s="prefix_closure xa"
      in ssubst)
     apply(rename_tac x v xa)(*strict*)
     apply(rule sym)
     apply(rule prefix_closure_idempotent)
    apply(rename_tac x v xa)(*strict*)
    apply(simp)
   apply(rename_tac x v xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac x v xa)(*strict*)
    apply(rule prefix_closure_idempotent)
   apply(rename_tac x v xa)(*strict*)
   apply(rule_tac
      A="xa"
      in set_mp)
    apply(rename_tac x v xa)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(blast)
   apply(rename_tac x v xa)(*strict*)
   apply(blast)+
  done

lemma preservePrecNonBlock: "
  (\<And>B. B \<in> C \<Longrightarrow> B = prefix_closure B \<and> B \<subseteq> prefix_closure (D \<inter> B))
  \<Longrightarrow> \<Union> C \<subseteq> prefix_closure (D \<inter> \<Union> C)"
  apply(rule_tac
      P="\<lambda> x . \<Union>x \<subseteq> prefix_closure (D \<inter> \<Union>x)"
      and t="C"
      and s="{A. \<exists>B. B \<in> C \<and> A = B}"
      in ssubst)
   apply(force)
  apply(rule_tac
      P="\<lambda> x . \<Union>{A. \<exists>B. B \<in> C \<and> A = B} \<subseteq> prefix_closure x"
      and t="D\<inter>\<Union>{A. \<exists>B. B \<in> C \<and> A = B}"
      and s="(\<Union>{A. \<exists>B. B\<in> C \<and> A = D \<inter> B})"
      in ssubst)
   apply(blast)
  apply(rule_tac
      P="\<lambda> x . \<Union>{A. \<exists>B. B \<in> C \<and> A = B} \<subseteq> x"
      and t="prefix_closure(\<Union>{A. \<exists>B. B\<in> C \<and> A = D \<inter> B})"
      and s="\<Union>{A. \<exists>B. B\<in> C \<and> A = (prefix_closure (D \<inter> B))}"
      in ssubst)
   apply(simp add: prefix_closure_def prefix_def)
   apply(blast)
  apply(rule Union_mono)
  apply(rule_tac
      A="{A. \<exists>B. B \<in> C \<and> A = B}"
      and B="{A. \<exists>B. B \<in> C \<and> A = prefix_closure (D \<inter> B)}"
      in subsetI)
  apply(rename_tac x)(*strict*)
  apply(simp)
  apply(rule_tac
      x="prefix_closure x"
      in exI)
  apply(simp add: prefix_closure_def prefix_def)
  apply(blast)
  done

corollary preservePrecNonBlock_3: "
  (\<And>B. B \<in> C \<Longrightarrow> nonblockingness_language B D)
  \<Longrightarrow> nonblockingness_language (\<Union> C) D"
  apply(subgoal_tac "C = {A. A\<in> C \<and> nonblockingness_language A D}")
   prefer 2
   apply(rule equalityI)
    apply(rule subsetI)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(simp add: nonblockingness_language_def)
  apply(clarsimp)
  apply(rename_tac x X)(*strict*)
  apply(rule_tac
      A="X"
      in set_mp)
   apply(rename_tac x X)(*strict*)
   apply(fold nonblockingness_language_def)
   apply(force)
  apply(rename_tac x X)(*strict*)
  apply(force)
  done

lemma helpLem: "
  \<forall>C. P C \<longrightarrow> (C = prefix_closure C
              \<and> C \<subseteq> prefix_closure (B \<inter> C)
              \<and> controllable_language C \<Sigma>UC L)
  \<Longrightarrow> controllable_language (prefix_closure (B \<inter> \<Union> Collect P)) \<Sigma>UC L"
  apply(simp add: controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac v s)(*strict*)
  apply(rule_tac
      A="\<Union>Collect P"
      in set_mp)
   apply(rename_tac v s)(*strict*)
   apply(rule preservePrecNonBlock)
   apply(rename_tac v s Ba)(*strict*)
   apply(simp)
  apply(rename_tac v s)(*strict*)
  apply(rule_tac
      A="prefix_closure (\<Union>(Collect P))"
      in set_mp)
   apply(rename_tac v s)(*strict*)
   apply(subgoal_tac "prefix_closure (\<Union>Collect P) = \<Union>Collect P")
    apply(rename_tac v s)(*strict*)
    apply(blast)
   apply(rename_tac v s)(*strict*)
   apply(rule sym)
   apply(rule preservePrec)
   apply(rename_tac v s Ba)(*strict*)
   apply(blast)
  apply(rename_tac v s)(*strict*)
  apply(subgoal_tac "v\<in> prefix_closure (\<Union>Collect P)")
   apply(rename_tac v s)(*strict*)
   apply(subgoal_tac "controllable_language (prefix_closure(\<Union>Collect P)) \<Sigma>UC L")
    apply(rename_tac v s)(*strict*)
    apply(simp add: controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
    apply(blast)
   apply(rename_tac v s)(*strict*)
   apply(simp add: controllable_language_def)
   apply(rule_tac
      C="(Collect P)"
      and \<Sigma>UC="\<Sigma>UC"
      and L="L"
      in preserve_controllable_language)
   apply(rename_tac v s Ba)(*strict*)
   apply(simp add: append_alphabet_def prefix_closure_def prefix_def append_language_def alphabet_to_language_def)
  apply(rename_tac v s)(*strict*)
  apply(rule_tac
      A="prefix_closure (B \<inter> \<Union>Collect P)"
      in set_mp)
   apply(rename_tac v s)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(blast)
  apply(rename_tac v s)(*strict*)
  apply(blast)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_2: "
  Pum = prefix_closure Pum
  \<Longrightarrow> a = prefix_closure a
  \<Longrightarrow> a \<inter> Pum = prefix_closure (a \<inter> Pum)"
  apply(rule sym)
  apply(rule prefix_closure_intersection3)
   apply(simp)+
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_3: "
  b \<inter> Pm \<subseteq> Sm
  \<Longrightarrow> a \<inter> Pum \<subseteq> prefix_closure (b\<inter>Pm)
  \<Longrightarrow> Pum = prefix_closure Pum
  \<Longrightarrow> a = prefix_closure a
  \<Longrightarrow> Pm \<subseteq> Pum
  \<Longrightarrow> b \<subseteq> a
  \<Longrightarrow> a \<inter> Pum \<subseteq> prefix_closure ((Pm \<inter> Sm) \<inter> (a \<inter> Pum))"
  apply(rule_tac
      A="a \<inter> Pum"
      and B="prefix_closure (b \<inter> Pm)"
      and C="(prefix_closure (Pm\<inter> Sm \<inter> (a \<inter> Pum)))"
      in subset_trans)
   apply(simp)
  apply(rule_tac
      A="prefix_closure(b \<inter> Pm)"
      and B="(prefix_closure (Pm\<inter> Sm \<inter> (b \<inter> Pm)))"
      and C="(prefix_closure (Pm\<inter>Sm \<inter> (a \<inter> Pum)))"
      in subset_trans)
   apply(rule prefix_closure_preserves_subseteq)
   apply(rule Set.Int_greatest)
    apply(rule Set.Int_greatest)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rule prefix_closure_preserves_subseteq)
  apply(rule Set.Int_greatest)
   apply(rule Set.Int_greatest)
    apply(blast)
   apply(blast)
  apply(rule Set.Int_greatest)
   apply(blast)
  apply(blast)
  done

lemma controllable_language_infimum: "
  controllable_language C'um \<Sigma>UC Pum
  \<Longrightarrow> controllable_language (C'um \<inter> Pum) \<Sigma>UC Pum"
  apply(simp add: controllable_language_def append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac a v)(*strict*)
  apply(rule_tac
      A="{w. \<exists>a\<in> C'um. \<exists>b. (\<exists>v\<in> \<Sigma>UC. b = [v]) \<and> w = a @ b} \<inter> Pum"
      in set_mp)
   apply(rename_tac a v)(*strict*)
   apply(force)
  apply(rename_tac a v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac a v)(*strict*)
   apply(force)
  apply(rename_tac a v)(*strict*)
  apply(force)
  done

lemma prefix_closedness_closed_under_union: "
  prefix_closure A = A
  \<Longrightarrow> prefix_closure B = B
  \<Longrightarrow> prefix_closure (A \<union> B) = A \<union> B"
  apply(simp add: prefix_closure_def prefix_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(erule disjE)
    apply(rename_tac x c)(*strict*)
    apply(force)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(force)
  done

lemma SCP_UPsol_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_hlp2_1: "
  b \<inter> Pm \<subseteq> Sm
  \<Longrightarrow> a \<inter> Pum \<subseteq> prefix_closure (b \<inter> Pm)
  \<Longrightarrow> a \<inter> Pum \<subseteq> prefix_closure (Pm \<inter> Sm)"
  apply(rule_tac
      A="a \<inter> Pum"
      and B="prefix_closure(b \<inter> Pm)"
      and C="prefix_closure (Pm \<inter> Sm)"
      in subset_trans)
   apply(simp)
  apply(rule prefix_closure_preserves_subseteq)
  apply(simp)
  done

end
