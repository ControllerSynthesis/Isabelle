section {*control\_theory\_on\_languages\_\_characterization\_of\_controllable\_sublanguage*}
theory
  control_theory_on_languages__characterization_of_controllable_sublanguage

imports
  control_theory_on_languages__alternative_characterization_of_controllable_language

begin

definition controllable_subset :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "controllable_subset A \<Sigma>UC L \<equiv>
  {w \<in> A. controllable_sublanguage (prefix_closure {w}) (alphabet_to_language \<Sigma>UC) L A}"

definition star_controllable_subset :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "star_controllable_subset A \<Sigma>UC L \<equiv>
  {w \<in> A. controllable_sublanguage (prefix_closure {w}) (kleene_star \<Sigma>UC) L A}"

corollary star_controllable_subset_unequal_to_controllable_subset: "
  A = {[],[u]}
  \<Longrightarrow> L = {[],[u],[u,u]}
  \<Longrightarrow> \<Sigma>UC = {u}
  \<Longrightarrow> controllable_subset A \<Sigma>UC L = {[]}
  \<and> star_controllable_subset A \<Sigma>UC L = {}"
  apply(unfold star_controllable_subset_def controllable_subset_def)
  apply(rule conjI)
   apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(erule_tac
      x="[u]"
      in allE)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
  apply(case_tac "x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a list)(*strict*)
  apply(erule_tac
      x="[u]"
      in allE)
  apply(clarsimp)
  apply(force)
  done

corollary star_controllable_subset_is_subset_of_controllable_subset: "
  star_controllable_subset A \<Sigma>UC L \<subseteq> controllable_subset A \<Sigma>UC L"
  apply(unfold star_controllable_subset_def controllable_subset_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
  apply(clarsimp)
  done

definition uncontrollable_subset :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "uncontrollable_subset A \<Sigma>UC \<Sigma> L \<equiv>
  append_language
    ((right_quotient (L - A) (alphabet_to_language \<Sigma>UC)) \<inter> A)
    (kleene_star \<Sigma>)"

definition star_uncontrollable_subset :: "
  '\<Sigma> list set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> set
  \<Rightarrow> '\<Sigma> list set
  \<Rightarrow> '\<Sigma> list set" where
  "star_uncontrollable_subset A \<Sigma>UC \<Sigma> L \<equiv>
  append_language
    ((right_quotient (L - A) (kleene_star \<Sigma>UC)) \<inter> A)
    (kleene_star \<Sigma>)"

corollary controllable_subset_prefix_closed: "
  A = prefix_closure A
  \<Longrightarrow> controllable_subset A \<Sigma>UC L = prefix_closure (controllable_subset A \<Sigma>UC L)"
  apply(simp add: controllable_subset_def prefix_closure_def controllable_sublanguage_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(rule conjI)
   apply(rename_tac x v)(*strict*)
   apply(blast)
  apply(rename_tac x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v w)(*strict*)
  apply(simp add: controllable_word_def prefix_def)
  apply(clarsimp)
  done

corollary star_controllable_subset_prefix_closed: "
  A = prefix_closure A
  \<Longrightarrow> star_controllable_subset A \<Sigma>UC L = prefix_closure (star_controllable_subset A \<Sigma>UC L)"
  apply(simp add: star_controllable_subset_def prefix_closure_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(rule conjI)
   apply(rename_tac x v)(*strict*)
   apply(blast)
  apply(rename_tac x v)(*strict*)
  apply(simp add: controllable_word_def prefix_def controllable_sublanguage_def)
  apply(clarsimp)
  done

corollary uncontrollable_subset_extension_closed: "
  set x \<subseteq> \<Sigma>
  \<Longrightarrow> prefix w' x
  \<Longrightarrow> w' \<in> uncontrollable_subset A \<Sigma>UC \<Sigma> L
  \<Longrightarrow> x \<in> uncontrollable_subset A \<Sigma>UC \<Sigma> L"
  apply(simp add: uncontrollable_subset_def append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac a b)(*strict*)
   apply(simp add: prefix_def)
   apply(erule exE)
   apply(rename_tac a b c)(*strict*)
   apply(rule_tac
      x="b@c"
      in exI)
   apply(clarsimp)
   apply(rename_tac a b c x)(*strict*)
   apply(blast)
  apply(rename_tac a b)(*strict*)
  apply(blast)
  done

corollary star_uncontrollable_subset_extension_closed: "
  set x \<subseteq> \<Sigma>
  \<Longrightarrow> prefix w' x
  \<Longrightarrow> w' \<in> star_uncontrollable_subset A \<Sigma>UC \<Sigma> L
  \<Longrightarrow> x \<in> star_uncontrollable_subset A \<Sigma>UC \<Sigma> L"
  apply(simp add: star_uncontrollable_subset_def append_alphabet_def append_language_def alphabet_to_language_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac a b)(*strict*)
   apply(simp add: prefix_def)
   apply(erule exE)
   apply(rename_tac a b c)(*strict*)
   apply(rule_tac
      x="b@c"
      in exI)
   apply(clarsimp)
   apply(rename_tac a b c x)(*strict*)
   apply(blast)
  apply(rename_tac a b)(*strict*)
  apply(blast)
  done

lemma apply_controllability2: "
  append_language A (kleene_star \<Sigma>UC) \<inter> L \<subseteq> A
  \<Longrightarrow> w \<in> A
  \<Longrightarrow> u \<in> (kleene_star \<Sigma>UC)
  \<Longrightarrow> w @ u \<in> L
  \<Longrightarrow> w @ u \<in> A"
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(force)
  done

corollary controllable_subset_FP_implies_controllable_language: "
  A = prefix_closure A
  \<Longrightarrow> A = controllable_subset A \<Sigma>UC L
  \<Longrightarrow> controllable_language A \<Sigma>UC L"
  apply(simp add: controllable_subset_def controllable_language_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def prefix_closure_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac v s)(*strict*)
  apply(subgoal_tac "\<forall>w'. w' \<sqsubseteq> v \<longrightarrow> (\<forall>x\<in> \<Sigma>UC. w' @ [x] \<in> L \<longrightarrow> w' @ [x] \<in> A)")
   apply(rename_tac v s)(*strict*)
   apply(erule_tac
      x="v"
      in allE)
   apply(erule impE)
    apply(rename_tac v s)(*strict*)
    apply(rule prefix_reflexive)
   apply(rename_tac v s)(*strict*)
   apply(erule_tac
      x="s"
      in ballE)
    apply(rename_tac v s)(*strict*)
    apply(clarsimp)
   apply(rename_tac v s)(*strict*)
   apply(clarsimp)
  apply(rename_tac v s)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac s w' x c)(*strict*)
  apply(subgoal_tac "w' \<in> A")
   apply(rename_tac s w' x c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac s w' x c)(*strict*)
  apply(subgoal_tac "w' \<in> {w \<in> A. \<forall>wa. (\<exists>c. wa @ c = w) \<longrightarrow> (\<forall>u. (\<exists>v\<in> \<Sigma>UC. u = [v]) \<longrightarrow> wa @ u \<in> L \<longrightarrow> wa @ u \<in> A)}")
   apply(rename_tac s w' x c)(*strict*)
   prefer 2
   apply(rule_tac
      t="{w \<in> A. \<forall>wa. (\<exists>c. wa @ c = w) \<longrightarrow> (\<forall>u. (\<exists>v\<in> \<Sigma>UC. u = [v]) \<longrightarrow> wa @ u \<in> L \<longrightarrow> wa @ u \<in> A)}"
      and s="A"
      in ssubst)
    apply(rename_tac s w' x c)(*strict*)
    apply(force)
   apply(rename_tac s w' x c)(*strict*)
   apply(force)
  apply(rename_tac s w' x c)(*strict*)
  apply(simp (no_asm_use))
  apply(erule conjE)+
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac s w' x c)(*strict*)
   apply(force)
  apply(rename_tac s w' x c)(*strict*)
  apply(clarsimp)
  done

corollary controllable_language_implies_star_controllable_subset_FP: "
  L = prefix_closure L
  \<Longrightarrow> A = prefix_closure A
  \<Longrightarrow> controllable_language A \<Sigma>UC L
  \<Longrightarrow> A = star_controllable_subset A \<Sigma>UC L"
  apply(subgoal_tac "((append_language A (kleene_star \<Sigma>UC)) \<inter> L \<subseteq> A)")
   prefer 2
   apply(unfold controllable_language_def)
   apply(rule_tac
      Q="(((append_alphabet A \<Sigma>UC) \<inter> L) \<subseteq> A)"
      in HOL.iffD1)
    apply(rule sym)
    apply(fold star_controllable_language_def controllable_language_def)
    apply(rule star_controllable_language_vs_controllable_language)
    apply(force)
   apply(force)
  apply(unfold star_controllable_subset_def)
  apply(simp add: controllable_word_def prefix_def controllable_sublanguage_def)
  apply(rule equalityI)
   prefer 2
   apply(blast)
  apply(clarsimp)
  apply(rename_tac x w' xa)(*strict*)
  apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and L="L"
      in apply_controllability2)
     apply(rename_tac x w' xa)(*strict*)
     apply(simp add: star_controllable_language_def controllable_language_def)
    apply(rename_tac x w' xa)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(blast)
   apply(rename_tac x w' xa)(*strict*)
   apply(blast)
  apply(rename_tac x w' xa)(*strict*)
  apply(blast)
  done

corollary star_controllable_language_implies_controllable_subset_FP: "
  L = prefix_closure L
  \<Longrightarrow> A = prefix_closure A
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L
  \<Longrightarrow> A = controllable_subset A \<Sigma>UC L"
  apply(subgoal_tac "((append_alphabet A \<Sigma>UC) \<inter> L \<subseteq> A)")
   prefer 2
   apply(unfold star_controllable_language_def)
   apply(rule_tac
      Q="(((append_language A (kleene_star \<Sigma>UC)) \<inter> L) \<subseteq> A)"
      in HOL.iffD1)
    apply(fold star_controllable_language_def controllable_language_def)
    apply(rule star_controllable_language_vs_controllable_language)
    apply(simp)+
  apply(unfold controllable_subset_def)
  apply(simp add: controllable_word_def prefix_def controllable_sublanguage_def)
  apply(rule equalityI)
   prefer 2
   apply(blast)
  apply(clarsimp)
  apply(rename_tac x w' xa)(*strict*)
  apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and L="L"
      in apply_controllability2)
     apply(rename_tac x w' xa)(*strict*)
     apply(simp add: star_controllable_language_def controllable_language_def alphabet_to_language_def)
    apply(rename_tac x w' xa)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(blast)
   apply(rename_tac x w' xa)(*strict*)
   apply(simp add: star_controllable_language_def controllable_language_def alphabet_to_language_def kleene_star_def)
   apply(clarsimp)
  apply(rename_tac x w' xa)(*strict*)
  apply(blast)
  done

corollary star_controllable_subset_FP_implies_star_controllable_language: "
  A = prefix_closure A
  \<Longrightarrow> A = star_controllable_subset A \<Sigma>UC L
  \<Longrightarrow> star_controllable_language A \<Sigma>UC L"
  apply(simp add: star_controllable_subset_def star_controllable_language_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: append_alphabet_def append_language_def alphabet_to_language_def)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(subgoal_tac "\<forall>w'. w' \<sqsubseteq> a \<longrightarrow> (\<forall>x\<in> kleene_star \<Sigma>UC. w' @ x \<in> L \<longrightarrow> w' @ x \<in> A)")
   apply(rename_tac a b)(*strict*)
   apply(erule_tac
      x="a"
      in allE)
   apply(erule impE)
    apply(rename_tac a b)(*strict*)
    apply(rule prefix_reflexive)
   apply(rename_tac a b)(*strict*)
   apply(erule_tac
      x="b"
      in ballE)
    apply(rename_tac a b)(*strict*)
    apply(clarsimp)
   apply(rename_tac a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(simp add: prefix_def prefix_closure_def controllable_sublanguage_def controllable_word_def kleene_star_def)
  apply(clarsimp)
  apply(rename_tac b w' c x)(*strict*)
  apply(subgoal_tac "w' \<in> A")
   apply(rename_tac b w' c x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac b w' c x)(*strict*)
  apply(subgoal_tac "w' \<in> {w \<in> A. \<forall>wa. (\<exists>c. wa @ c = w) \<longrightarrow> (\<forall>u. set u \<subseteq> \<Sigma>UC \<longrightarrow> wa @ u \<in> L \<longrightarrow> wa @ u \<in> A)}")
   apply(rename_tac b w' c x)(*strict*)
   prefer 2
   apply(rule_tac
      t="{w \<in> A. \<forall>wa. (\<exists>c. wa @ c = w) \<longrightarrow> (\<forall>u. set u \<subseteq> \<Sigma>UC \<longrightarrow> wa @ u \<in> L \<longrightarrow> wa @ u \<in> A)}"
      and s="A"
      in ssubst)
    apply(rename_tac b w' c x)(*strict*)
    apply(force)
   apply(rename_tac b w' c x)(*strict*)
   apply(force)
  apply(rename_tac b w' c x)(*strict*)
  apply(simp (no_asm_use))
  apply(erule conjE)+
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac b w' c x)(*strict*)
   apply(force)
  apply(rename_tac b w' c x)(*strict*)
  apply(clarsimp)
  done

corollary controllable_subset_vs_uncontrollable_subset: "
  A = prefix_closure A
  \<Longrightarrow> A \<subseteq> kleene_star \<Sigma>
  \<Longrightarrow> controllable_subset A \<Sigma>UC L = A - uncontrollable_subset A \<Sigma>UC \<Sigma> L"
  apply(rule equalityI)
   apply(simp add: controllable_subset_def uncontrollable_subset_def append_alphabet_def append_language_def alphabet_to_language_def right_quotient_def prefix_def controllable_word_def)
   apply(simp add: controllable_word_def prefix_def controllable_sublanguage_def kleene_star_def prefix_closure_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: controllable_subset_def uncontrollable_subset_def append_language_def alphabet_to_language_def prefix_def right_quotient_def controllable_word_def kleene_star_def controllable_sublanguage_def prefix_closure_def)
  apply(clarsimp)
  apply(rename_tac w' c xa)(*strict*)
  apply(case_tac "w'@[xa]\<in> A")
   apply(rename_tac w' c xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(erule_tac
      x="w'"
      in ballE)
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      in allE)
   apply(erule impE)
    apply(rename_tac w' xa c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w' xa c)(*strict*)
   apply(force)
  apply(rename_tac w' xa c)(*strict*)
  apply(clarsimp)
  apply(erule_tac disjE)
   apply(rename_tac w' xa c)(*strict*)
   apply(erule_tac
      x="[c]"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac w' xa c)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(subgoal_tac "w'\<in> A")
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(rule prefixAlsoIn)
    apply(rename_tac w' xa c)(*strict*)
    apply(blast)
   apply(rename_tac w' xa c)(*strict*)
   apply(blast)
  apply(rename_tac w' xa c)(*strict*)
  apply(rule prefix_append)
  done

corollary star_controllable_subset_vs_star_uncontrollable_subset: "
  A = prefix_closure A
  \<Longrightarrow> A \<subseteq> kleene_star \<Sigma>
  \<Longrightarrow> star_controllable_subset A \<Sigma>UC L = A - star_uncontrollable_subset A \<Sigma>UC \<Sigma> L"
  apply(rule equalityI)
   apply(simp add: star_controllable_subset_def star_uncontrollable_subset_def append_alphabet_def append_language_def alphabet_to_language_def right_quotient_def prefix_def)
   apply(clarsimp)
   apply(rename_tac a b v)(*strict*)
   apply(simp add: controllable_word_def prefix_def controllable_sublanguage_def kleene_star_def prefix_closure_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: star_controllable_subset_def star_uncontrollable_subset_def append_alphabet_def append_language_def alphabet_to_language_def right_quotient_def prefix_def controllable_word_def controllable_sublanguage_def kleene_star_def prefix_closure_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(case_tac "w'@c\<in> A")
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(erule_tac
      x="w'"
      in ballE)
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      in allE)
   apply(rename_tac w' xa c)(*strict*)
   apply(force)
  apply(rename_tac w' xa c)(*strict*)
  apply(subgoal_tac "w'@c \<in> (kleene_star \<Sigma>)")
   apply(rename_tac w' xa c)(*strict*)
   apply(simp add: kleene_star_def)
   apply(rename_tac w' xa c)(*strict*)
   apply(force)
  apply(rename_tac w' xa c)(*strict*)
  apply(clarsimp)
  apply(erule_tac disjE)
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(subgoal_tac "w'\<in> A")
   apply(rename_tac w' xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' xa c)(*strict*)
  apply(rule prefixAlsoIn)
    apply(rename_tac w' xa c)(*strict*)
    apply(blast)
   apply(rename_tac w' xa c)(*strict*)
   apply(blast)
  apply(rename_tac w' xa c)(*strict*)
  apply(rule prefix_append)
  done

definition supremal_controllable_language :: "'\<Sigma> list set \<Rightarrow> '\<Sigma> set \<Rightarrow> '\<Sigma> list set \<Rightarrow> '\<Sigma> list set" where
  "supremal_controllable_language A \<Sigma>UC L =
  \<Union>{A'. prefix_closure A' = A' \<and> A' \<subseteq> A \<and> controllable_language A' \<Sigma>UC L}"

definition supremal_star_controllable_language :: "'\<Sigma> list set \<Rightarrow> '\<Sigma> set \<Rightarrow> '\<Sigma> list set \<Rightarrow> '\<Sigma> list set" where
  "supremal_star_controllable_language A \<Sigma>UC L =
  \<Union>{A'. prefix_closure A' = A' \<and> A' \<subseteq> A \<and> star_controllable_language A' \<Sigma>UC L}"

corollary supremal_star_controllable_language_and_supremal_controllable_language_coincide: "
  A = prefix_closure A
  \<Longrightarrow> L = prefix_closure L
  \<Longrightarrow> supremal_star_controllable_language A \<Sigma>UC L = supremal_controllable_language A \<Sigma>UC L"
  apply(unfold supremal_star_controllable_language_def supremal_controllable_language_def)
  apply(rule antisym)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply (metis star_controllable_language_implies_controllable_language)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(rule Sup_upper)
  apply(clarsimp)
  apply (metis controllable_language_implies_star_controllable_language)
  done

lemma star_controllable_subset_idempotent: "
  A = prefix_closure A
  \<Longrightarrow> L = prefix_closure L
  \<Longrightarrow> star_controllable_subset A \<Sigma>UC L = star_controllable_subset (star_controllable_subset A \<Sigma>UC L) \<Sigma>UC L"
  apply(rule antisym)
   apply(simp add: star_controllable_subset_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def prefix_closure_def prefix_def kleene_star_def)
   apply(clarsimp)
   apply(rename_tac w c u wa ca ua)(*strict*)
   apply(subgoal_tac "prefix wa w \<or> prefix w wa")
    apply(rename_tac w c u wa ca ua)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac w c u wa ca ua)(*strict*)
   apply(erule disjE)
    apply(rename_tac w c u wa ca ua)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac w c u wa ca ua)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: star_controllable_subset_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def prefix_closure_def prefix_def kleene_star_def)
  done

corollary star_controllable_subset_equal_to_supremal_star_controllable_language: "
  A = prefix_closure A
  \<Longrightarrow> L = prefix_closure L
  \<Longrightarrow> star_controllable_subset A \<Sigma>UC L = supremal_star_controllable_language A \<Sigma>UC L"
  apply(unfold supremal_star_controllable_language_def supremal_controllable_language_def)
  apply(rule antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule sym)
    apply(rule star_controllable_subset_prefix_closed)
    apply(force)
   apply(rule conjI)
    apply(simp add: star_controllable_subset_def)
    apply(force)
   apply(rule star_controllable_subset_FP_implies_star_controllable_language)
    apply(rule star_controllable_subset_prefix_closed)
    apply(force)
   apply(rule star_controllable_subset_idempotent)
    apply(force)
   apply(force)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
  apply(rule conjI)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w c u)(*strict*)
  apply(rule_tac
      A="x"
      in set_mp)
   apply(rename_tac x w c u)(*strict*)
   apply(force)
  apply(rename_tac x w c u)(*strict*)
  apply(rule_tac
      A="{w. \<exists>a\<in> x. \<exists>b. set b \<subseteq> \<Sigma>UC \<and> w = a @ b} \<inter> L"
      in set_mp)
   apply(rename_tac x w c u)(*strict*)
   apply(force)
  apply(rename_tac x w c u)(*strict*)
  apply(simp (no_asm))
  apply(rule conjI)
   apply(rename_tac x w c u)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x w c u)(*strict*)
  apply(rule_tac
      x="w"
      in bexI)
   apply(rename_tac x w c u)(*strict*)
   apply(clarsimp)
  apply(rename_tac x w c u)(*strict*)
  apply(force)
  done

corollary supremal_star_controllable_language_smaller_than_controllable_subset: "
  A = prefix_closure A
  \<Longrightarrow> L = prefix_closure L
  \<Longrightarrow> supremal_star_controllable_language A \<Sigma>UC L \<subseteq> controllable_subset A \<Sigma>UC L"
  apply(unfold supremal_star_controllable_language_def supremal_controllable_language_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
  apply(rule conjI)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w c v)(*strict*)
  apply(rule_tac
      A="x"
      in set_mp)
   apply(rename_tac x w c v)(*strict*)
   apply(force)
  apply(rename_tac x w c v)(*strict*)
  apply(rule_tac
      A="{w. \<exists>a\<in> x. \<exists>b. set b \<subseteq> \<Sigma>UC \<and> w = a @ b} \<inter> L"
      in set_mp)
   apply(rename_tac x w c v)(*strict*)
   apply(force)
  apply(rename_tac x w c v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="w"
      in bexI)
   apply(rename_tac x w c v)(*strict*)
   apply(force)
  apply(rename_tac x w c v)(*strict*)
  apply(force)
  done

corollary supremal_star_controllable_language_unequal_to_controllable_subset: "
  A = {[],[u]}
  \<Longrightarrow> L = {[],[u],[u,u]}
  \<Longrightarrow> \<Sigma>UC = {u}
  \<Longrightarrow> controllable_subset A \<Sigma>UC L = {[]}
  \<and> supremal_controllable_language A \<Sigma>UC L = {}"
  apply(unfold supremal_star_controllable_language_def supremal_controllable_language_def)
  apply(rule conjI)
   apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(erule_tac
      x="[u]"
      in allE)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: star_controllable_language_def star_controllable_subset_def controllable_language_def controllable_subset_def append_alphabet_def append_language_def alphabet_to_language_def controllable_word_def controllable_sublanguage_def prefix_closure_def kleene_star_def prefix_def)
  apply(case_tac "x={}")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>a. a \<in> x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x a)(*strict*)
  apply(case_tac "a=[]")
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(subgoal_tac "a=[u]")
   apply(rename_tac x a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "[u,u]\<in> {w. \<exists>a\<in> x. w = a @ [u]}")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "[u,u]\<in> x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp (no_asm))
  done

end
