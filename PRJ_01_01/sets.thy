section {*sets*}
theory
  sets

imports
  basic

begin

lemma ex1_set: "
  \<exists>!x. x \<in> A
  \<Longrightarrow> x \<in> A
  \<Longrightarrow> A = {x}"
  apply(auto)
  done

lemma in_set_eq_imp: "
  x \<in> A
  \<Longrightarrow> A = B
  \<Longrightarrow> (x \<in> B \<Longrightarrow> P)
  \<Longrightarrow> P"
  apply(auto)
  done

lemma from_in_set: "
  x \<in> A
  \<Longrightarrow> A = {f w|w. P w}
  \<Longrightarrow> \<exists>w. x = f w \<and> P w"
  apply(rule_tac
      x = "x"
      and A = "A"
      and B = "{f w|w. P w}"
      in in_set_eq_imp)
    apply(force)
   apply(force)
  apply(force)
  done

lemma propForElem: "
  {a} = A
  \<Longrightarrow> A = (Collect P)
  \<Longrightarrow> P a"
  apply(auto)
  done

lemma inMap_rev: "
  x  \<in> f ` A
  \<Longrightarrow> \<exists>y \<in> A. f y = x"
  apply(auto)
  done

lemma mapToApply: "
  A = {a}
  \<Longrightarrow> B = {b}
  \<Longrightarrow> f ` A = f ` B
  \<Longrightarrow> f a = f b"
  apply(auto)
  done

lemma inMap2: "
  f y = x
  \<Longrightarrow> y \<in> A
  \<Longrightarrow> x \<in> (f`A)"
  apply(auto)
  done

lemma inMap: "
  \<exists>y \<in> A. f y = x
  \<Longrightarrow> x \<in> f`A"
  apply(auto)
  done

lemma InBigUnion: "
  \<exists>y \<in> A. x \<in> f y
  \<Longrightarrow> x \<in> \<Union>{f y |y. y \<in> A}"
  apply(auto)
  done

lemma InBigUnion2: "
  x \<in> \<Union>{f y |y. y \<in> A}
  \<Longrightarrow> \<exists>y \<in> A. x \<in> f y"
  apply(auto)
  done

lemma distinct_by_set_membership: "
  a \<in> A 
  \<Longrightarrow> b \<notin> A 
  \<Longrightarrow> a \<noteq> b"
  apply(force)
  done

lemma elementChoice: "
  y \<in> (A\<union>B)
  \<Longrightarrow> y \<notin> B
  \<Longrightarrow> y \<in> A"
  apply(force)
  done

lemma eqSubset: "
  Collect P = Collect Q
  \<Longrightarrow> Q x
  \<Longrightarrow> P x"
  apply(auto)
  done

lemma theI_prime2: "
  \<exists>!x. f x  \<in> A
  \<Longrightarrow> (THE x. f x  \<in> A) = y
  \<Longrightarrow> f y  \<in> A"
  apply(rule_tac
      t = "y"
      and s = "THE x. f x  \<in> A"
      in ssubst)
   apply(force)
  apply(rule theI')
  apply(force)
  done

lemma isID: "
  R^^0 = Id"
  apply(auto)
  done

lemma setElemE: "
  x \<in> {(f y)| y. P (f y)}
  \<Longrightarrow> (\<And>y. P (f y) \<Longrightarrow> Q (f y))
  \<Longrightarrow> Q x"
  apply(auto)
  done

lemma mapToApply2: "
  A = {a}
  \<Longrightarrow> B = {b}
  \<Longrightarrow> \<exists>x \<in> A. \<exists>y \<in> B. f1(f2(f1 x)) = f1 y
  \<Longrightarrow> f1 ` (f2 ` (f1 ` A)) = f1 ` B"
  apply(auto)
  done

lemma unequal1: "
  \<exists>x \<in> A. x \<notin> B
  \<Longrightarrow> A \<noteq> B"
  apply(force)
  done

lemma hasElem_prefix_closureise: "
  A - B = {c}
  \<Longrightarrow> \<exists>I. I \<in> A"
  apply(force)
  done

lemma notin_union: "
  a \<notin> A
  \<Longrightarrow> a \<notin> B
  \<Longrightarrow> a \<notin> (A\<union>B)"
  apply(force)
  done

lemma rev_subset: "
  F1 \<subset> F0
  \<Longrightarrow> F0 \<subseteq> A
  \<Longrightarrow> A - F0 \<subset> A - F1"
  apply(auto)
  done

lemma getInner: "
  (\<And>X. f X \<subseteq> X)
  \<Longrightarrow> (\<And>X. g X \<subseteq> X)
  \<Longrightarrow> A = f (g A)
  \<Longrightarrow> A = g A"
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      A = "f (g A)"
      in set_mp)
   apply(rename_tac x)(*strict*)
   apply(blast+)
  done

lemma subsetI_basic: "
  \<forall>x. x \<in> A \<longrightarrow> x \<in> B
  \<Longrightarrow> A\<subseteq>B"
  apply(force)
  done

lemma subsetE: "
  A \<subseteq> B
  \<Longrightarrow> \<forall>x. x  \<in> A \<longrightarrow> x  \<in> B"
  apply(blast)
  done

lemma nInterI: "
  x \<notin> A \<or> x \<notin> B
  \<Longrightarrow> x \<notin> A \<inter> B"
  apply(simp)
  done

lemma nInterE: "
  x \<notin> A \<inter> B
  \<Longrightarrow> x \<notin> A \<or> x \<notin> B"
  apply(simp)
  done

lemma complementA: "
  x  \<in> A
  \<Longrightarrow> x \<notin> A - B
  \<Longrightarrow> x  \<in> B"
  apply(simp)
  done

lemma elemSubsetTrans: "
  x  \<in> A
  \<Longrightarrow> A \<subseteq> Collect P
  \<Longrightarrow> (P x \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(blast)
  done

lemma SetContraPosSubset: "
  A \<subseteq> B
  \<Longrightarrow> B \<subseteq> C
  \<Longrightarrow> C - B \<subseteq> C - A"
  apply(blast)
  done

lemma interSimp: "
  A = B \<inter> C
  \<Longrightarrow> A \<subseteq> C"
  apply(auto)
  done

lemma interSimp2: "
  A \<subseteq> B
  \<Longrightarrow> C \<subseteq> B
  \<Longrightarrow> A \<inter> C \<subseteq> B"
  apply(auto)
  done

lemma emptySetE: "
  A \<noteq> {}
  \<Longrightarrow> \<exists> x . x  \<in> A"
  apply(auto)
  done

lemma emptySetI: "
  \<exists> x . x  \<in> A
  \<Longrightarrow> A \<noteq> {}"
  apply(auto)
  done

lemma trivConjBySubset: "
  A\<subseteq> D
  \<Longrightarrow> A\<subseteq>B
  \<Longrightarrow> C\<subseteq>A
  \<Longrightarrow> P
  \<Longrightarrow> (A\<subseteq>B\<and>(P\<and>C\<subseteq>D))"
  apply(auto)
  done

lemma imageNotEmpty: "
  A \<noteq> {}
  \<Longrightarrow> f`A \<noteq> {}"
  apply(auto)
  done

lemma TransSubSetNorm: "
  \<forall>n. R^^n\<subseteq>S
  \<Longrightarrow> R\<^sup>* \<subseteq> S"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "(\<exists>n. x  \<in> R ^^ n)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply (metis rtrancl_power)
  apply(rename_tac x)(*strict*)
  apply(erule exE)
  apply(rename_tac x n)(*strict*)
  apply(rule_tac
      A = "R^^n"
      in set_mp)
   apply(rename_tac x n)(*strict*)
   apply(blast) +
  done

lemma useForMGEQZ: "
  (\<And>y. (z, y)  \<in> {e  \<in> less_than. fst e  \<in> A \<and> snd e  \<in> A}\<inverse> \<Longrightarrow> y \<notin> A)
  \<Longrightarrow> m  \<in> A
  \<Longrightarrow> z \<in> A
  \<Longrightarrow> z \<le> m"
  apply(case_tac "m < z")
   prefer 2
   apply(rule Orderings.linorder_class.leI)
   apply(blast)
  apply(subgoal_tac "(z,m) \<in> {e  \<in> less_than. fst e  \<in> A \<and> snd e  \<in> A}\<inverse>")
   apply(blast)
  apply(rule Relation.converseI)
  apply(simp)
  done

lemma supProveSubset: "
  B = \<Union>Collect P
  \<Longrightarrow> P C
  \<Longrightarrow> C \<subseteq> B"
  apply(auto)
  done

lemma supProveEq: "
  P B
  \<Longrightarrow> \<forall>C. P C \<longrightarrow> C \<subseteq> B
  \<Longrightarrow> B = \<Union>Collect P"
  apply(auto)
  done

lemma gfpSupCorrespond: "
  (\<And>x. f x \<subseteq> x)
  \<Longrightarrow> gfp (\<lambda>x. f x \<inter> y) = \<Union>{x. x = f x \<and> x\<subseteq>y }"
  apply(simp add: gfp_def)
  apply(subgoal_tac "{u. u \<subseteq> f u \<and> u \<subseteq> y} = {x. x = f x \<and> x \<subseteq> y}")
   apply(force)
  apply(force)
  done

lemma exSetEQI: "
  A = B
  \<Longrightarrow> {X. X = A} = {X. X = B}"
  apply(simp)
  done

lemma doubleMonoEQ: "
  (\<And>X. f X \<subseteq> X)
  \<Longrightarrow> (\<And>X. g X \<subseteq> X)
  \<Longrightarrow> X = f (g X)
  \<Longrightarrow> X = f X \<and> X = g X"
  apply(subgoal_tac "X = g X")
   apply(clarsimp)
  apply(subgoal_tac "X\<subseteq>f (g X)")
   apply(rule equalityI)
    apply(rule_tac
      B = "f (g X)"
      in subset_trans)
     apply(blast) +
  done

lemma EQremoveInter: "
  A = B\<inter>C
  \<Longrightarrow> B\<subseteq>C
  \<Longrightarrow> A = B"
  apply(auto)
  done

lemma setExEQI2: "
  (\<And>X. P X = Q X)
  \<Longrightarrow> {X. X\<subseteq>P X} = {X. X\<subseteq>Q X}"
  apply(auto)
  done

lemma subsetExtension: "
  A\<subseteq>B
  \<Longrightarrow> A\<subseteq>C
  \<Longrightarrow> A\<inter>C\<subseteq>B\<inter>C"
  apply(auto)
  done

lemma antiAbsorb: "
  A\<inter>B = A
  \<Longrightarrow> A\<subseteq>B"
  apply(auto)
  done

lemma nset_mp: "
  A \<subseteq> B
  \<Longrightarrow> x \<notin> B
  \<Longrightarrow> x \<notin> A"
  apply(auto)
  done

lemma set_eq_from_double_subseteq: "
  A \<subseteq> B
  \<Longrightarrow> B \<subseteq> A
  \<Longrightarrow> A = B"
  apply(auto)
  done

lemma add_element_to_enumeration: "
  y < x
  \<Longrightarrow> insert y (S \<union> {Suc y..x - Suc 0}) = S \<union> {y..x - Suc 0}"
  apply(rule order_antisym)
   apply(auto)
  done

lemma rev_subseteq: "
  F1 \<subseteq> F0
  \<Longrightarrow> A - F0 \<subseteq> A - F1"
  apply(auto)
  done

lemma useForMLEQZ: "
  (\<And>y. (y, z)  \<in> {e  \<in> less_than. fst e  \<in> A \<and> snd e  \<in> A}\<inverse> \<Longrightarrow> y \<notin> A)
  \<Longrightarrow> m  \<in> A
  \<Longrightarrow> z \<in> A
  \<Longrightarrow> m \<le> z"
  apply(case_tac "z < m")
   prefer 2
   apply(rule Orderings.linorder_class.leI)
   apply(blast)
  apply(subgoal_tac "(m,z) \<in> {e  \<in> less_than. fst e  \<in> A \<and> snd e  \<in> A}\<inverse>")
   apply(blast)
  apply(rule Relation.converseI)
  apply(simp)
  done

lemma set_mp_prime: "
  A \<subseteq> B
  \<Longrightarrow> x  \<in> A
  \<Longrightarrow> (x  \<in> B \<Longrightarrow> P)
  \<Longrightarrow> P"
  apply(auto)
  done

lemma restrict_subseteq: "
  A \<subseteq> B
  \<Longrightarrow> A \<subseteq> {x. P x}
  \<Longrightarrow> A \<subseteq> {x  \<in> B. P x}"
  apply(auto)
  done

lemma finite_ex_min: "
  finite (M::nat set)
  \<Longrightarrow> M \<noteq> {}
  \<Longrightarrow> \<exists>i. i \<in> M \<and> (\<forall>j < i. j\<notin>M)"
  apply(case_tac "0 \<in> M")
   apply(force)
  apply(subgoal_tac "\<exists>x. x \<in> M")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>k \<le> x. (\<forall>i < k. \<not>(\<lambda>x. x \<in> M) i) & (\<lambda>x. x \<in> M)k")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule ex_least_nat_le)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma InvLessThanFinite: "
  finite A
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> wf ({e. e \<in> less_than \<and> (fst e) \<in> A \<and>(snd e) \<in> A}\<inverse>)"
  apply(rule Wellfounded.finite_acyclic_wf_converse)
   apply(rule_tac
      B = "A\<times>A"
      in Finite_Set.finite_subset)
    apply(clarsimp)
   apply(rule Finite_Set.finite_cartesian_product)
    apply(simp) +
  apply(rule_tac
      s = "less_than"
      in Transitive_Closure.acyclic_subset)
   apply(rule Wellfounded.wf_acyclic)
   apply(rule Wellfounded.wf_less_than)
  apply(blast)
  done

lemma LessThanFinite: "
  finite A
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> wf ({e. e \<in> less_than \<and> (fst e) \<in> A \<and>(snd e) \<in> A})"
  apply(rule_tac
      r = "less_than"
      in Wellfounded.wf_subset)
   apply(rule Wellfounded.wf_less_than)
  apply(blast)
  done

lemma card_diff_null_implies_subseteq: "
  finite A
  \<Longrightarrow> card (A - B) = 0
  \<Longrightarrow> A \<subseteq> B"
  apply(subgoal_tac "A - B = {}")
   apply(auto)
  done

lemma strictly_smaller_set_map_has_strictly_fewer_image_elements: "
  \<forall>x. finite (f' x)
  \<Longrightarrow> \<forall>x. f x \<subseteq> f' x
  \<Longrightarrow> \<exists>x  \<in> A. f x \<subset> f' x
  \<Longrightarrow> finite A
  \<Longrightarrow> (\<Sum>x  \<in> A. card (f x)) < (\<Sum>x  \<in> A. card (f' x))"
  apply(erule_tac bexE)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t = "sum (\<lambda>x. card (f x)) A"
      and s = "(card(f x)) + (sum (\<lambda>x. card (f x)) (A - {x}))"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(rule Groups_Big.comm_monoid_add_class.sum.remove)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t = "sum (\<lambda>x. card (f' x)) A"
      and s = "(card(f' x)) + (sum (\<lambda>x. card (f' x)) (A - {x}))"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(rule Groups_Big.comm_monoid_add_class.sum.remove)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(rule Groups.ordered_cancel_ab_semigroup_add_class.add_less_le_mono)
   apply(rename_tac x)(*strict*)
   apply(rule Finite_Set.psubset_card_mono)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      i = "\<lambda>x. x"
      in Groups_Big.sum_le_included)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(rule_tac ballI)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x = "xa"
      and P = "\<lambda>xa. f xa \<subseteq> f' xa"
      in allE)
  apply(rule_tac
      x = "xa"
      in bexI)
   apply(rename_tac x xa)(*strict*)
   defer
   apply(blast)
  apply(rename_tac x xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(rule Finite_Set.card_mono)
   apply(rename_tac x xa)(*strict*)
   apply(blast)
  apply(rename_tac x xa)(*strict*)
  apply(blast)
  done

lemma finite_map_split: "
  finite A
  \<Longrightarrow> \<forall>x  \<in> A. finite (f x)
  \<Longrightarrow> finite {(x, y). x  \<in> A \<and> y = f x}"
  apply(rule_tac
      B = "(A \<times> {x. \<exists>y  \<in> A. x = f y})"
      in Finite_Set.finite_subset)
   apply(auto)
  done

lemma finite_big_union: "
  finite A
  \<Longrightarrow> \<forall>x  \<in> A. finite (f x)
  \<Longrightarrow> finite (\<Union>{f x |x. x  \<in> A})"
  apply(subgoal_tac "(\<forall>x  \<in> A. finite (f x)) \<longrightarrow> finite (\<Union>{f x |x. x  \<in> A})")
   apply(blast)
  apply(rule_tac
      x = "A"
      in Finite_Set.finite.induct)
    apply(blast)
   apply(clarsimp)
  apply(rename_tac Aa a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      s = "(f a)\<union>(\<Union>{y. \<exists>x. y = f x \<and> x  \<in> Aa})"
      and t = "\<Union>{y. \<exists>x. y = f x \<and> (x = a \<or> x  \<in> Aa)}"
      in ssubst)
   apply(rename_tac Aa a)(*strict*)
   apply(blast)
  apply(rename_tac Aa a)(*strict*)
  apply(auto)
  done

lemma positive_weight_function_with_sum_null_is_null_everywhere: "
  finite A
  \<Longrightarrow> sum f A = (0::nat)
  \<Longrightarrow> x  \<in> A
  \<Longrightarrow> \<forall>x  \<in> A. 0 \<le> f x
  \<Longrightarrow> f x = 0"
  apply(subgoal_tac "\<forall>x  \<in> A. f x = 0")
   apply(blast)
  apply(rule_tac
      s = "sum f A = 0"
      and t = "\<forall>x  \<in> A. f x = 0"
      in ssubst)
   apply(rule sym)
   apply(rule sum_eq_0_iff)
   apply(blast)
  apply(blast)
  done

lemma exInsert: "
  card A>0
  \<Longrightarrow> \<exists>a B. A = insert a B \<and> a \<notin> B"
  apply(case_tac "A = {}")
   apply(clarsimp)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule_tac
      x = "A - {x}"
      in allE)
  apply(clarsimp)
  apply(auto)
  done

lemma injToInfiniteSet: "
  \<not> finite B
  \<Longrightarrow> finite Q
  \<Longrightarrow> \<exists>f. inj_on f Q \<and> f`Q\<subseteq>B"
  apply(subgoal_tac "\<forall>n. \<forall>Q. card Q = n \<and> finite Q \<longrightarrow> (\<exists>f. inj_on f Q \<and> f`Q\<subseteq>B)")
   apply(erule_tac
      x = "card Q"
      in allE)
   apply(erule_tac
      x = "Q"
      in allE)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(induct_tac n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na Qa)(*strict*)
  apply(subgoal_tac "\<exists>a Q'. Qa = insert a Q' \<and> a \<notin> Q'")
   apply(rename_tac na Qa)(*strict*)
   defer
   apply(rule exInsert)
   apply(clarsimp)
  apply(rename_tac na Qa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a Q')(*strict*)
  apply(erule_tac
      x = "Q'"
      in allE)
  apply(erule impE)
   apply(rename_tac a Q')(*strict*)
   apply(clarsimp)
  apply(rename_tac a Q')(*strict*)
  apply(erule exE)
  apply(rename_tac a Q' f)(*strict*)
  apply(auto)
  apply(subgoal_tac "B - (f`Q') \<noteq> {}")
   apply(rename_tac a Q' f)(*strict*)
   defer
   apply(clarsimp)
  apply(rename_tac a Q' f)(*strict*)
  apply(subgoal_tac "\<exists>x. x \<in> (B - (f`Q'))")
   apply(rename_tac a Q' f)(*strict*)
   defer
   apply(blast)
  apply(rename_tac a Q' f)(*strict*)
  apply(erule exE)
  apply(rename_tac a Q' f x)(*strict*)
  apply(rule_tac
      x = "\<lambda>n. (if n = a then x else f n)"
      in exI)
  apply(rule conjI)
   apply(rename_tac a Q' f x)(*strict*)
   apply(simp add: inj_on_def)
  apply(rename_tac a Q' f x)(*strict*)
  apply(rule conjI)
   apply(rename_tac a Q' f x)(*strict*)
   apply(clarsimp)
  apply(rename_tac a Q' f x)(*strict*)
  apply(rule conjI)
   apply(rename_tac a Q' f x)(*strict*)
   apply(clarsimp)
  apply(rename_tac a Q' f x)(*strict*)
  apply(rule subsetI)
  apply(rename_tac a Q' f x xa)(*strict*)
  apply(rule set_mp)
   apply(rename_tac a Q' f x xa)(*strict*)
   apply(blast)
  apply(rename_tac a Q' f x xa)(*strict*)
  apply(clarsimp)
  done

lemma notFinite_subset: "
  \<not>(finite A)
  \<Longrightarrow> A\<subseteq>B
  \<Longrightarrow> \<not> finite B"
  apply(auto)
  apply(subgoal_tac "finite A")
   apply(blast)
  apply(rule Finite_Set.finite_subset)
   apply(auto)
  done

lemma finite_has_max: "
  finite A
  \<Longrightarrow> \<exists>(n::nat). \<forall>x \<in> A. f x \<le> n"
  apply(rule_tac
      x = "sum f A"
      in exI)
  apply(rule ballI)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t = "sum f A"
      and s = "f x + sum f (A - {x})"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(rule Groups_Big.sum.remove)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma finite_imageI_2sets: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> finite {f a b| a b. a  \<in> A \<and> b  \<in> B }"
  apply(rule_tac
      t = "{f a b| a b. a  \<in> A \<and> b  \<in> B }"
      and s = "(\<lambda>(a,b). f a b) ` (A\<times>B)"
      in ssubst)
   apply(force)
  apply(rule finite_imageI)
  apply(force)
  done

lemma finite_imageI_1set: "
  finite A
  \<Longrightarrow> finite {f a| a. a  \<in> A }"
  apply(rule_tac
      t = "{f a| a. a  \<in> A }"
      and s = "(\<lambda>a. f a) ` A"
      in ssubst)
   apply(force)
  apply(rule finite_imageI)
  apply(force)
  done

lemma UN_eq: "
  (\<Union>x \<in> A. B x) = \<Union>{Y. \<exists>x \<in> A. Y = B x}"
  apply(blast)
  done

lemma finite_transfer_card_eq: "
  card A = card B
  \<Longrightarrow> finite A
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> finite B"
  apply (metis card_eq_0_iff)
  done

lemma finite_two_set: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> B \<noteq> {}
  \<Longrightarrow> inj_on (\<lambda> (x, y) . two x y) (A \<times> B)
  \<Longrightarrow> finite {two a b| a b. a  \<in> A \<and> b  \<in> B}"
  apply(rule_tac
      A="A\<times>B"
      in finite_transfer_card_eq)
    apply(rule_tac
      f="\<lambda>(a,b). two a b"
      in bij_betw_same_card)
    apply(simp add: bij_betw_def)
    apply(rule order_antisym)
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma finite_three_set: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> B \<noteq> {}
  \<Longrightarrow> inj_on (\<lambda>(a, x, y). three a x y) (A \<times> B \<times> A)
  \<Longrightarrow> finite {three a b c| a b c. a  \<in> A \<and> c  \<in> A \<and> b  \<in> B}"
  apply(rule_tac
      A="A\<times>B\<times>A"
      in finite_transfer_card_eq)
    apply(rule_tac
      f="\<lambda>(a,b,c). three a b c"
      in bij_betw_same_card)
    apply(simp add: bij_betw_def)
    apply(rule order_antisym)
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Min_is_Suc_n: "
  n \<notin> A
  \<Longrightarrow> finite A
  \<Longrightarrow> (\<And>k. k  \<in> A \<Longrightarrow> n \<le> k)
  \<Longrightarrow> Suc n  \<in> A
  \<Longrightarrow> Min A = Suc n"
  apply (metis Min_eqI eq_iff not_less_eq_eq)
  done

lemma apply_min: "
  x  \<in> A
  \<Longrightarrow> x  \<in> A
  \<Longrightarrow> x = Min A
  \<Longrightarrow> P x
  \<Longrightarrow> P (Min A)"
  apply(force)
  done

lemma inter_eq_intro: "
  A \<subseteq> B
  \<Longrightarrow> A \<subseteq> C
  \<Longrightarrow> B \<inter> C \<subseteq> A
  \<Longrightarrow> A = B \<inter> C"
  apply(force)
  done

lemma card_diff: "
  C \<subseteq> B
  \<Longrightarrow> C \<noteq> B
  \<Longrightarrow> finite A
  \<Longrightarrow> B \<subseteq> A
  \<Longrightarrow> card (A - B) < card (A - C)"
  apply (metis finite_Diff psubset_card_mono psubset_eq rev_subset)
  done

lemma finite_big_union2: "
  finite A
  \<Longrightarrow> \<forall>x  \<in> A. finite (f x)
  \<Longrightarrow> finite (\<Union> (f ` A))"
  apply(rule finite_Union)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(force)
  done

lemma showDisj: "
  (\<And>x. x \<in> A \<Longrightarrow> x \<notin> B)
  \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<notin> A)
  \<Longrightarrow> A\<inter>B = {}"
  apply(auto)
  done

lemma showInImage: "
  \<exists>y \<in> A. f y = x
  \<Longrightarrow> x \<in> (f ` A)"
  apply(clarsimp)
  done

lemma inv_into_f_eq2: "
  inj_on f A
  \<Longrightarrow> a  \<in> A
  \<Longrightarrow> ((inv_into A f) \<circ> f) a = a"
  apply (metis inv_into_f_eq o_apply)
  done

lemma inj_on_from_infinite_set: "
  finite A
  \<Longrightarrow> \<not> finite (B::'b set)
  \<Longrightarrow> \<exists>f::'a \<Rightarrow> 'b. inj_on f A"
  apply (metis injToInfiniteSet)
  done

lemma Max_exists: "
  N \<noteq> {} 
  \<Longrightarrow> finite N 
  \<Longrightarrow> \<exists>x \<in> N. x = Max N"
  apply(rule_tac
      x="Max N"
      in bexI)
   apply(force)
  apply(rule Max_in)
   apply(force)
  apply(force)
  done

lemma ballE_prime: "
  \<forall>x \<in> A. P x
  \<Longrightarrow> (P x \<Longrightarrow> \<forall>x \<in> A. P x  \<Longrightarrow> Q)
  \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q )
  \<Longrightarrow> Q"
  apply(force)
  done

end

