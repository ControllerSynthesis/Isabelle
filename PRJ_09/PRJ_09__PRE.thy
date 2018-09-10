section {*PRJ\_09\_\_PRE*}
theory
  PRJ_09__PRE

imports
  PRJ_09__ENTRY

begin

lemma derivation_dropPosTransfer1: "
  y>0
  \<Longrightarrow> derivation_drop d x y = d (y+x)"
  apply(simp add: derivation_drop_def)
  done

lemma derivation_dropPosTransfer2: "
  d x = Some (pair e c)
  \<Longrightarrow> derivation_drop d x 0 = Some (pair None c)"
  apply(simp add: derivation_drop_def)
  done

definition nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt w n \<equiv> (if n<length w then Some (w!n) else None)"

lemma single_element_in_some_slice: "
  foldl (@) [] \<alpha> = l @ A # r
  \<Longrightarrow> \<exists>n l1 l2 r1 r2.
  n<length \<alpha>
  \<and> l1=foldl (@) [] (take n \<alpha>)
  \<and> l1@l2=l
  \<and> r1=foldl (@) [] (drop (Suc n) \<alpha>)
  \<and> r=r2@r1
  \<and> \<alpha>!n=l2@[A]@r2"
  apply(induct \<alpha> arbitrary: l A r rule: rev_induct)
   apply(rename_tac l A r)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs l A r)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix (foldl (@) [] xs) l \<or> prefix l (foldl (@) [] xs)")
   apply(rename_tac x xs l A r)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xs l A r)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs l A r)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xs A r c)(*strict*)
   apply(rule_tac
      x="length xs"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xs l A r)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xs l A r c)(*strict*)
  apply(case_tac c)
   apply(rename_tac x xs l A r c)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs A r)(*strict*)
   apply(rule_tac
      x="length xs"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xs l A r c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs l A r a list)(*strict*)
  apply(subgoal_tac "a=A")
   apply(rename_tac x xs l A r a list)(*strict*)
   prefer 2
   apply (metis append_eq_appendI drop_0 drop_Suc_Cons drop_prefix_closureise first_drop nth_append_length)
  apply(rename_tac x xs l A r a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs l A r list)(*strict*)
  apply(subgoal_tac "list@x=r")
   apply(rename_tac x xs l A r list)(*strict*)
   prefer 2
   apply (metis append_Cons append_assoc list.inject same_append_eq)
  apply(rename_tac x xs l A r list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs l A list)(*strict*)
  apply(erule_tac
      x="l"
      in meta_allE)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="list"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x xs A n cons_l2 r2)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply (metis nth_appendX)
  done

lemma equal_left_liftB: "
  liftB w1 @ liftA v1 = liftB w2 @ teA A # v2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "prefix (liftB w1) (liftB w2) \<or> SSA" for SSA)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac c ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac ys y)(*strict*)
   apply(rule_tac
      xs="w2"
      in rev_cases)
    apply(rename_tac ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y ysa ya)(*strict*)
   apply(clarsimp)
   apply (metis Nil_is_append_conv liftA.simps(1) liftA.simps(2) maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string neq_Nil_conv)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rule liftB_inj)
   apply(rule sym)
   apply(force)
  apply(rename_tac c ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(rule_tac
      xs="w1"
      in rev_cases)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply (metis Nil_is_append_conv liftA.simps(1) liftA.simps(2) maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string neq_Nil_conv)
  done

lemma filterA_commutes_over_concat: "
  filterA (w@v) = filterA w @ filterA v"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w v \<Sigma>)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v b)(*strict*)
  apply(clarsimp)
  done

lemma filterA_gt_0_then_rm_nonterminal: "
  length (filterA w2)>0
  \<Longrightarrow> \<exists>wx1 A wx2. w2 = wx1 @ [teA A] @ liftB wx2"
  apply(induct w2 rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(case_tac x)
   apply(rename_tac x xs \<Sigma>)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs \<Sigma>)(*strict*)
   apply(rule_tac
      x="xs"
      in exI)
   apply(rule_tac
      x="\<Sigma>"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rename_tac x xs b)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs b)(*strict*)
  apply(simp add: filterA_commutes_over_concat)
  apply(clarsimp)
  apply(rename_tac b wx1 A wx2)(*strict*)
  apply(rule_tac
      x="wx1"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="wx2@[b]"
      in exI)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma filterA_gt_0_then_lm_nontelminal: "
  length (filterA w2)>0
  \<Longrightarrow> \<exists>wx1 A wx2. w2 = liftB wx1 @ [teA A] @ wx2"
  apply(induct w2)
   apply(clarsimp)
  apply(rename_tac a w2)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w2 \<Sigma>)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 \<Sigma>)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rename_tac a w2 b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat)
  apply(rule_tac
      x="b#wx1"
      in exI)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma setA_elem_contained: "
  x \<in> setA w
  \<Longrightarrow> \<exists>w1 w2. w=w1@[teA x]@w2"
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
   apply(rename_tac a w \<Sigma>)(*strict*)
   prefer 2
   apply(rename_tac a w b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w \<Sigma>)(*strict*)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma setA_empty_filterA_empty: "
  setA w' = {}
  \<Longrightarrow> filterA w' = []"
  apply(induct w')
   apply(clarsimp)
  apply(rename_tac a w')(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w' \<Sigma>)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w' b)(*strict*)
  apply(clarsimp)
  done

lemma liftB_with_nonterminal_inside: "
  liftB x= w1@teA A#w2
  \<Longrightarrow> Q"
  apply (metis setA_liftB all_not_in_conv elemInsetA)
  done

lemma liftA_inj: "
  liftA a=liftA b
  \<Longrightarrow> a=b"
  apply (metis liftA_vs_filterA)
  done

lemma if_option_simp: "
  Some Y = (if P then Some X else None)
  \<Longrightarrow> (P \<Longrightarrow> X=Y \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(case_tac P)
   apply(force)
  apply(force)
  done

lemma if_option_simp_rev: "
  (if P then Some X else None) = Some Y
  \<Longrightarrow> (P \<Longrightarrow> X=Y \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(case_tac P)
   apply(force)
  apply(force)
  done

lemma liftA_distributes_over_drop: "
  liftA (drop n xa) = drop n (liftA xa)"
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

lemma take_liftA: "
  take k (liftA w) = liftA (take k w)"
  apply(rule_tac
      t="liftA"
      and s="map (\<lambda>x. teA x)"
      in ssubst)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(rule liftAMap)
  apply(rule List.take_map)
  done

lemma liftA_decompose: "
  liftA w = x@y
  \<Longrightarrow> \<exists>x' y'. liftA x'=x \<and> liftA y'=y \<and> w=x'@y'"
  apply(rule_tac
      x="take (length x) w"
      in exI)
  apply(rule_tac
      x="drop (length x) w"
      in exI)
  apply (metis liftA_distributes_over_drop append_take_drop_id dropPrecise takePrecise take_liftA)
  done

lemma terminal_prefix_eq: "
  setA w={}
  \<Longrightarrow> setA v={}
  \<Longrightarrow> (a=[] \<or> (\<exists>A w. a=teA A#w))
  \<Longrightarrow> (b=[] \<or> (\<exists>A w. b=teA A#w))
  \<Longrightarrow> w@a=v@b
  \<Longrightarrow> w=v"
  apply(subgoal_tac "prefix w v \<or> prefix v w")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule_tac
      P="a = []"
      in disjE)
   apply(simp add: prefix_def)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
   apply(rename_tac A w)(*strict*)
   apply (metis all_not_in_conv elemInsetA)
  apply(simp add: prefix_def)
  apply(erule_tac
      P="b = []"
      in disjE)
   apply(clarsimp)
   apply(rename_tac A wa)(*strict*)
   apply (metis all_not_in_conv elemInsetA)
  apply(clarsimp)
  apply(rename_tac A Aa wa waa)(*strict*)
  apply(erule disjE)
   apply(rename_tac A Aa wa waa)(*strict*)
   apply(clarsimp)
   apply(rename_tac A Aa wa waa c)(*strict*)
   apply(case_tac c)
    apply(rename_tac A Aa wa waa c)(*strict*)
    apply(clarsimp)
   apply(rename_tac A Aa wa waa c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac A list)(*strict*)
   apply (metis all_not_in_conv elemInsetA)
  apply(rename_tac A Aa wa waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac A Aa w wa c)(*strict*)
  apply(case_tac c)
   apply(rename_tac A Aa w wa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac A Aa w wa c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac Aa list)(*strict*)
  apply (metis all_not_in_conv elemInsetA)
  done

lemma liftB_prefix: "
  liftB w1 \<sqsubseteq> liftB w2
  \<Longrightarrow> w1 \<sqsubseteq> w2"
  apply (metis maxTermPrefix_shift maxTermPrefix_term_string prefix_def)
  done

lemma liftB_liftA_eq_liftB_liftA: "
  liftB w1 @ liftA w2 = liftB w3 @ liftA w4
  \<Longrightarrow> w1 = w3"
  apply(case_tac w4)
   apply(clarsimp)
   apply(rule_tac xs="w2" in rev_cases)
    apply(clarsimp)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: liftA_commutes_over_concat)
   apply(rule_tac xs="w3" in rev_cases)
    apply(rename_tac ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y ysa ya)(*strict*)
   apply(clarsimp)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rule_tac ?v1.0="w2" and A="a" and ?v2.0="liftA list" in equal_left_liftB)
  apply(clarsimp)
  done

lemma split_XX2: "
  (THE v. \<exists>x. liftB w1 @ liftA w2 = liftB x @ liftA v) = w2"
  apply(rule theI2)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(subgoal_tac "w1=xa")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule liftB_liftA_eq_liftB_liftA)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule liftA_inj)
   apply(rule sym)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "w1=xa")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(rule liftB_liftA_eq_liftB_liftA)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule liftA_inj)
  apply(rule sym)
  apply(force)
  done

lemma length_cmp_help: "
  length w1 = length w2
  \<Longrightarrow> X # w1 = v1 @ a # Y # w2
  \<Longrightarrow> Q"
  apply (metis append_Cons length_shorter_append2 list.distinct(1) list.size(4) order_refl)
  done

lemma append_nth_drop_tail: "
  i<length (a#w)
  \<Longrightarrow> (a#w@v)!i = (a#w)!i"
  apply(case_tac i)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule nth_append_1)
  apply(clarsimp)
  done

lemma equal_take_1: "
0<k
\<Longrightarrow>
       min k (Suc y) = Suc x \<Longrightarrow>
       Suc y \<le> k \<Longrightarrow>
       take x w = take y w"
  apply(case_tac k)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply (metis min.commute min_def)
  done

lemma nat_between_to_others: "
  Suc m \<ge> n \<Longrightarrow> n>m \<Longrightarrow> n=Suc m"
  apply(force)
  done

lemma nth_append_use_second: "
  i\<ge>length w
  \<Longrightarrow> x=v!(i-length w)
  \<Longrightarrow> (w@v)!i = x"
  apply(rule_tac t="(w@v)!i" in ssubst)
   apply(rule  nth_append_2)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma mutual_prefix_from_reversed_continuation_hlp: "
  n<length x1
  \<Longrightarrow> foldl (@) [] (take n (rev x1)) @
           rev x1 ! n @ foldl (@) [] (drop (Suc n) (rev x1)) =
           foldl (@) [] (rev x1)"
  apply(rule_tac
      t="rev x1 ! n"
      and s="foldl (@) [] [rev x1 ! n]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] [rev x1 ! n] @ foldl (@) [] (drop (Suc n) (rev x1))"
      and s="foldl (@) [] ([rev x1 ! n] @ (drop (Suc n) (rev x1)))"
      in subst)
   apply(rule foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] (take n (rev x1)) @ foldl (@) [] ([rev x1 ! n] @ drop (Suc n) (rev x1))"
      and s=" foldl (@) [] (take n (rev x1) @ ([rev x1 ! n] @ drop (Suc n) (rev x1)))"
      in subst)
   apply(rule foldl_distrib_append)
  apply(rule_tac
      t="take n (rev x1) @ [rev x1 ! n] @ drop (Suc n) (rev x1)"
      and s="rev x1"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule_tac
      P="\<lambda>X. (take n (rev x1)) @ [rev x1 ! n] @ (drop (Suc n) (rev x1)) = rev X"
      and t="x1"
      and s="(take (length x1- Suc n) x1)@(x1!(length x1- Suc n))#(drop(Suc (length x1- Suc n))x1)"
      in ssubst)
   apply (metis diff_Suc_less gr_implies_not0 id_take_nth_drop neq0_conv)
  apply (metis Cons_eq_appendI append_Nil append_take_drop_id_hlp diff_Suc_less diff_self_eq_0 length_rev less_imp_diff_less Cons_nth_drop_Suc)
  done

lemma mutual_prefix_from_reversed_continuation: "
  (\<And>y. length x1 - i \<le> y \<Longrightarrow>
  foldl (@) [] (drop y (rev x1)) = foldl (@) [] (drop y (rev x2)))
  \<Longrightarrow> foldl (@) [] (rev x1) = foldl (@) [] (rev x2)
  \<Longrightarrow> length x1 = length x2
  \<Longrightarrow> i< length x1
  \<Longrightarrow> suffix (x1!i) (x2!i) \<or> suffix (x2!i) (x1!i)"
  apply(rule_tac
      t="x1!i"
      and s="(rev x1)!(length x1 - Suc i)"
      in ssubst)
   apply(rule nth_rev)
   apply(force)
  apply(rule_tac
      t="x2!i"
      and s="(rev x2)!(length x2 - Suc i)"
      in ssubst)
   apply(rule nth_rev)
   apply(force)
  apply(subgoal_tac "\<exists>n. i+Suc n=length x1")
   prefer 2
   apply(rule_tac
      x="length x1 - (Suc i)"
      in exI)
   apply(force)
  apply(erule exE)+
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="length x2 - Suc i"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="length x1 - Suc i"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      a="foldl (@) [] (take n (rev x1))"
      and d="foldl (@) [] (take n (rev x2))"
      and c="foldl (@) [] (drop (Suc n) (rev x1))"
      and f="foldl (@) [] (drop (Suc n) (rev x2))"
      in mutual_suffix_suffix2)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(erule_tac
      x="Suc n"
      in meta_allE)
   apply(erule_tac meta_impE)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take n (rev x1)) @ rev x1 ! n @ foldl (@) [] (drop (Suc n) (rev x1))"
      and s="foldl (@) [] (rev x1)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule mutual_prefix_from_reversed_continuation_hlp)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take n (rev x2)) @ rev x2 ! n @ foldl (@) [] (drop (Suc n) (rev x2))"
      and s="foldl (@) [] (rev x2)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule mutual_prefix_from_reversed_continuation_hlp)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma pull_put_some_rev_nth: "
  i < length x1
  \<Longrightarrow> i + Suc n = length x1
  \<Longrightarrow> rev x1 ! n @ foldl (@) [] (drop (Suc n) (rev x1)) = foldl (@) [] (drop n (rev x1))"
  apply(rule_tac
      t="drop n (rev x1)"
      and s="rev (take (length (rev x1) - n) (rev (rev x1)))"
      in ssubst)
   apply(rule take_drop_rev2)
  apply(rule_tac
      t="length (rev x1)"
      and s="length x1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="length x1 - n"
      and s="Suc i"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="rev(rev x1)"
      and s="x1"
      in ssubst)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. rev x1 ! n @ foldl (@) [] (drop (Suc n) (rev x1)) = foldl (@) [] (rev (take (Suc i) X))"
      and t="x1"
      and s="(take i x1)@(x1!i)#(drop(Suc i)x1)"
      in ssubst)
   apply (metis append_take_drop_id_hlp Cons_nth_drop_Suc)
  apply(rule_tac
      t="take (Suc i) (take i x1 @ x1 ! i # drop (Suc i) x1)"
      and s="take i x1 @ [x1 ! i]"
      in ssubst)
   apply (metis append_take_drop_id_hlp Cons_nth_drop_Suc take_Suc_conv_app_nth)
  apply(rule_tac
      t="rev (take i x1 @ [x1 ! i])"
      and s="[x1 ! i] @ rev (take i x1 )"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] ([x1 ! i] @ rev (take i x1))"
      and s="foldl (@) [] (x1 ! i#rev (take i x1))"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] (x1 ! i# rev (take i x1))"
      and s="x1 ! i@foldl (@) [] (rev (take i x1))"
      in ssubst)
   apply(rule foldl_drop_head)
  apply(rule_tac
      t="x1!i"
      and s="(rev x1)!(length x1 - (Suc i))"
      in ssubst)
   apply(rule nth_rev)
   apply(force)
  apply(rule_tac
      t="length x1-Suc i"
      and s="n"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="take i x1"
      and s="rev (drop (length x1 - i) (rev x1))"
      in ssubst)
   apply(rule take_drop_rev3)
  apply(rule_tac
      t="length x1 - i"
      and s="Suc n"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma mutual_prefix_from_reverserd_continuation_unused: "
  (\<And>y. y\<le>(length x1 -Suc i) \<Longrightarrow>
  foldl (@) [] (drop y (rev x1)) = foldl (@) [] (drop y (rev x2)))
  \<Longrightarrow> length x1 = length x2
  \<Longrightarrow> i< length x1
  \<Longrightarrow> prefix (x1!i) (x2!i) \<or> prefix (x2!i) (x1!i)"
  apply(rule_tac
      t="x1!i"
      and s="(rev x1)!(length x1 - Suc i)"
      in ssubst)
   apply(rule nth_rev)
   apply(force)
  apply(rule_tac
      t="x2!i"
      and s="(rev x2)!(length x2 - Suc i)"
      in ssubst)
   apply(rule nth_rev)
   apply(force)
  apply(subgoal_tac "\<exists>n. i+Suc n=length x1")
   prefer 2
   apply(rule_tac
      x="length x1 - (Suc i)"
      in exI)
   apply(force)
  apply(erule exE)+
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="length x2 - Suc i"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="length x1 - Suc i"
      and s="n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      b="foldl (@) [] (drop (Suc n) (rev x1))"
      and d="foldl (@) [] (drop (Suc n) (rev x2))"
      in mutual_prefix_prefix)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="length x1"
      and s="i+Suc n"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="i + Suc n - Suc i"
      and s="n"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="rev x1 ! n @ foldl (@) [] (drop (Suc n) (rev x1))"
      and s="foldl (@) [] (drop n (rev x1))"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      i="i"
      in pull_put_some_rev_nth)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="rev x2 ! n @ foldl (@) [] (drop (Suc n) (rev x2))"
      and s="foldl (@) [] (drop n (rev x2))"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      i="i"
      in pull_put_some_rev_nth)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma foldl_equal_beyond_i: "
  (\<And>ia. i<ia \<and> ia < length \<alpha> \<Longrightarrow> x1 ! ia = x2 ! ia)
  \<Longrightarrow> length x1 = length \<alpha>
  \<Longrightarrow> length x2 = length \<alpha>
  \<Longrightarrow> i<length \<alpha>
  \<Longrightarrow> foldl (@) [] (drop (Suc i) x1) = foldl (@) [] (drop (Suc i) x2)"
  apply(induct "length \<alpha>-Suc i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i)(*strict*)
  apply(erule_tac
      x="Suc i"
      and P="\<lambda>z. (x = length \<alpha> - Suc z \<Longrightarrow> (\<And>ia. z < ia \<and> ia < length \<alpha> \<Longrightarrow> x1 ! ia = x2 ! ia) \<Longrightarrow> length x1 = length \<alpha> \<Longrightarrow> length x2 = length \<alpha> \<Longrightarrow> z < length \<alpha> \<Longrightarrow> foldl (@) [] (drop (Suc z) x1) = foldl (@) [] (drop (Suc z) x2))"
      in meta_allE)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule meta_impE)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="x1"
      and s="(take (Suc i) x1)@(x1!(Suc i))#(drop(Suc (Suc i))x1)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply (metis Suc_lessI add_Suc add_Suc_shift add_diff_inverse diff_Suc_Suc length_drop less_add_Suc2 less_not_refl list_update_id add.commute upd_conv_take_nth_drop)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="x2"
      and s="(take (Suc i) x2)@(x2!(Suc i))#(drop(Suc (Suc i))x2)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply (metis Suc_lessI add_Suc add_Suc_shift add_diff_inverse diff_Suc_Suc length_drop less_add_Suc2 less_not_refl list_update_id add.commute upd_conv_take_nth_drop)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="drop (Suc i) (take (Suc i) x1 @ x1 ! Suc i # drop (Suc (Suc i)) x1)"
      and s="x1 ! Suc i # drop (Suc (Suc i)) x1"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply (metis Suc_lessI add_Suc add_Suc_shift add_diff_inverse append_take_drop_id_hlp diff_Suc_Suc length_drop less_add_Suc2 less_not_refl add.commute Cons_nth_drop_Suc)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="drop (Suc i) (take (Suc i) x2 @ x2 ! Suc i # drop (Suc (Suc i)) x2)"
      and s="x2 ! Suc i # drop (Suc (Suc i)) x2"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply (metis Suc_lessI add_Suc add_Suc_shift add_diff_inverse append_take_drop_id_hlp diff_Suc_Suc length_drop less_add_Suc2 less_not_refl add.commute Cons_nth_drop_Suc)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (x1 ! Suc i # drop (Suc (Suc i)) x1)"
      and s=" foldl (@) [] ([x1 ! Suc i] @ drop (Suc (Suc i)) x1)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] ([x1 ! Suc i] @ drop (Suc (Suc i)) x1)"
      and s="foldl (@) [] [x1!Suc i] @ foldl (@) [] (drop (Suc (Suc i)) x1)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(rule foldl_distrib_append)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (x2 ! Suc i # drop (Suc (Suc i)) x2)"
      and s=" foldl (@) [] ([x2 ! Suc i] @ drop (Suc (Suc i)) x2)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] ([x2 ! Suc i] @ drop (Suc (Suc i)) x2)"
      and s="foldl (@) [] [x2!Suc i] @ foldl (@) [] (drop (Suc (Suc i)) x2)"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(rule foldl_distrib_append)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="x1!Suc i"
      and s="x2!Suc i"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  done

lemma foldl_take_decomp: "
  Suc x = length x1 - Suc i
  \<Longrightarrow> i < length x1
  \<Longrightarrow> foldl (@) [] (take (length x1 - Suc i) (rev x1)) = (foldl (@) [] (take (length x1 - Suc (Suc i)) (rev x1))) @ (x1 ! Suc i)"
  apply(rule_tac
      t="take (length x1 - Suc i) (rev x1)"
      and s="take (length x1 - Suc (Suc i)) (rev x1) @ [(rev x1)!(length x1 - Suc (Suc i))]"
      in subst)
   apply(rule_tac
      n="length x1 - Suc (Suc i)"
      in take_n_vs_take_Suc_n)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] (take (length x1 - Suc (Suc i)) (rev x1) @ [rev x1 ! (length x1 - Suc (Suc i))])"
      and s=" (foldl (@) [] (take (length x1 - Suc (Suc i)) (rev x1))) @ (foldl (@) [] [rev x1 ! (length x1 - Suc (Suc i))])"
      in ssubst)
   apply(rule foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] [rev x1 ! (length x1 - Suc (Suc i))]"
      and s="rev x1 ! (length x1 - Suc (Suc i))"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="rev x1 ! (length x1 - Suc (Suc i))"
      and s="x1!Suc i"
      in subst)
   apply(rule nth_rev)
   apply(force)
  apply(force)
  done

lemma lemma_4_7_uniqueness_hlp3: "
  (\<And>ia. length x1 - Suc ia < length x1 - Suc i \<Longrightarrow> ia < length x1
              \<Longrightarrow> x1 ! ia = x2 ! ia)
  \<Longrightarrow> i < length x1
  \<Longrightarrow> length x2 = length x1
  \<Longrightarrow> foldl (@) [] (take (length x1 - Suc i) (rev x1)) = foldl (@) [] (take (length x1 - Suc i) (rev x2))"
  apply(induct "length x1 - Suc i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take (length x1 - Suc i) (rev x1))"
      and s="foldl (@) [] (take (length x1 - Suc (Suc i)) (rev x1)) @ x1 ! Suc i"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(rule foldl_take_decomp)
    apply(rename_tac x i)(*strict*)
    apply(force)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="length x1 - Suc i"
      and s="length x2 - Suc i"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (take (length x2 - Suc i) (rev x2))"
      and s="foldl (@) [] (take (length x2 - Suc (Suc i)) (rev x2)) @ x2 ! Suc i"
      in ssubst)
   apply(rename_tac x i)(*strict*)
   apply(rule foldl_take_decomp)
    apply(rename_tac x i)(*strict*)
    apply(force)
   apply(rename_tac x i)(*strict*)
   apply(force)
  apply(rename_tac x i)(*strict*)
  apply(force)
  done

lemma rhs_hlp: "
  Suc k \<le> length r
  \<Longrightarrow> foldl (@) [] (take k (map (\<lambda>x. [x]) r)) @ [r ! k] =
          foldl (@) [] (take (Suc k) (map (\<lambda>x. [x]) r))"
  apply (metis less_eq_Suc_le_raw split_string_into_single_item_strings take_map take_nth_split)
  done

lemma take_split: "
  foldl (@) [] (take k(map (\<lambda>x. [x]) r)) = take k r"
  apply(induct r arbitrary: k rule: rev_induct)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs k)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="k"
      in meta_allE)
  apply(case_tac "k-length xs")
   apply(rename_tac x xs k)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs k nat)(*strict*)
  apply(clarsimp)
  done

lemma equivalent_append: "
  x1=w1@v
  \<Longrightarrow> x2=w2@v
  \<Longrightarrow> length w1\<le>i
  \<Longrightarrow> length w2\<le>j
  \<Longrightarrow> i-length w1=j-length w2
  \<Longrightarrow> x1!i = x2!j"
  apply (metis nth_append_2)
  done

lemma in_set_butlast: "
  w=w1@[x]@w2
  \<Longrightarrow> w2\<noteq>[]
  \<Longrightarrow> x \<in> set(butlast w)"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "w2=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   apply(rename_tac w' a')(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  done

lemma butlast_direct: "
  w@[a]=v
  \<Longrightarrow> butlast v = w"
  apply(force)
  done

lemma foldl_subset: "
  (\<And>x. x\<in> set w \<Longrightarrow> set x \<subseteq> A)
  \<Longrightarrow> set (foldl (@) [] w) \<subseteq> A"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w x)(*strict*)
  apply(subgoal_tac "foldl (@) a w = a@foldl (@) [] w")
   apply(rename_tac a w x)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac a w x)(*strict*)
    apply(force)
   apply(rename_tac a w x)(*strict*)
   apply(force)
  apply(rename_tac a w x)(*strict*)
  apply(rule foldl_first)
  done

lemma map_append: "
  w=w1@w2
  \<Longrightarrow> map f w = map f w1 @ map f w2"
  apply(force)
  done

lemma setA_substring: "
  w2 @ w3 = liftB v
  \<Longrightarrow> setA w2 = {}"
  apply(induct w2 arbitrary: w3 v)
   apply(rename_tac w3 v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w2 w3 v)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w2 w3 v aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w2 w3 v aa)(*strict*)
   apply(case_tac v)
    apply(rename_tac w2 w3 v aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac w2 w3 v aa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w2 w3 v b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w2 w3 v b)(*strict*)
  apply(case_tac v)
   apply(rename_tac w2 w3 v b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w2 w3 v b a list)(*strict*)
  apply(clarsimp)
  done

lemma setA_substring_prime: "
  w2 @ w3 = liftB v
  \<Longrightarrow> setA w3 = {}"
  apply(induct w3 arbitrary: w2 v rule: rev_induct)
   apply(rename_tac w2 v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs w2 v)(*strict*)
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. v=w'@[a'])")
   apply(rename_tac x xs w2 v)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x xs w2 v)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs w2 v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs w2 v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w2 w' a')(*strict*)
  apply(simp add: simpY)
  apply(clarsimp)
  done

lemma initial_liftB_strings_coincide: "
  liftB l @ teA A # r = liftB x @ liftA y
  \<Longrightarrow> l = x"
  apply (metis setA_liftB liftB_inj split_decide1)
  done

lemma liftB_empty: "
  liftB x = []
  \<Longrightarrow> x=[]"
  apply(case_tac x)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma liftA_empty: "
  liftA x = []
  \<Longrightarrow> x=[]"
  apply(case_tac x)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma setA_liftA_set: "
  setA(liftA w) = set w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma setA_substring2: "
  w1@w2 @ w3 = liftB v
  \<Longrightarrow> setA w2 = {}"
  apply(subgoal_tac "\<exists>l'. liftB l' = w1@w2")
   prefer 2
   apply(rule_tac
      x="filterB (w1@w2)"
      in exI)
   apply (rule liftBDeConv2)
   apply(rule setA_substring)
   apply(force)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w1")
   apply(rename_tac l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w1"
      in exI)
   apply (rule liftBDeConv2)
   apply(rule setA_substring)
   apply(force)
  apply(rename_tac l')(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a)(*strict*)
  apply(rule setA_substring_prime)
  apply(rule sym)
  apply(force)
  done

lemma SPLIT_X1: "
  (THE w. \<exists>v. teA A # liftA \<beta> = liftB w @ liftA v) = []"
  apply(rule_tac
      t="teA A # liftA \<beta>"
      and s="liftB [] @teA A # liftA \<beta>"
      in ssubst)
   apply(force)
  apply (metis SPLIT_2_1)
  done

lemma SPLIT_X2: "
  (THE w. \<exists>v. teB b # teA B # liftA \<beta> = liftB w @ liftA v) = [b]"
  apply(rule_tac
      a="[b]"
      in HOL.theI2)
    apply(rule_tac
      x="B#\<beta>"
      in exI)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac v)(*strict*)
    apply(case_tac v)
     apply(rename_tac v)(*strict*)
     apply(force)
    apply(rename_tac v a list)(*strict*)
    apply(force)
   apply(rename_tac x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list v)(*strict*)
   apply(case_tac list)
    apply(rename_tac list v)(*strict*)
    apply(clarsimp)
   apply(rename_tac list v a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(case_tac x)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac v)(*strict*)
   apply(case_tac v)
    apply(rename_tac v)(*strict*)
    apply(clarsimp)
   apply(rename_tac v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac v list)(*strict*)
  apply(case_tac list)
   apply(rename_tac v list)(*strict*)
   apply(clarsimp)
  apply(rename_tac v list a lista)(*strict*)
  apply(clarsimp)
  done

lemma maximalPrefixB_split: "
  maximalPrefixB (liftB w@liftA v) =w"
  apply (metis append_Nil2 maximalPrefixB_liftA maximalPrefixB_drop_liftB)
  done

lemma left_most_terminal_exists: "
  setA w\<noteq>{}
  \<Longrightarrow> \<exists>w1 w2 A. w=liftB w1 @ teA A # w2"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac "setA w = {}")
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
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w1 w2 A)(*strict*)
  apply(simp add: simpY)
  apply(case_tac a)
   apply(rename_tac a w1 w2 A aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 A aa)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w1 w2 A b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 A b)(*strict*)
  apply(rule_tac
      x="b#w1"
      in exI)
  apply(clarsimp)
  done

lemma nonterminal_not_in_liftB: "
  liftB w1 = liftB v1 @ teA a # liftA v2
  \<Longrightarrow> Q"
  apply(induct w1 arbitrary: v1 a v2)
   apply(rename_tac v1 a v2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w1 v1 aa v2)(*strict*)
  apply(clarsimp)
  apply(case_tac v1)
   apply(rename_tac a w1 v1 aa v2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w1 v1 aa v2 ab list)(*strict*)
  apply(clarsimp)
  done

lemma liftB_liftA_inj1: "
  liftB w1 @ liftA w2 = liftB v1 @ liftA v2
  \<Longrightarrow> w1=v1"
  apply(case_tac w2)
   apply(clarsimp)
   apply(case_tac v2)
    apply(clarsimp)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule nonterminal_not_in_liftB)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac v2)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rule nonterminal_not_in_liftB)
   apply(rule sym)
   apply(force)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply (metis liftA.simps(2) append_Nil2 maximalPrefixB_liftA maximalPrefixB_drop_liftB)
  done

lemma liftB_liftA_inj2: "
  liftB w1 @ liftA w2 = liftB v1 @ liftA v2
  \<Longrightarrow> w2=v2"
  apply(subgoal_tac "w1=v1")
   apply(clarsimp)
   apply(rule liftA_inj)
   apply(force)
  apply(rule liftB_liftA_inj1)
  apply(force)
  done

lemma prefix_of_maxTermPrefix_is_terminal_string_prefix: "
  \<alpha>@x = maxTermPrefix w
  \<Longrightarrow> prefix (liftB \<alpha>) w"
  apply(induct \<alpha> arbitrary: x w)
   apply(rename_tac x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac a \<alpha> x w)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac a \<alpha> x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<alpha> x)(*strict*)
   apply(subgoal_tac "a # \<alpha> @ x = []")
    apply(rename_tac a \<alpha> x)(*strict*)
    apply(force)
   apply(rename_tac a \<alpha> x)(*strict*)
   apply(rule_tac
      t="a # \<alpha> @ x"
      and s="maxTermPrefix []"
      in ssubst)
    apply(rename_tac a \<alpha> x)(*strict*)
    apply(force)
   apply(rename_tac a \<alpha> x)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB.simps(1))
  apply(rename_tac a \<alpha> x w aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<alpha> x aa list)(*strict*)
  apply(case_tac aa)
   apply(rename_tac a \<alpha> x aa list ab)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<alpha> x list ab)(*strict*)
   apply(subgoal_tac "a # \<alpha> @ x = []")
    apply(rename_tac a \<alpha> x list ab)(*strict*)
    apply(force)
   apply(rename_tac a \<alpha> x list ab)(*strict*)
   apply(rule_tac
      t="a # \<alpha> @ x"
      and s="maxTermPrefix (teA ab # list)"
      in ssubst)
    apply(rename_tac a \<alpha> x list ab)(*strict*)
    apply(force)
   apply(rename_tac a \<alpha> x list ab)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac a \<alpha> x aa list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<alpha> x list b)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teB b # list) = b#maxTermPrefix list")
   apply(rename_tac a \<alpha> x list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<alpha> x list b)(*strict*)
   apply(erule_tac
      x="x"
      in meta_allE)
   apply(erule_tac
      x="list"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(rename_tac a \<alpha> x list b)(*strict*)
  apply (metis maxTermPrefix_pull_out)
  done

lemma prefix_of_liftB_liftA: "
  liftB x \<sqsubseteq> (y @ liftA z)
  \<Longrightarrow> liftB x \<sqsubseteq> y"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix (liftB x) y \<or> prefix y (liftB x)")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = y")
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB y"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ca l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = ca")
   apply(rename_tac c ca l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB ca"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac c ca l')(*strict*)
  apply(clarsimp)
  apply(rename_tac c l' l'a)(*strict*)
  apply(subgoal_tac "l'@l'a=x")
   apply(rename_tac c l' l'a)(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac c l' l'a)(*strict*)
  apply(clarsimp)
  apply(thin_tac "liftB l' @ liftB l'a = liftB (l' @ l'a)")
  apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac c l'a)(*strict*)
  apply(case_tac l'a)
   apply(rename_tac c l'a)(*strict*)
   apply(clarsimp)
  apply(rename_tac c l'a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c a list)(*strict*)
  apply(case_tac z)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac c a list aa lista)(*strict*)
  apply(clarsimp)
  done

lemma prefix_append1: "
  prefix x (y@z)
  \<Longrightarrow> x \<sqsubseteq> y \<or> (\<exists>c1 c2. c1 \<noteq>[] \<and> y@c1=x \<and> c1@c2=z)"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix x y \<or> prefix y x")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  apply(force)
  done

lemma prefix_append2: "
  prefix x (y@z)
  \<Longrightarrow> x\<noteq>y@z
  \<Longrightarrow> x \<sqsubseteq> y \<or> (\<exists>c1 c2. c2 \<noteq>[] \<and> y@c1=x \<and> c1@c2=z)"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix x y \<or> prefix y x")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(force)
  done

lemma earlies_nonterminal_may_exist: "
  (\<exists>v. w=liftB v) \<or> (\<exists>w1 A w2. liftB w1@teA A#w2=w)"
  apply(case_tac "setA w={}")
   apply(rule disjI1)
   apply(rule_tac
      x="filterB w"
      in exI)
   apply (metis liftBDeConv2)
  apply(rule disjI2)
  apply(subgoal_tac "\<exists>x. x\<in> setA w")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "setA w \<noteq> {}")
  apply(subgoal_tac "\<exists>w1 w2 A. w1 @ [teA A] @ w2 = SSw \<and> setA w1 = {}" for SSw)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule setA_decomp_R2)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w1 w2 A)(*strict*)
  apply(rule_tac
      x="filterB w1"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="w2"
      in exI)
  apply(clarsimp)
  apply (metis liftBDeConv2)
  done

lemma liftB_append: "
  x@y=liftB w
  \<Longrightarrow> \<exists>l1 l2. x=liftB l1 \<and> y=liftB l2 \<and> w=l1@l2"
  apply(subgoal_tac "\<exists>l'. liftB l' = x")
   prefer 2
   apply(rule_tac
      x="filterB x"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = y")
   apply(rename_tac l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB y"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac l')(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a)(*strict*)
  apply(rule_tac
      x="l'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="l'a"
      in exI)
  apply(clarsimp)
  apply(rule liftB_inj)
  apply(simp add: liftB_commutes_over_concat)
  apply(rule sym)
  apply(force)
  done

lemma terminal_nonterminal_identify: "
  a@b=c@d
  \<Longrightarrow> setA a={}
  \<Longrightarrow> setA c={}
  \<Longrightarrow> setB b={}
  \<Longrightarrow> setB d={}
  \<Longrightarrow> a=c \<and> b=d"
  apply(subgoal_tac "\<exists>l'. liftB l' = a")
   prefer 2
   apply(rule_tac
      x="filterB a"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = c")
   apply(rename_tac l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB c"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac l')(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = b")
   apply(rename_tac l' l'a)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterA b"
      in exI)
   apply (metis liftA_filterA liftA_append_setB liftA_commutes_over_concat)
  apply(rename_tac l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a l'b)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = d")
   apply(rename_tac l' l'a l'b)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterA d"
      in exI)
   apply (metis liftA_filterA liftA_append_setB liftA_commutes_over_concat)
  apply(rename_tac l' l'a l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c)(*strict*)
  apply(subgoal_tac "prefix (liftB l') (liftB l'a) \<or> SSX" for SSX)
   apply(rename_tac l' l'a l'b l'c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac l' l'a l'b l'c)(*strict*)
  apply(erule disjE)
   apply(rename_tac l' l'a l'b l'c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac l' l'a l'b l'c c)(*strict*)
   apply(case_tac c)
    apply(rename_tac l' l'a l'b l'c c)(*strict*)
    apply(clarsimp)
   apply(rename_tac l' l'a l'b l'c c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' l'a l'b l'c a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac l' l'a l'b l'c a list aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac l' l'a l'b l'c list aa)(*strict*)
    apply(rule liftB_with_nonterminal_inside)
    apply(rule sym)
    apply(force)
   apply(rename_tac l' l'a l'b l'c a list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' l'a l'b l'c list b)(*strict*)
   apply(subgoal_tac "liftB l' @ liftA l'b = (liftB l' @ teB b # list) @ liftA l'c")
    apply(rename_tac l' l'a l'b l'c list b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac l' l'a l'b l'c list b)(*strict*)
   apply(thin_tac "liftB l' @ liftA l'b = liftB l'a @ liftA l'c")
   apply(thin_tac "liftB l' @ teB b # list = liftB l'a")
   apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c c)(*strict*)
  apply(case_tac c)
   apply(rename_tac l' l'a l'b l'c c)(*strict*)
   apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac l' l'a l'b l'c a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' l'a l'b l'c list aa)(*strict*)
   apply(rule liftB_with_nonterminal_inside)
   apply(rule sym)
   apply(force)
  apply(rename_tac l' l'a l'b l'c a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c list b)(*strict*)
  apply(subgoal_tac "(liftB l'a @ teB b # list) @ liftA l'b = liftB l'a @ liftA l'c")
   apply(rename_tac l' l'a l'b l'c list b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac l' l'a l'b l'c list b)(*strict*)
  apply(thin_tac "liftB l' @ liftA l'b = liftB l'a @ liftA l'c")
  apply(thin_tac "liftB l'a @ teB b # list = liftB l'")
  apply(clarsimp)
  apply(case_tac l'c)
   apply(rename_tac l' l'a l'b l'c list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac l' l'a l'b l'c list b a lista)(*strict*)
  apply(force)
  done

lemma strict_prefix_alt: "
  strict_prefix w1 (w2@w3)
  \<Longrightarrow> strict_prefix w1 w2 \<or> prefix w2 w1"
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix w1 w2 \<or> SSX" for SSX)
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def)
  done

lemma liftB_liftA_inter: "
  set (liftB w) \<inter> set (liftA v) = {}"
  apply(case_tac "\<exists>x. x \<in> set (liftB w) \<inter> set (liftA v)")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply (metis teA_not_in_liftB)
  apply(rename_tac x b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply (metis setB_liftA setB_set_not emptyE)
  done

lemma strict_prefix_length: "
  strict_prefix a b
  \<Longrightarrow> length a < length b"
  apply(simp add: strict_prefix_def)
  apply(force)
  done
lemma length_append_empty1: "
  length w = length v
  \<Longrightarrow> w @ x = v
  \<Longrightarrow> x=[]"
  apply(force)
  done

lemma length_append_empty2: "
  length w = length v
  \<Longrightarrow> x @ w = v
  \<Longrightarrow> x=[]"
  apply(force)
  done

lemma equal_drop_with_an_extension: "
  w@x=y
  \<Longrightarrow> m=n+length w
  \<Longrightarrow> drop n x = drop m y"
  apply(clarsimp)
  done

lemma insert_larger_in_Min_set1: "
  finite A
  \<Longrightarrow> y\<le>x
  \<Longrightarrow> Min (A\<union>{x,y}) \<le> Min (A\<union>{y})"
  apply (metis Min_antimono Un_empty_right Un_insert_right empty_not_insert finite.insertI insert_commute insert_mono subset_insertI)
  done

lemma Min_insert: "
  finite A
  \<Longrightarrow> A \<noteq>{}
  \<Longrightarrow> Min A \<le> X
  \<Longrightarrow> Min ({X} \<union> A) = Min A"
  apply(rule order_antisym)
   apply(rule Min_antimono)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma insert_larger_in_Min_set2: "
  finite A
  \<Longrightarrow> y\<le>x
  \<Longrightarrow> Min (A\<union>{y}) = Min (A\<union>{y,x})"
  apply(subgoal_tac "Min ({x} \<union> (A\<union>{y})) = Min (A\<union>{y})")
   apply(force)
  apply(rule Min_insert)
    apply(force)
   apply(force)
  apply (metis Min_le Un_empty_right Un_insert_right finite.insertI insertI1 xt1(6))
  done
lemma append_take_drop_id_C: "
  w@drop n v = v
  \<Longrightarrow> w=take n v"
  apply (metis append_same_eq append_take_drop_id)
  done

lemma double_suffix_butn_decomposition: "
  suffix w1 w2
  \<Longrightarrow> suffix w2 w3
  \<Longrightarrow> butn w1 (length w3) = butn w1 (length w2) @ butn w2 (length w3)"
  apply(simp add: suffix_def butn_def)
  apply(clarsimp)
  done

lemma exI_5: "
  \<exists>a b c d. P a b c d e
  \<Longrightarrow> \<exists>a b c d e. P a b c d e"
  apply(force)
  done

lemma take_butn2: "
  length w=n+m
  \<Longrightarrow> take n w = butn w m"
  apply(simp add: butn_def)
  done

lemma maxTermPrefix_drop_liftA: "
  maxTermPrefix (w@liftA v)=maxTermPrefix w"
  apply(induct w)
   apply(clarsimp)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB.simps(1) maximalPrefixB_liftA)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w aa)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w b)(*strict*)
  apply (metis maxTermPrefix_pull_out append_Cons)
  done

lemma ballE_in: "
  \<forall>x\<in> A. P x
  \<Longrightarrow> (P x \<Longrightarrow> Q)
  \<Longrightarrow> x \<in> A
  \<Longrightarrow> Q"
  apply(force)
  done

lemma setA_elem_is_contained: "
  A \<in> setA w
  \<Longrightarrow> \<exists>w1 w2. w=w1@teA A#w2"
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
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma always_greater_satisfaction_implies_satisfaction_beyond_any_limit: "
  (\<And>n. P n \<Longrightarrow> \<exists>m>n. P m)
  \<Longrightarrow> P x
  \<Longrightarrow> \<exists>m. P (k + Suc m)"
  apply(case_tac "k<x")
   apply(clarsimp)
   apply(rule_tac
      x="x-Suc k"
      in exI)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "x \<le> k")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(induct "k-x" arbitrary: x rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(case_tac "x=k")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="k"
      and P="\<lambda>k. (P k \<Longrightarrow> \<exists>m>k. P m)"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac m)(*strict*)
   apply(rule_tac
      x="m-Suc k"
      in exI)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. (P x \<Longrightarrow> \<exists>m>x. P m)"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x m)(*strict*)
  apply(subgoal_tac "x<k")
   apply(rename_tac x m)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x m)(*strict*)
  apply(clarsimp)
  apply(case_tac "k<m")
   apply(rename_tac x m)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="m-Suc k"
      in exI)
   apply(force)
  apply(rename_tac x m)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "m\<le>k")
   apply(rename_tac x m)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x m)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="m"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x m)(*strict*)
   apply(force)
  apply(rename_tac x m)(*strict*)
  apply(erule meta_impE)
   apply(force)
  apply(rename_tac x m)(*strict*)
  apply(force)
  done

lemma always_extendable_satisfaction_in_conflict_with_finite_satisfaction: "
  (\<And>n. P n \<Longrightarrow> \<exists>m>n. P m)
  \<Longrightarrow> (\<And>k m. Q k \<Longrightarrow> P (k+Suc m) \<Longrightarrow> R)
  \<Longrightarrow> \<exists>k. Q k
  \<Longrightarrow> \<exists>x. P x
  \<Longrightarrow> R"
  apply(clarsimp)
  apply(rename_tac k x)(*strict*)
  apply(subgoal_tac "\<exists>m. P (k+Suc m)")
   apply(rename_tac k x)(*strict*)
   apply(force)
  apply(rename_tac k x)(*strict*)
  apply(rule always_greater_satisfaction_implies_satisfaction_beyond_any_limit)
   apply(rename_tac k x n)(*strict*)
   apply(force)
  apply(rename_tac k x)(*strict*)
  apply(force)
  done

lemma liftA_append: "
  x @ y = liftA w
  \<Longrightarrow> \<exists>l1 l2. x = liftA l1 \<and> y = liftA l2 \<and> w = l1 @ l2"
  apply(subgoal_tac "\<exists>l'. liftA l' = x")
   prefer 2
   apply(rule_tac
      x="filterA x"
      in exI)
   apply (metis liftA_filterA liftA_decompose setB_liftA)
  apply(clarsimp)
  apply(rename_tac l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = y")
   apply(rename_tac l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterA y"
      in exI)
   apply (metis liftA_filterA liftA_decompose setB_liftA)
  apply(rename_tac l')(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a)(*strict*)
  apply(rule_tac
      x="l'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="l'a"
      in exI)
  apply(clarsimp)
  apply(rule liftA_inj)
  apply(simp add: liftA_commutes_over_concat)
  apply(rule sym)
  apply(force)
  done
lemma liftB_liftA_one_one: "
  liftB a @ liftA b = [teB x, teA y]
  \<Longrightarrow> a = [x] \<and> b=[y]"
  apply(case_tac a)
   apply(clarsimp)
   apply(case_tac b)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
   apply(case_tac b)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista)(*strict*)
  apply(clarsimp)
  done

lemma liftB_liftA_zero_two: "
  liftB a @ liftA b = [teA x, teA y]
  \<Longrightarrow> a = [] \<and> b=[x,y]"
  apply(case_tac a)
   apply(clarsimp)
   apply(case_tac b)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac lista a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(clarsimp)
  done

lemma liftB_liftA_zero_one: "
  liftB a @ liftA b = [teA y]
  \<Longrightarrow> a = [] \<and> b=[y]"
  apply(case_tac a)
   apply(clarsimp)
   apply(case_tac b)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(case_tac list)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(clarsimp)
  done

lemma liftB_prefixes_coincide: "
  liftB x @ a = liftB y @ b
  \<Longrightarrow> setB a = {} \<or> (\<exists>x v. a=teA x#v)
  \<Longrightarrow> setB b = {} \<or> (\<exists>x v. b=teA x#v)
  \<Longrightarrow> x=y"
  apply(subgoal_tac "prefix (liftB x) (liftB y) \<or> SSX" for SSX)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule_tac
      P="liftB x \<sqsubseteq> liftB y"
      in disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac c aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac aa list)(*strict*)
    apply(force)
   apply(rename_tac aa list)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac aa list)(*strict*)
    prefer 2
    apply(rule liftB_append)
    apply(force)
   apply(rename_tac aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa list l1 l2)(*strict*)
   apply(subgoal_tac "x=l1")
    apply(rename_tac aa list l1 l2)(*strict*)
    prefer 2
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac aa list l1 l2)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa list l2)(*strict*)
   apply(case_tac l2)
    apply(rename_tac aa list l2)(*strict*)
    apply(clarsimp)
   apply(rename_tac aa list cons_l2 aaa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa lista)(*strict*)
   apply(thin_tac "liftB x @ teB aa # liftB lista = liftB (x @ aa # lista)")
   apply (simp only: liftB_commutes_over_concat)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rule liftB_inj)
   apply(rule sym)
   apply(force)
  apply(rename_tac c aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac aa list)(*strict*)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac aa list)(*strict*)
   prefer 2
   apply(rule liftB_append)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa list l1 l2)(*strict*)
  apply(subgoal_tac "y=l1")
   apply(rename_tac aa list l1 l2)(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(force)
  apply(rename_tac aa list l1 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa list l2)(*strict*)
  apply(case_tac l2)
   apply(rename_tac aa list l2)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa list cons_l2 aaa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa lista)(*strict*)
  apply(thin_tac "liftB y @ teB aa # liftB lista = liftB (y @ aa # lista)")
  apply (simp only: liftB_commutes_over_concat)
  apply(erule_tac
      P="setB b = {}"
      in disjE)
   apply(rename_tac aa lista)(*strict*)
   apply(force)
  apply(rename_tac aa lista)(*strict*)
  apply(force)
  done

lemma liftB_butlast: "
  liftB (butlast (a @ b)) = butlast (liftB a @ liftB b)"
  apply(subgoal_tac "b=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   prefer 2
   apply(clarsimp)
   apply(rename_tac w' a')(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply (metis liftB.simps(2) liftB_commute_one_elem_app liftB_commutes_over_concat append_is_Nil_conv append_self_conv2 butlast_snoc_2 insert_Nil n_not_Suc_n rotate_simps snoc_eq_iff_butlast)
  apply(clarsimp)
  apply(subgoal_tac "a=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma in_set_butlast_append: "
  S2 ! n \<notin> set (butlast (S2 @ S2'))
  \<Longrightarrow> n<length S2
  \<Longrightarrow> S2' \<noteq> []
  \<Longrightarrow> Q"
  apply(subgoal_tac "S2 ! n \<in> set (butlast (S2 @ S2'))")
   apply(force)
  apply(thin_tac "S2 ! n \<notin> set (butlast (S2 @ S2'))")
  apply(subgoal_tac "S2'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(erule exE)+
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="S2'"
      and s="w'@[a']"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="butlast (S2 @ w' @ [a'])"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      A="set S2"
      in set_mp)
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule nth_mem)
  apply(force)
  done

lemma in_set_butlast_append2: "
  S2 ! n \<notin> set (butlast (S2 @ S2'))
  \<Longrightarrow> Suc n<length S2
  \<Longrightarrow> Q"
  apply(case_tac "S2'=[]")
   prefer 2
   apply(rule_tac
      ?S2.0="S2"
      in in_set_butlast_append)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "S2 ! n \<in> set (butlast (S2 @ S2'))")
   apply(force)
  apply(thin_tac "S2 ! n \<notin> set (butlast (S2 @ S2'))")
  apply(subgoal_tac "S2'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "S2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rule_tac
      t="(w' @ [a']) ! n"
      and s="w' ! n"
      in ssubst)
   apply(rename_tac w' a')(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule nth_mem)
  apply(force)
  done

lemma equal_by_length_and_prefix_of_greater: "
  length w1 = length w2
  \<Longrightarrow> prefix w1 v
  \<Longrightarrow> prefix w2 v
  \<Longrightarrow> w1=w2"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done
lemma strict_prefix_from_prefix_of_longer_and_shorter: "
  prefix w1 v
  \<Longrightarrow> prefix w2 v
  \<Longrightarrow> length w1 < length w2
  \<Longrightarrow> strict_prefix w1 w2"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(subgoal_tac "strict_prefix w1 w2 \<or> SSX" for SSX)
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac c ca)(*strict*)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma error_free_compatible_solution_exists: "
  ERROR x (n::nat)
  \<Longrightarrow> (\<And>x. P x x)
  \<Longrightarrow> (\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c)
  \<Longrightarrow> (\<And>x n. ERROR x n \<Longrightarrow> n>0 \<Longrightarrow> (\<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n'<n))
  \<Longrightarrow> (\<exists>x'. P x' x \<and> ERROR x' 0)"
  apply(induct n arbitrary: x rule: less_induct)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac x)
   apply(rename_tac x xa)(*strict*)
   apply(thin_tac "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c")
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xa nat)(*strict*)
  apply(clarify)
  apply(subgoal_tac "\<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < Suc nat")
   apply(rename_tac x xa nat)(*strict*)
   prefer 2
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. (\<And>n. ERROR xa n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < n)"
      in meta_allE)
   apply(erule_tac
      x="Suc nat"
      and P="\<lambda>X. (ERROR xa X \<Longrightarrow> 0 < X \<Longrightarrow> \<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < X)"
      in meta_allE)
   apply(rename_tac x xa nat)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x xa nat)(*strict*)
    apply(force)
   apply(rename_tac x xa nat)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x xa nat)(*strict*)
    apply(force)
   apply(rename_tac x xa nat)(*strict*)
   apply(force)
  apply(rename_tac x xa nat)(*strict*)
  apply(clarify)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule_tac
      x="n'"
      in meta_allE)
  apply(erule_tac
      x="x'"
      and P="\<lambda>x. (n' < Suc nat \<Longrightarrow> ERROR x n' \<Longrightarrow> (\<And>x. P x x) \<Longrightarrow> (\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c) \<Longrightarrow> (\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n) \<Longrightarrow> \<exists>x'. P x' x \<and> ERROR x' 0)"
      in meta_allE)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n')(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n')(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' xb)(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' a b c)(*strict*)
   apply(subgoal_tac "P a c")
    apply(rename_tac x xa nat x' n' a b c)(*strict*)
    apply(force)
   apply(rename_tac x xa nat x' n' a b c)(*strict*)
   apply(thin_tac "\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n")
   apply(thin_tac "\<And>x. P x x")
   apply(erule_tac
      x="a"
      in meta_allE)
   apply(erule_tac
      x="b"
      in meta_allE)
   apply(erule_tac
      x="c"
      in meta_allE)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' xb n)(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(clarify)
  apply(rename_tac x xa nat x' n' x'a)(*strict*)
  apply(rule_tac
      x="x'a"
      in exI)
  apply(rule conjI)
   apply(rename_tac x xa nat x' n' x'a)(*strict*)
   apply(thin_tac "\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n")
   apply(thin_tac "\<And>x. P x x")
   apply(erule_tac
      x="x'a"
      in meta_allE)
   apply(erule_tac
      x="x'"
      in meta_allE)
   apply(erule_tac
      x="xa"
      in meta_allE)
   apply(force)
  apply(rename_tac x xa nat x' n' x'a)(*strict*)
  apply(force)
  done

lemma error_free_compatible_solution_exists2: "
  ERROR x (n::nat)
  \<Longrightarrow> (\<And>x. P x x)
  \<Longrightarrow> (\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c)
  \<Longrightarrow> (\<And>x n. ERROR x n \<Longrightarrow> n>0 \<Longrightarrow> (\<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n'<n))
  \<Longrightarrow> (\<And>x y n. ERROR x 0 \<Longrightarrow> ERROR y n \<Longrightarrow> P y x \<Longrightarrow> y = x \<and> n=0)
  \<Longrightarrow> (\<exists>x' n'. P x' x \<and> ERROR x' n'
  \<and> (\<forall>x'' n''. P x'' x' \<and> ERROR x'' n'' \<longrightarrow> x''=x' \<and> n'=n''))"
  apply(induct n arbitrary: x rule: less_induct)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac x)
   apply(rename_tac x xa)(*strict*)
   apply(thin_tac "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c")
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(force)
  apply(rename_tac x xa nat)(*strict*)
  apply(clarify)
  apply(subgoal_tac "\<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < Suc nat")
   apply(rename_tac x xa nat)(*strict*)
   prefer 2
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. (\<And>n. ERROR xa n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < n)"
      in meta_allE)
   apply(erule_tac
      x="Suc nat"
      and P="\<lambda>X. (ERROR xa X \<Longrightarrow> 0 < X \<Longrightarrow> \<exists>x' n'. P x' xa \<and> ERROR x' n' \<and> n' < X)"
      in meta_allE)
   apply(rename_tac x xa nat)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x xa nat)(*strict*)
    apply(force)
   apply(rename_tac x xa nat)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x xa nat)(*strict*)
    apply(force)
   apply(rename_tac x xa nat)(*strict*)
   apply(force)
  apply(rename_tac x xa nat)(*strict*)
  apply(clarify)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule_tac
      x="n'"
      in meta_allE)
  apply(erule_tac
      x="x'"
      and P="\<lambda>x'. (n' < Suc nat \<Longrightarrow> ERROR x' n' \<Longrightarrow> (\<And>x. P x x) \<Longrightarrow> (\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> P a c) \<Longrightarrow> (\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n) \<Longrightarrow> (\<And>x y n. ERROR x 0 \<Longrightarrow> ERROR y n \<Longrightarrow> P y x \<Longrightarrow> y = x \<and> n = 0) \<Longrightarrow> \<exists>x'a n'. P x'a x' \<and> ERROR x'a n' \<and> (\<forall>x'' n''. P x'' x'a \<and> ERROR x'' n'' \<longrightarrow> x'' = x'a \<and> n' = n''))"
      in meta_allE)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n')(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n')(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' xb)(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' a b c)(*strict*)
   apply(subgoal_tac "P a c")
    apply(rename_tac x xa nat x' n' a b c)(*strict*)
    apply(force)
   apply(rename_tac x xa nat x' n' a b c)(*strict*)
   apply(thin_tac "\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n")
   apply(thin_tac "\<And>x. P x x")
   apply(thin_tac "\<And>x y n. ERROR x 0 \<Longrightarrow> ERROR y n \<Longrightarrow> P y x \<Longrightarrow> y = x \<and> n = 0")
   apply(erule_tac
      x="a"
      in meta_allE)
   apply(erule_tac
      x="b"
      in meta_allE)
   apply(erule_tac
      x="c"
      in meta_allE)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' xb n)(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xa nat x' n' xb y n)(*strict*)
   apply(force)
  apply(rename_tac x xa nat x' n')(*strict*)
  apply(clarify)
  apply(rename_tac x xa nat x' n' x'a n'a)(*strict*)
  apply(rule_tac
      x="x'a"
      in exI)
  apply(rule_tac
      x="n'a"
      in exI)
  apply(rule conjI)
   apply(rename_tac x xa nat x' n' x'a n'a)(*strict*)
   apply(thin_tac "\<And>x n. ERROR x n \<Longrightarrow> 0 < n \<Longrightarrow> \<exists>x' n'. P x' x \<and> ERROR x' n' \<and> n' < n")
   apply(thin_tac "\<And>x. P x x")
   apply(thin_tac "\<And>x y n. ERROR x 0 \<Longrightarrow> ERROR y n \<Longrightarrow> P y x \<Longrightarrow> y = x \<and> n = 0")
   apply(erule_tac
      x="x'a"
      in meta_allE)
   apply(erule_tac
      x="x'"
      in meta_allE)
   apply(erule_tac
      x="xa"
      in meta_allE)
   apply(force)
  apply(rename_tac x xa nat x' n' x'a n'a)(*strict*)
  apply(force)
  done

lemma butn_butlast: "
  butn (butlast x) n = butn x (Suc n)"
  apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: butn_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: butn_def)
  done

lemma split_inst_step_stay_hlp2: "
        fromS1 @ f # fromw' @ [froma'] =
        [ini] # toS1 @ t # tow'
  \<Longrightarrow> length fromS1 = length toS1
       \<Longrightarrow> fromS1 @ f # (B # t) # fromw' @ [froma'] =
          [ini] # toS1 @ (B # t) # t # tow'"
  apply(case_tac fromS1)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(subgoal_tac "toS1=[] \<or> (\<exists>w' a'. toS1=w'@[a'])")
   apply(rename_tac list)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac list)(*strict*)
  apply(erule disjE)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(clarsimp)
  done

lemma take_restrict: "
  n<length w1
  \<Longrightarrow> take (Suc n) w1 = w2 @ [x]
  \<Longrightarrow> take n w1 = w2"
  apply (metis butn_prefix_closureise last_snoc take_Suc_conv_app_nth)
  done

lemma butn_butlast2: "
  butlast (butn x n) = butn (butlast x) n"
  apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
   apply(simp add: butn_def)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(simp add: butn_def)
  apply(case_tac n)
   apply(rename_tac w' a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' a' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' nat)(*strict*)
  apply(subgoal_tac "take (length w' - nat) w'=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac w' nat)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac w' nat)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' nat)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' nat w'a a')(*strict*)
  apply(case_tac "length w'")
   apply(rename_tac w' nat w'a a')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' nat w'a a' nata)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc nata\<le> nat")
   apply(rename_tac w' nat w'a a' nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' nat w'a a' nata)(*strict*)
  apply(subgoal_tac "nat < Suc nata")
   apply(rename_tac w' nat w'a a' nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w' nat w'a a' nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k. nat + Suc k = Suc nata")
   apply(rename_tac w' nat w'a a' nata)(*strict*)
   prefer 2
   apply (metis add_Suc add_Suc_shift less_iff_Suc_add)
  apply(rename_tac w' nat w'a a' nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' nat w'a a' k)(*strict*)
  apply (metis less_iff_Suc_add add.commute take_restrict)
  done

lemma butn_take_butlast: "
  k \<le> length (butlast w)
  \<Longrightarrow> butn w ((length w) - k) = take k (butlast w)"
  apply(simp add: butn_def)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma liftA_butn: "
  liftA (butn x n) = butn (liftA x) n"
  apply(induct x arbitrary: n rule: rev_induct)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: butn_def)
  apply(rename_tac x xs n)(*strict*)
  apply(case_tac n)
   apply(rename_tac x xs n)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs)(*strict*)
   apply(simp add: butn_def)
  apply(rename_tac x xs n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs nat)(*strict*)
  apply(simp add: butn_def)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply (metis liftA_preserves_length diff_Suc_Suc diff_less_Suc length_Suc take_liftA take_shorter_butlast)
  done

lemma maxTermPrefix_liftA: "
  maxTermPrefix (liftA v) = []"
  apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_liftA)
  done

lemma liftA_arg_cong_indirect: "
  c=d
  \<Longrightarrow> a=liftA c
  \<Longrightarrow> b=liftA d
  \<Longrightarrow> a=b"
  apply(force)
  done

lemma prefix_of_liftB_prefixes: "
  liftB a @ liftA b = liftB c @ x
  \<Longrightarrow> prefix c a"
  apply(subgoal_tac "prefix (liftB a) (liftB c) \<or> SSX" for SSX)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ca)(*strict*)
    prefer 2
    apply(rule liftB_append)
    apply(force)
   apply(rename_tac ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac l1 l2)(*strict*)
   apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
   apply(subgoal_tac "a=l1")
    apply(rename_tac l1 l2)(*strict*)
    apply(clarsimp)
    apply(rename_tac l2)(*strict*)
    apply(rule liftB_inj)
    apply(clarsimp)
    apply(case_tac l2)
     apply(rename_tac l2)(*strict*)
     apply(clarsimp)
    apply(rename_tac cons_l2 aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac aa list)(*strict*)
    apply (simp only: liftB_commutes_over_concat)
    apply(clarsimp)
    apply(rename_tac a list)(*strict*)
    apply(case_tac b)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac l1 l2)(*strict*)
   apply(rule liftB_inj)
   apply(force)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(rule liftB_append)
   apply(force)
  apply(rename_tac ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac l1 l2)(*strict*)
  apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
  apply(subgoal_tac "c=l1")
   apply(rename_tac l1 l2)(*strict*)
   apply(clarsimp)
  apply(rename_tac l1 l2)(*strict*)
  apply(rule liftB_inj)
  apply(force)
  done

lemma foldl_length_eq: "
  (length x = length y)
  \<Longrightarrow> (\<And>i. i<length x \<Longrightarrow> i<length y \<Longrightarrow> (length (x!i) = length (y!i)))
  \<Longrightarrow> length (foldl (@) [] x) = length (foldl (@) [] y)"
  apply(induct x arbitrary: y)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x y)(*strict*)
  apply(clarsimp)
  apply(case_tac y)
   apply(rename_tac a x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac a x y aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a x aa list)(*strict*)
  apply(rename_tac a x b y)
  apply(rename_tac a x b y)(*strict*)
  apply(rule_tac
      t="foldl (@) a x"
      in ssubst)
   apply(rename_tac a x b y)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a x b y)(*strict*)
  apply(rule_tac
      t="foldl (@) b y"
      in ssubst)
   apply(rename_tac a x b y)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a x b y)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="length a"
      and s="length b"
      in ssubst)
   apply(rename_tac a x b y)(*strict*)
   apply(erule_tac
      x="0"
      in meta_allE)
   apply(force)
  apply(rename_tac a x b y)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="y"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a x b y i)(*strict*)
   apply(erule_tac
      x="Suc i"
      in meta_allE)
   apply(force)
  apply(rename_tac a x b y)(*strict*)
  apply(force)
  done

lemma foldl_preserves_prefix: "
  prefix w v
  \<Longrightarrow> prefix (foldl (@) [] w) (foldl (@) [] v)"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) a w"
      in ssubst)
   apply(rename_tac a w v)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w v)(*strict*)
  apply(case_tac v)
   apply(rename_tac a w v)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac a w v aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w aa list)(*strict*)
  apply(subgoal_tac "a=aa")
   apply(rename_tac a w aa list)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
  apply(rename_tac a w aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w aa list)(*strict*)
  apply(rule_tac
      t="foldl (@) aa list"
      in ssubst)
   apply(rename_tac w aa list)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac w aa list)(*strict*)
  apply(erule_tac
      x="list"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac w aa list)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac w aa list)(*strict*)
  apply(simp add: prefix_def)
  done

lemma take_is_prefix: "
  prefix (take n w) w"
  apply(simp add: prefix_def)
  apply(rule_tac
      x="drop n w"
      in exI)
  apply(rule append_take_drop_id)
  done

lemma map_foldl: "
  map g (foldl (@) [] w) = foldl (@) [] (map (map g) w)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) a w"
      in ssubst)
   apply(rename_tac a w)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w)(*strict*)
  apply(rule_tac
      t="foldl (@) (map g a) (map (map g) w)"
      in ssubst)
   apply(rename_tac a w)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma equal_by_embedding_and_AX_equal_length: "
  prefix (w@a) x
  \<Longrightarrow> prefix (v@b) y
  \<Longrightarrow> x=y
  \<Longrightarrow> w=v
  \<Longrightarrow> length a=length b
  \<Longrightarrow> a = b"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma prefix_append_bigger: "
  prefix a b
  \<Longrightarrow> prefix a (b@c)"
  apply(simp add: prefix_def)
  apply(force)
  done
lemma foldl_take_length: "
  length (foldl (@) [] (take n w)) \<le> length (foldl (@) [] w)"
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
  apply(rename_tac a w nat)(*strict*)
  apply(rule_tac
      t="foldl (@) a (take nat w)"
      in ssubst)
   apply(rename_tac a w nat)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w nat)(*strict*)
  apply(rule_tac
      t="foldl (@) a w"
      in ssubst)
   apply(rename_tac a w nat)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w nat)(*strict*)
  apply(force)
  done

lemma compatible_by_embedding: "
  prefix (w@a) x
  \<Longrightarrow> prefix (v@b) y
  \<Longrightarrow> x=y
  \<Longrightarrow> w=v
  \<Longrightarrow> \<exists>k1 k2. a@k1 = b@k2"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule_tac
      x="ca"
      in exI)
  apply(force)
  done

lemma liftB_eq_liftA_empty: "
  liftB x = liftA y
  \<Longrightarrow> x=[] \<and> y=[]"
  apply(case_tac x)
   apply(clarsimp)
   apply(case_tac y)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac y)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  done

lemma drop_not_empty: "
  drop n w \<noteq> []
  \<Longrightarrow> length w>n"
  apply(force)
  done

lemma drop_nth_hlp1: "
  drop n w = a # b # v
  \<Longrightarrow> w ! Suc n = b"
  apply (metis nth_drop2 drop_Suc drop_not_empty list.simps(2) nth_first List.list.sel tl_drop)
  done

lemma drop_nth_hlp2: "
  drop n w = a # b # v
  \<Longrightarrow> w ! n = a"
  apply (metis nth_drop2 drop_Suc drop_not_empty list.simps(2) nth_first List.list.sel tl_drop)
  done

lemma length2_string_has_two_elems: "
  length w = Suc (Suc 0)
  \<Longrightarrow> \<exists>a b. w=[a,b]"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista)(*strict*)
  apply(case_tac lista)
   apply(rename_tac list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista aa listb)(*strict*)
  apply(clarsimp)
  done

lemma two_prefixes_are_prefix: "
  strict_prefix x y
  \<Longrightarrow> prefix w (drop(length x)y)
  \<Longrightarrow> prefix (x@w) y"
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  done

lemma two_prefixes_are_prefix_and_equal: "
  strict_prefix x y
  \<Longrightarrow> w = (drop(length x)y)
  \<Longrightarrow> (x@w) = y"
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  done

lemma strict_prefix_prefix_from_common_bigger: "
  prefix a x
  \<Longrightarrow> prefix b x
  \<Longrightarrow> strict_prefix a b \<or> strict_prefix b a \<or> a=b"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(subgoal_tac "strict_prefix a b \<or> SSX " for SSX)
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac c ca)(*strict*)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(simp add: prefix_def strict_prefix_def)
  apply(clarsimp)
  done

lemma drop_not_empty_if_len: "
  n<length w
  \<Longrightarrow> drop n w \<noteq> []"
  apply(force)
  done

lemma prefix_drop_is_difference: "
  prefix w x
  \<Longrightarrow> w@(drop(length w)x)=x"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma left_context_empty: "
  setA l={}
  \<Longrightarrow> liftA x=l@y
  \<Longrightarrow> l=[]"
  apply(case_tac l)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b)(*strict*)
  apply(case_tac x)
   apply(rename_tac list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac list b a lista)(*strict*)
  apply(clarsimp)
  done

lemma liftA_AA: "
  liftA l=[teA A,teA B]
  \<Longrightarrow> l=[A,B]"
  apply(case_tac l)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac lista)(*strict*)
  apply(case_tac lista)
   apply(rename_tac lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac lista a list)(*strict*)
  apply(clarsimp)
  done

lemma liftA_BA: "
  liftA l=[teB A,teA B]
  \<Longrightarrow> Q"
  apply(case_tac l)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma liftA_A: "
  liftA l=[teA A]
  \<Longrightarrow> l=[A]"
  apply(case_tac l)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista)(*strict*)
  apply(clarsimp)
  done

lemma liftA_AAw: "
  liftA v =
        teA A #
        teA B # liftA y
  \<Longrightarrow> v=[A,B]@y"
  apply(case_tac v)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(case_tac list)
   apply(rename_tac list)(*strict*)
   apply(clarsimp)
  apply(rename_tac list a lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac lista)(*strict*)
  apply(rule liftA_inj)
  apply(force)
  done

lemma liftA_Aw: "
  liftA v =
        teA B # liftA y
  \<Longrightarrow> v=[B]@y"
  apply(case_tac v)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(rule liftA_inj)
  apply(force)
  done

lemma equal_by_same_length_and_equal_embedding: "
  map f x1 = map f x2
  \<Longrightarrow> prefix w1 (drop x x1)
  \<Longrightarrow> prefix w2 (drop x x2)
  \<Longrightarrow> length w1=length w2
  \<Longrightarrow> length x1=length x2
  \<Longrightarrow> map f w1=map f w2"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply (metis drop_map takePrecise take_map)
  done

lemma prefix_is_equal_by_length: "
  prefix a b
  \<Longrightarrow> length a = length b
  \<Longrightarrow> a=b"
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma terminal_set_elem: "
  teB b \<in> set(liftB w)
  \<Longrightarrow> b\<in> set w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma helpY: "
  liftB x @ teA A # w @ teB B # v = liftB w1X @ liftA w2X
  \<Longrightarrow> Q"
  apply(case_tac w2X)
   apply(clarsimp)
   apply (metis list.simps(3) maximalPrefixB_liftB maximalPrefixB_prefix2_prime self_append_conv)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "x=w1X")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply (metis setB_liftA elemInsetB empty_iff)
  apply(rule leading_liftB_prefix_eq)
  apply(force)
  done

lemma not_contained_filter_list_empty: "
  x0 \<notin> set preW
  \<Longrightarrow> length [x\<leftarrow>preW . x = x0] = 0"
  apply(induct preW)
   apply(clarsimp)
  apply(rename_tac a preW)(*strict*)
  apply(clarsimp)
  done

lemma nth_in_setA_subset: "
  setA w \<subseteq> A
  \<Longrightarrow> i<length w
  \<Longrightarrow> w ! i = teA a
  \<Longrightarrow> a \<in> A"
  apply (metis nth_mem set_setA subsetD)
  done

lemma nth_in_setB_subset: "
  setB w \<subseteq> A
  \<Longrightarrow> i<length w
  \<Longrightarrow> w ! i = teB a
  \<Longrightarrow> a \<in> A"
  apply (metis nth_mem set_setB subsetD)
  done

lemma split_signature_length3: "
  \<forall>x\<in> set w'. \<exists>y. f x = Some y
  \<Longrightarrow> length (foldl (@) [] (map (option_to_list \<circ> f) w')) = length w'"
  apply(induct w')
   apply(clarsimp)
  apply(rename_tac a w')(*strict*)
  apply(clarsimp)
  apply(rename_tac a w' y)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rule_tac
      t="foldl (@) [y] (map (option_to_list \<circ> f) w')"
      and s="[y]@(foldl (@) [] (map (option_to_list \<circ> f) w'))"
      in ssubst)
   apply(rename_tac a w' y)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w' y)(*strict*)
  apply(force)
  done

lemma setA_foldl_elem: "
  x \<in> setA (foldl (@) [] w)
  \<Longrightarrow> \<exists>y\<in> set w. x \<in> setA y"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply (metis filterA_distrib_append filterA_preserves_setA foldl_first not_set_append)
  done

lemma setB_foldl_elem: "
  x \<in> setB (foldl (@) [] w)
  \<Longrightarrow> \<exists>y\<in> set w. x \<in> setB y"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply (metis foldl_first not_in_setBI not_set_append set_setB)
  done

lemma equal_split_prefix__contra_case: "
  foldl (@) [] \<pi>s2 @ c = foldl (@) [] (take (length \<pi>s1) \<pi>s2)
  \<Longrightarrow> c\<noteq> []
  \<Longrightarrow> False"
  apply(subgoal_tac "length (foldl (@) [] \<pi>s2 @ c) > length (foldl (@) [] (take (length \<pi>s1) \<pi>s2))")
   apply(force)
  apply(thin_tac "foldl (@) [] \<pi>s2 @ c = foldl (@) [] (take (length \<pi>s1) \<pi>s2)")
  apply(subgoal_tac "length (foldl (@) [] (take (length \<pi>s1) \<pi>s2)) \<le> length (foldl (@) [] \<pi>s2)")
   apply(clarsimp)
   apply(case_tac c)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(thin_tac "c\<noteq>[]")
  apply(induct \<pi>s2 arbitrary: \<pi>s1)
   apply(rename_tac \<pi>s1)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<pi>s2 \<pi>s1)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (a # \<pi>s2)"
      and s="a@foldl (@) [] (\<pi>s2)"
      in ssubst)
   apply(rename_tac a \<pi>s2 \<pi>s1)(*strict*)
   apply (metis concat.simps(2) concat_conv_foldl)
  apply(rename_tac a \<pi>s2 \<pi>s1)(*strict*)
  apply(case_tac \<pi>s1)
   apply(rename_tac a \<pi>s2 \<pi>s1)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>s2 \<pi>s1 aa list)(*strict*)
  apply(rule_tac
      t="take (length \<pi>s1) (a # \<pi>s2)"
      and s="a#(take (length list) (\<pi>s2))"
      in ssubst)
   apply(rename_tac a \<pi>s2 \<pi>s1 aa list)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>s2 \<pi>s1 aa list)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (a # take (length list) \<pi>s2)"
      and s="a@foldl (@) [] (take (length list) \<pi>s2)"
      in ssubst)
   apply(rename_tac a \<pi>s2 \<pi>s1 aa list)(*strict*)
   apply (metis concat.simps(2) concat_conv_foldl)
  apply(rename_tac a \<pi>s2 \<pi>s1 aa list)(*strict*)
  apply(force)
  done

lemma equal_split_prefix__contra_case2: "
  foldl (@) [] \<pi>s2 @ c = foldl (@) [] (take (length \<pi>s1) \<pi>s2)
  \<Longrightarrow> (\<And>x. x\<in> set \<pi>s2 \<Longrightarrow> x \<noteq> [])
  \<Longrightarrow> length \<pi>s1 < length \<pi>s2
  \<Longrightarrow> False"
  apply(subgoal_tac "length (foldl (@) [] \<pi>s2 @ c) > length (foldl (@) [] (take (length \<pi>s1) \<pi>s2))")
   apply(force)
  apply(thin_tac "foldl (@) [] \<pi>s2 @ c = foldl (@) [] (take (length \<pi>s1) \<pi>s2)")
  apply(subgoal_tac "length (foldl (@) [] (take (length \<pi>s1) \<pi>s2)) < length (foldl (@) [] \<pi>s2)")
   apply(clarsimp)
  apply(rule_tac
      y="length(foldl (@) [] ((take (length \<pi>s1) \<pi>s2)@[\<pi>s2!(length \<pi>s1)]))"
      in less_le_trans)
   apply(rule_tac
      t="foldl (@) [] (take (length \<pi>s1) \<pi>s2 @ [\<pi>s2 ! length \<pi>s1])"
      and s="foldl (@) [] (take (length \<pi>s1) \<pi>s2) @ (\<pi>s2 ! length \<pi>s1)"
      in ssubst)
    apply (metis foldl_tail take_Suc_conv_app_nth)
   apply(clarsimp)
  apply(rule_tac
      P="\<lambda>X. length (foldl (@) [] (take (length \<pi>s1) \<pi>s2 @ [\<pi>s2 ! length \<pi>s1])) \<le> length (foldl (@) [] X)"
      and t="\<pi>s2"
      and s="take SSi SSxs @ SSxs ! SSi # drop (Suc SSi) SSxs" for SSi SSxs
      in ssubst)
   apply(rule_tac
      i="length \<pi>s1"
      in id_take_nth_drop)
   apply(force)
  apply(rule_tac
      t="take (length \<pi>s1) \<pi>s2 @ \<pi>s2 ! length \<pi>s1 # drop (Suc (length \<pi>s1)) \<pi>s2"
      and s="take (length \<pi>s1) \<pi>s2 @ [\<pi>s2 ! length \<pi>s1] @ drop (Suc (length \<pi>s1)) \<pi>s2"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="length (foldl (@) [] (take (length \<pi>s1) \<pi>s2 @ [\<pi>s2 ! length \<pi>s1] @ drop (Suc (length \<pi>s1)) \<pi>s2))"
      and s="length (foldl (@) [] SSw) + length (foldl (@) [] SSv) " for SSw SSv
      in ssubst)
   apply(rule length_foldl_append)
  apply(rule_tac
      t="length (foldl (@) [] (take (length \<pi>s1) \<pi>s2 @ [\<pi>s2 ! length \<pi>s1]))"
      and s="length (foldl (@) [] SSw) + length (foldl (@) [] SSv) " for SSw SSv
      in ssubst)
   apply(rule length_foldl_append)
  apply(rule_tac
      t="length (foldl (@) [] ([\<pi>s2 ! length \<pi>s1] @ drop (Suc (length \<pi>s1)) \<pi>s2))"
      and s="length (foldl (@) [] SSw) + length (foldl (@) [] SSv) " for SSw SSv
      in ssubst)
   apply(rule length_foldl_append)
  apply(force)
  done

lemma set_elem_has_context: "
  x \<in> set w
  \<Longrightarrow> \<exists>w1 w2. w = w1 @ [x] @ w2"
  apply (metis ConsApp in_set_conv_decomp)
  done

lemma take_length: "
  k\<le>length w
  \<Longrightarrow> length (take k w) = k"
  apply(force)
  done

lemma nth_equal_by_take_equal: "
  take n w = take m v
  \<Longrightarrow> k<n
  \<Longrightarrow> k<m
  \<Longrightarrow> w!k = v!k"
  apply (metis nth_take)
  done

lemma foldl_last: "
  foldl (@) [] (w @ [X]) = foldl (@) [] w @ X"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma equal_by_strict_prefix_alt: "
  (strict_prefix w1 w2 \<Longrightarrow> False)
  \<Longrightarrow> (strict_prefix w2 w1 \<Longrightarrow> False)
  \<Longrightarrow> w1@v1=w2@v2
  \<Longrightarrow> w1=w2"
  apply(subgoal_tac "prefix w1 w2 \<or> prefix w2 w1")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(case_tac "strict_prefix w1 w2")
    apply(force)
   apply(simp add: strict_prefix_def prefix_def)
   apply(force)
  apply(case_tac "strict_prefix w2 w1")
   apply(force)
  apply(simp add: strict_prefix_def prefix_def)
  apply(force)
  done

lemma map_empty_eq: "
  length w1=length w2
  \<Longrightarrow> map (\<lambda>x. []) w1= map (\<lambda>x. []) w2"
  apply(rule listEqI)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma nth_dropX: "
  n<length w
  \<Longrightarrow> w ! n = drop n w ! 0"
  apply (metis nth_drop Nat.add_0_right)
  done

lemma equal_split_prefix_hlp1_take_and_butlast: "
  length fw=Suc(length v)
  \<Longrightarrow> n\<le>length v
  \<Longrightarrow> take (length v - n) (drop n fw) = butlast (drop n fw)"
  apply(subgoal_tac "drop n fw=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "length (w'@[a']) = length fw - n")
   apply(rename_tac w' a')(*strict*)
   prefer 2
   apply(rule_tac
      t="w'@[a']"
      and s="drop n fw"
      in ssubst)
    apply(rename_tac w' a')(*strict*)
    apply(force)
   apply(rename_tac w' a')(*strict*)
   apply(simp (no_asm))
  apply(rename_tac w' a')(*strict*)
  apply(clarsimp)
  done

lemma e_derivation_at_tail_exists_hlp1: "
  i<length w
  \<Longrightarrow> i<length fw
  \<Longrightarrow> fw ! i = w! i
  \<Longrightarrow> drop i w = fw ! i # drop (Suc i) w"
  apply(rule_tac
      t="fw!i"
      and s="w!i"
      in ssubst)
   apply(force)
  apply(thin_tac "fw!i=w!i")
  apply (metis List.Cons_nth_drop_Suc)
  done

lemma strict_prefix_prefix_alt: "
  strict_prefix w (v@x)
  \<Longrightarrow> \<not> prefix w v
  \<Longrightarrow> \<exists>y. v@y=w \<and> strict_prefix y x"
  apply(simp add: prefix_def strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "prefix w v \<or> prefix v w")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(erule disjE)
   apply(rename_tac c)(*strict*)
   apply(simp add: prefix_def strict_prefix_def)
  apply(rename_tac c)(*strict*)
  apply(simp add: prefix_def strict_prefix_def)
  apply(clarsimp)
  done

lemma in_butlast: "
  i<length w'
  \<Longrightarrow> w' ! i \<in> set (butlast (w' @ a' # v))"
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w'a a'a)(*strict*)
  apply (metis append_Cons butlast_snoc_2 nth_mem set_append_contra1)
  done

lemma suffix_drop: "
  suffix w v
  \<Longrightarrow> length w-n\<ge>length v-m
  \<Longrightarrow> suffix (drop n w) (drop m v)"
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac "n-length c")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="drop n c @ take m v"
      in exI)
   apply(force)
  apply(rename_tac c nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "n=Suc nat+length c")
   apply(rename_tac c nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "length v-m")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length v=Suc nata+m")
   apply(rename_tac nat nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k. Suc nata+k=nata+m-nat")
   apply(rename_tac nat nata)(*strict*)
   prefer 2
   apply(rule_tac
      x="nata+m-nat - Suc nata"
      in exI)
   apply(force)
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat nata k)(*strict*)
  apply(subgoal_tac "Suc(nata+k)+nat=nata+m")
   apply(rename_tac nat nata k)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat nata k)(*strict*)
  apply(thin_tac "Suc (nata + k) = nata + m - nat")
  apply(clarsimp)
  apply(rule_tac
      x="take k (drop (Suc nat) v)"
      in exI)
  apply (metis add_Suc add_Suc_shift append_take_drop_id drop_drop)
  done

lemma suffix_append: "
  suffix w v
  \<Longrightarrow> suffix (x@w) v"
  apply(simp add: suffix_def)
  apply(force)
  done

lemma shortest_dropper: "
  w1@v1=w2@v2
  \<Longrightarrow> w1 @ (drop(length w1) w2) = w2 @ (drop(length w2) w1)"
  apply(subgoal_tac "prefix w1 w2 \<or> SSX" for SSX)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma Min_less: "
  finite S
  \<Longrightarrow> S \<noteq> {}
  \<Longrightarrow> (\<exists>a\<in> S. a < n)
  \<Longrightarrow> Min S < n"
  apply(rule_tac
      t="Min S < n"
      in ssubst)
   apply(rule Min_less_iff)
    apply(force)
   apply(force)
  apply(force)
  done

lemma disjI_imp: "
  (\<not> P \<Longrightarrow> Q)
  \<Longrightarrow> P \<or> Q"
  apply(force)
  done

lemma nth_drop_set: "
  n<length w
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> w!n \<in> set(drop k w)"
  apply(case_tac k)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac k)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      P="\<lambda>X. X ! n \<in> set (drop (Suc k) w)"
      and s="take (Suc k)w@drop(Suc k)w"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply (metis append_take_drop_id)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="(take (Suc k) w @ drop (Suc k) w) ! n"
      and s="(drop (Suc k) w) ! (n-length(take (Suc k) w))"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      t="n - length (take (Suc k) w)"
      and s="n-Suc k"
      in ssubst)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(metis diff_less_mono length_drop less_eq_Suc_le_raw nth_mem)
  done

lemma nth_drop_prime: "
  n<length w
  \<Longrightarrow> n=k+i
  \<Longrightarrow> w!n = (drop k w)!i"
  apply (metis nth_drop)
  done

definition takeB :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeB n w \<equiv> drop (length w - n) w"

lemma for_all_in_set_by_takeB_induct: "
  (\<And>n. \<forall>x\<in> set (takeB n w). P x)
  \<Longrightarrow> \<forall>x\<in> set w. P x"
  apply(erule_tac
      x="length w"
      in meta_allE)
  apply(simp add: takeB_def)
  done

lemma for_all_in_set_by_takeB_induct_prime: "
  (\<And>ii x. Suc x \<le> length w \<Longrightarrow> ii < Suc x \<Longrightarrow> ii = 0 \<or> ii = x \<Longrightarrow> \<forall>x\<in> set (takeB x w). P x \<Longrightarrow> P (takeB (Suc x) w ! ii))
  \<Longrightarrow> \<forall>x\<in> set (takeB n w). P x"
  apply(induct n rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "\<exists>ii<length(takeB x w). (takeB x w)!ii=xa")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply (rule set_elem_nth)
   apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x ii)(*strict*)
  apply(case_tac "(length w) - ((length w) - x) = x")
   apply(rename_tac x ii)(*strict*)
   prefer 2
   apply(subgoal_tac "length (takeB x w) = length w")
    apply(rename_tac x ii)(*strict*)
    prefer 2
    apply(simp add: takeB_def)
   apply(rename_tac x ii)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
    apply(rename_tac x ii)(*strict*)
    apply(force)
   apply(rename_tac x ii nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac ii nat)(*strict*)
   apply(rename_tac x)
   apply(rename_tac ii x)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>y. (y < Suc x \<Longrightarrow> \<forall>x\<in>set (takeB y w). P x)"
      in meta_allE)
   apply(rename_tac ii x)(*strict*)
   apply(clarsimp)
   apply(rename_tac ii x)(*strict*)
   apply(erule_tac
      x="takeB (Suc x) w ! ii"
      in ballE)
    apply(rename_tac ii x)(*strict*)
    apply(force)
   apply(rename_tac ii x)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac ii x)(*strict*)
    apply(force)
   apply(rename_tac ii x)(*strict*)
   apply(simp add: takeB_def)
  apply(rename_tac x ii)(*strict*)
  apply(subgoal_tac "length (takeB x w) = x")
   apply(rename_tac x ii)(*strict*)
   prefer 2
   apply(simp add: takeB_def)
  apply(rename_tac x ii)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "x\<le>length w")
   apply(rename_tac x ii)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x ii)(*strict*)
  apply(clarsimp)
  apply(case_tac "ii>0 \<and> Suc ii<x")
   apply(rename_tac x ii)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
    apply(rename_tac x ii)(*strict*)
    apply(force)
   apply(rename_tac x ii nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac ii nat)(*strict*)
   apply(rename_tac x)
   apply(rename_tac ii x)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>y. (y < Suc x \<Longrightarrow> \<forall>x\<in>set (takeB y w). P x)"
      in meta_allE)
   apply(rename_tac ii x)(*strict*)
   apply(clarsimp)
   apply(rename_tac ii x)(*strict*)
   apply(erule_tac
      x="takeB (Suc x) w ! ii"
      in ballE)
    apply(rename_tac ii x)(*strict*)
    apply(force)
   apply(rename_tac ii x)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac ii x)(*strict*)
    apply(force)
   apply(rename_tac ii x)(*strict*)
   apply(simp add: takeB_def)
   apply(case_tac "length w")
    apply(rename_tac ii x)(*strict*)
    apply(clarsimp)
   apply(rename_tac ii x nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "w ! (nat + ii - x) \<in> set (drop (Suc nat - x) w)")
    apply(rename_tac ii x nat)(*strict*)
    apply(force)
   apply(rename_tac ii x nat)(*strict*)
   apply(rule nth_drop_set)
    apply(rename_tac ii x nat)(*strict*)
    apply(force)
   apply(rename_tac ii x nat)(*strict*)
   apply(case_tac ii)
    apply(rename_tac ii x nat)(*strict*)
    prefer 2
    apply(rename_tac ii x nat nata)(*strict*)
    apply(force)
   apply(rename_tac ii x nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x ii)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "ii=0 \<or> Suc ii=x")
   apply(rename_tac x ii)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac x ii)(*strict*)
    apply(force)
   apply(rename_tac x ii)(*strict*)
   apply(subgoal_tac "x\<le>Suc ii")
    apply(rename_tac x ii)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x ii)(*strict*)
   apply(subgoal_tac "x=Suc ii")
    apply(rename_tac x ii)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x ii)(*strict*)
   apply(force)
  apply(rename_tac x ii)(*strict*)
  apply(thin_tac "ii = 0 \<or> \<not> Suc ii < x")
  apply(case_tac x)
   apply(rename_tac x ii)(*strict*)
   apply(clarsimp)
  apply(rename_tac x ii nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac ii nat)(*strict*)
  apply(blast)
  done

lemma length_takeB_shorter: "
  n<length w \<or> v \<noteq> []
  \<Longrightarrow> x=(v @ w)
  \<Longrightarrow> length (takeB n w) < length x"
  apply(simp add: takeB_def)
  apply (metis add_diff_inverse diff_add_inverse length_greater_0_conv less_diff_conv less_imp_diff_less less_zeroE linorder_neqE_nat add.commute not_add_less2 order_less_not_sym trans_less_add2 zero_less_diff)
  done

lemma drop_butn: "
  drop n (butn w k) = butn (drop n w) k"
  apply(simp add: butn_def)
  apply(case_tac "length w-k")
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length w=Suc nat+k")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply (metis drop_take)
  done

lemma butlast_empty: "
  length w\<le> Suc 0
  \<Longrightarrow> butlast w = []"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(force)
  apply(clarsimp)
  done

lemma hlpXXX: "
  m\<le>n
  \<Longrightarrow> m \<le> n-(n-(m::nat))"
  apply(force)
  done

lemma last_nth_prime: "
  length w=Suc n
  \<Longrightarrow> w!n = last w"
  apply (metis last_nth2 self_append_conv)
  done

lemma sub_diff_null: "
  n+k-m \<le> n
  \<Longrightarrow> k-m = (0::nat)"
  apply(force)
  done

lemma XXYASD_hlp: "
  ig\<noteq>tbr
  \<Longrightarrow> tbr\<le>ig
  \<Longrightarrow> ig-tbr=(0::nat)
  \<Longrightarrow> Q"
  apply(force)
  done

lemma diff_is_0_eq_prime_prime: "
  n-m=(0::nat)
  \<Longrightarrow> n\<le>m"
  apply(metis diff_is_0_eq)
  done

lemma XX11: "
  m1\<le>(m2::nat)
  \<Longrightarrow> m1\<le>n1
  \<Longrightarrow> m2\<le>n2
  \<Longrightarrow> (n1-(n1-m1))\<le> (n2-(n2-m2))"
  apply(force)
  done

lemma Min_ge_absorb: "
  finite A
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> X \<le> Min A
  \<Longrightarrow> X \<le> Min ({X}\<union>A)"
  apply(rule_tac
      t="X \<le> Min ({X}\<union>A)"
      in ssubst)
   apply(rule Lattices_Big.linorder_class.Min_ge_iff)
    apply(force)
   apply(force)
  apply(force)
  done

lemma exI_2: "
  \<exists>a. P a b
  \<Longrightarrow> \<exists>a b. P a b"
  apply(force)
  done

lemma exI_3: "
  \<exists>a b. P a b c
  \<Longrightarrow> \<exists>a b c. P a b c"
  apply(force)
  done

lemma exI_4: "
  \<exists>a b c. P a b c d
  \<Longrightarrow> \<exists>a b c d. P a b c d"
  apply(force)
  done

lemma allE_2: "
  \<forall>a b. P a b
  \<Longrightarrow> (\<forall>a. P a x \<Longrightarrow> R)
  \<Longrightarrow> R"
  apply(force)
  done

lemma allE_3: "
  \<forall>a b c. P a b c
  \<Longrightarrow> (\<forall>a b. P a b x \<Longrightarrow> R)
  \<Longrightarrow> R"
  apply(force)
  done

lemma allE_4: "
  \<forall>a b c d. P a b c d
  \<Longrightarrow> (\<forall>a b c. P a b c x \<Longrightarrow> R)
  \<Longrightarrow> R"
  apply(force)
  done

lemma drop_length_prime: "
  drop n w = v
  \<Longrightarrow> length w - n = length v"
  apply(force)
  done

lemma drop_length2: "
  drop n w = v
  \<Longrightarrow> x=length w - n
  \<Longrightarrow> y=length v
  \<Longrightarrow> y=x"
  apply(force)
  done

lemma in_set_with_context: "
  w1@w2@[x]@w3 =w1@w4
  \<Longrightarrow> x \<in> set w4"
  apply(clarsimp)
  done

lemma length_smaller: "
  length S \<le> length w
  \<Longrightarrow> length (foldl (@) [] (map (option_to_list \<circ> f) S)) \<le> length w"
  apply(induct S arbitrary: w rule: rev_induct)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. w=w'@[a'])")
   apply(rename_tac x xs w)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x xs w)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs w)(*strict*)
   apply(force)
  apply(rename_tac x xs w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w')(*strict*)
  apply(erule_tac
      x="w'"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac "f x")
   apply(rename_tac x xs w')(*strict*)
   apply(force)
  apply(rename_tac x xs w' a)(*strict*)
  apply(force)
  done

lemma length_strictly_smaller: "
  length S \<le> length w
  \<Longrightarrow> f (S ! n) = None
  \<Longrightarrow> n<length S
  \<Longrightarrow> length (foldl (@) [] (map (option_to_list \<circ> f) S)) < length w"
  apply(rule_tac
      t="S"
      and s="take n S @ [S ! n] @ drop (Suc n) S"
      in ssubst)
   apply(rule take_nth_drop_X)
   apply(force)
  apply(rule_tac
      t="w"
      and s="take n w @ [w ! n] @ drop (Suc n) w"
      in ssubst)
   apply(rule take_nth_drop_X)
   apply(force)
  apply(rule_tac
      t="length (take n w @ [w ! n] @ drop (Suc n) w)"
      and s=" length (take n w) + length [w ! n] + length (drop (Suc n) w)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="length (foldl (@) [] (map (option_to_list \<circ> f) (take n S @ [S ! n] @ drop (Suc n) S)))"
      and s=" length (foldl (@) [] (map (option_to_list \<circ> f) (take n S))) + length (foldl (@) [] (map (option_to_list \<circ> f) ([S ! n]))) + length (foldl (@) [] (map (option_to_list \<circ> f) (drop (Suc n) S))) "
      in ssubst)
   prefer 2
   apply(rule_tac
      y="length (foldl (@) [] (map (option_to_list \<circ> f) (take n S))) + length (foldl (@) [] (map (option_to_list \<circ> f) (drop (Suc n) S)))"
      in le_less_trans)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
   apply(rule_tac
      y="length (foldl (@) [] (map (option_to_list \<circ> f) (take n S))) + length (foldl (@) [] (map (option_to_list \<circ> f) (drop (Suc n) S)))+ Suc 0"
      in less_le_trans)
    apply(force)
   apply(subgoal_tac "length (foldl (@) [] (map (option_to_list \<circ> f) (take n S))) + length (foldl (@) [] (map (option_to_list \<circ> f) (drop (Suc n) S))) \<le> length (take n w) + length (drop (Suc n) w)")
    apply(force)
   apply(rule add_mono)
    apply(rule length_smaller)
    apply(force)
   apply(rule length_smaller)
   apply(force)
  apply(rule_tac
      t="map (option_to_list \<circ> f) (take n S @ [S ! n] @ drop (Suc n) S)"
      and s=" (map (option_to_list \<circ> f) (take n S)) @(map (option_to_list \<circ> f) ([S ! n])) @(map (option_to_list \<circ> f) (drop (Suc n) S)) "
      in ssubst)
   apply(simp add: map_append)
  apply(simp only: length_foldl_append)
  done

lemma not_none_if_AX_equal_lengths: "
  length (foldl (@) [] (map (option_to_list \<circ> f) S)) = length w
  \<Longrightarrow> length S \<le> length w
  \<Longrightarrow> n<length S
  \<Longrightarrow> \<exists>y. f (S ! n) = Some y"
  apply(case_tac "f (S ! n)")
   prefer 2
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length (foldl (@) [] (map (option_to_list \<circ> f) S)) < length w")
   apply(force)
  apply(subgoal_tac "length (foldl (@) [] (map (option_to_list \<circ> f) S)) \<le> length w")
   prefer 2
   apply(rule length_smaller)
   apply(force)
  apply(rule length_strictly_smaller)
    apply(force)
   apply(force)
  apply(force)
  done

lemma all_not_none_implies_AX_equal_length: "
  \<forall>x\<in> set w. \<exists>y. f x = Some y
  \<Longrightarrow> length w = length (foldl (@) [] (map (option_to_list \<circ> f) w))"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w y)(*strict*)
  apply(simp add: option_to_list_def)
  apply (metis ConsApp foldl_append_initial_pullout impossible_Cons le_SucE map_map takePrecise takeShorter take_Suc_Cons)
  done

lemma split_signature_length2: "
  length (foldl (@) [] (map (option_to_list \<circ> f) w')) \<le> length w'"
  apply(induct w')
   apply(clarsimp)
  apply(rename_tac a w')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) (option_to_list (f a)) (map (\<lambda>a. option_to_list (f a)) w')"
      and s=" (option_to_list (f a))@foldl (@) [] (map (\<lambda>a. option_to_list (f a)) w') "
      in ssubst)
   apply(rename_tac a w')(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w')(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac "f a")
   apply(rename_tac a w')(*strict*)
   apply(clarsimp)
  apply(rename_tac a w' aa)(*strict*)
  apply(clarsimp)
  done

lemma butlast_nthX: "
  Suc n<length w
  \<Longrightarrow> butlast w ! n = w!n"
  apply(subgoal_tac "w=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(rule sym)
  apply(rule nth_append_1)
  apply(force)
  done

lemma setB_map_nat_seq: "
  x \<in> setB (map f (nat_seq n m))
  \<Longrightarrow> \<exists>i. n\<le>i \<and> i\<le>m \<and> x \<in> setB [f i]"
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB SSx] @ w2 = SSw" for SSx SSw)
   prefer 2
   apply(rule setB_decomp)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "x \<in> setB (map f (nat_seq n m))")
  apply(subgoal_tac "teB x \<in> set (map f (nat_seq n m))")
   apply(rename_tac w1 w2)(*strict*)
   prefer 2
   apply (metis setB_selects_sound1 not_in_setBI)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "w1 @ teB x # w2 = map f (nat_seq n m)")
  apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
   apply(rename_tac w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      x="teB x"
      and w="map f (nat_seq n m)"
      in set_elem_nth)
   apply(force)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "teB x \<in> set (map f (nat_seq n m))")
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length (nat_seq n m) = SSn + 1 - SSm" for SSn SSm)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="n+i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq n m ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma setA_map_nat_seq: "
  x \<in> setA (map f (nat_seq n m))
  \<Longrightarrow> \<exists>i. n\<le>i \<and> i\<le>m \<and> x \<in> setA [f i]"
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA SSx] @ w2 = SSw" for SSx SSw)
   prefer 2
   apply(rule setA_decomp)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "x \<in> setA (map f (nat_seq n m))")
  apply(subgoal_tac "teA x \<in> set (map f (nat_seq n m))")
   apply(rename_tac w1 w2)(*strict*)
   prefer 2
   apply (metis in_set_conv_decomp)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "w1 @ teA x # w2 = map f (nat_seq n m)")
  apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
   apply(rename_tac w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      x="teA x"
      and w="map f (nat_seq n m)"
      in set_elem_nth)
   apply(force)
  apply(rename_tac w1 w2)(*strict*)
  apply(thin_tac "teA x \<in> set (map f (nat_seq n m))")
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length (nat_seq n m) = SSn + 1 - SSm" for SSn SSm)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="n+i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq n m ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma theI2_prime_prime: "
  \<exists>x. P x
  \<Longrightarrow> (\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> x=y)
  \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x)
  \<Longrightarrow> Q (THE x. P x)"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule HOL.theI2)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(force)
  done

lemma elim_THE_in_assumptions: "
  Q (THE x. P x)
  \<Longrightarrow> \<exists>!x. P x
  \<Longrightarrow> \<exists>x. Q x \<and> P x"
  apply(subgoal_tac "\<exists>x. P x")
   prefer 2
   apply(force)
  apply(erule exE)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="x"
      and s="THE x. P x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply (metis the_equality)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma butlast_nth_mem: "
  Suc i<length x
  \<Longrightarrow> x!i \<in> set(butlast x)"
  apply(rule_tac
      t="x!i"
      and s="butlast x!i"
      in subst)
   apply(rule butlast_nthX)
   apply(force)
  apply(force)
  done

lemma butn_not_empty: "
  butn w n \<noteq> []
  \<Longrightarrow> length w > n"
  apply(simp add: butn_def)
  done

lemma nth_simpX: "
  w1@[a]@w2=w
  \<Longrightarrow> length w1=i
  \<Longrightarrow> w!i=a"
  apply(clarsimp)
  done

lemma irrelevant_case: "
  P
  \<Longrightarrow> (p\<or>q)
  \<Longrightarrow> (p\<longrightarrow> P \<and> q \<longrightarrow> P)"
  apply(force)
  done

lemma set_butlast: "
  v\<noteq>[]
  \<Longrightarrow> set(butlast (w@v))=set w \<union> (set(butlast v))"
  apply(subgoal_tac "v=[] \<or> (\<exists>w' a'. SSS=w'@[a'])" for SSS)
   prefer 2
   apply(rule case_list)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply (metis butlast_snoc_2 set_append)
  done

lemma impossible_empty_newignore: "
  new_i \<noteq> []
  \<Longrightarrow> new_Si = []
  \<Longrightarrow> length ig_i = length new_i + length tbR_i
  \<Longrightarrow> length ig_Si = length new_Si + length tbR_Si
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) ig_i
  \<Longrightarrow> ig_Si = w @ ig_i
  \<Longrightarrow> Q"
  apply(simp add: takeB_def)
  done

lemma last_of_newignore_is_new_from: "
  new_i \<noteq> []
  \<Longrightarrow> new_Si = []
  \<Longrightarrow> length ig_i = length new_i + length tbR_i
  \<Longrightarrow> length ig_Si = length new_Si + length tbR_Si
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) ig_i
  \<Longrightarrow> w@ ig_Si = ig_i
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> last(butn(ig_i)(length(tbR_i)))=last w"
  apply(simp add: suffix_def takeB_def)
  apply(clarsimp)
  apply(simp add: butn_def)
  done

lemma butlast_of_newignore_is_new_from: "
  new_i \<noteq> []
  \<Longrightarrow> new_Si = []
  \<Longrightarrow> length ig_i = length new_i + length tbR_i
  \<Longrightarrow> length ig_Si = length new_Si + length tbR_Si
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) ig_i
  \<Longrightarrow> w@ ig_Si = ig_i
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> butlast(butn(ig_i)(length(tbR_i)))=butlast w"
  apply(simp add: suffix_def takeB_def)
  apply(clarsimp)
  apply(simp add: butn_def)
  done

lemma nat_diff: "
  b\<le>(a::nat)
  \<Longrightarrow> a = b+ (a-b)"
  apply(force)
  done

lemma nth_direct: "
  w=x@[y]@z
  \<Longrightarrow> length x=n
  \<Longrightarrow> w!n = y"
  apply(force)
  done

lemma nth_direct_via_drop: "
  x<length \<pi>1
  \<Longrightarrow> ys @ y # c = \<pi>1 ! x # drop (Suc x) \<pi>1
  \<Longrightarrow> \<pi>1!(x+length ys) = y \<and> x+length ys < length \<pi>1"
  apply(subgoal_tac "prefix (ys @ [y]) [\<pi>1!x] \<or> SSX" for SSX)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(case_tac ys)
    apply(rename_tac ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac ca a list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(case_tac ys)
   apply(rename_tac ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(rule conjI)
   apply(rename_tac list)(*strict*)
   apply(rule_tac
      x="take (Suc x) \<pi>1 @ list"
      and z="c"
      in nth_direct)
    apply(rename_tac list)(*strict*)
    apply(force)
   apply(rename_tac list)(*strict*)
   apply(force)
  apply(rename_tac list)(*strict*)
  apply(rule_tac
      t="\<pi>1"
      and s="take (Suc x) \<pi>1 @ list @ y # c"
      in ssubst)
   apply(rename_tac list)(*strict*)
   prefer 2
   apply(simp (no_asm))
  apply(rename_tac list)(*strict*)
  apply(force)
  done

lemma prefix_length: "
  prefix a b
  \<Longrightarrow> length a\<le>length b"
  apply(simp add: prefix_def)
  apply(force)
  done

lemma prefix_take_length: "
  prefix a b
  \<Longrightarrow> take (length a) b = a"
  apply(simp add: prefix_def)
  apply(force)
  done

lemma strict_prefix_from_prefix_and_neq: "
  prefix a b
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> strict_prefix a b"
  apply(simp add: strict_prefix_def prefix_def)
  apply(force)
  done

lemma map_liftB_length_eq: "
  map f ((liftB w)::('a,'b)DT_two_elements list) = map f ((liftB v)::('a,'b)DT_two_elements list)
  \<Longrightarrow> length w = length v"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(case_tac v)
    apply(rename_tac v)(*strict*)
    apply(clarsimp)
   apply(rename_tac v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(case_tac v)
   apply(rename_tac a w v)(*strict*)
   apply(clarify)
   apply(subgoal_tac "False")
    apply(rename_tac a w v)(*strict*)
    apply(force)
   apply(rename_tac a w v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v aa list)(*strict*)
  apply(clarsimp)
  done

lemma map_liftB_eq: "
  map f ((liftB w)::('a,'b)DT_two_elements list) = map f ((liftB v)::('a,'b)DT_two_elements list)
  \<Longrightarrow> inj f
  \<Longrightarrow> w = v"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(case_tac v)
    apply(rename_tac v)(*strict*)
    apply(clarsimp)
   apply(rename_tac v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(case_tac v)
   apply(rename_tac a w v)(*strict*)
   apply(clarify)
   apply(subgoal_tac "False")
    apply(rename_tac a w v)(*strict*)
    apply(force)
   apply(rename_tac a w v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w aa list)(*strict*)
  apply (metis DT_two_elements.inject(2) inj_eq)
  done

lemma nth_last: "
  Suc n = length w
  \<Longrightarrow> w!n=last w"
  apply(rule_tac
      xs="w"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  done

lemma liftA_inj_equality: "
  (liftA a = liftA b) = (a=b)"
  apply (metis liftA_vs_filterA)
  done

lemma le_absorb1: "
  c\<le>(b::nat)
  \<Longrightarrow> a \<le> a + b - c"
  apply(force)
  done

lemma nth_in_butlast_append: "
  n<length w
  \<Longrightarrow> v=[] \<longrightarrow> Suc n<length w
  \<Longrightarrow> w!n \<in> set(butlast(w@v))"
  apply(rule_tac
      xs="v"
      in rev_cases)
   apply(clarsimp)
   apply(rule_tac
      xs="w"
      in rev_cases)
    apply(clarsimp)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(ys @ [y]) ! n"
      in ssubst)
    apply(rename_tac ys y)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="butlast (w @ ys @ [y])"
      in ssubst)
   apply(rename_tac ys y)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(force)
  done

lemma nth_in_butlast_append2: "
  w ! n \<notin> set (butlast (w @ v))
  \<Longrightarrow> n < length w
  \<Longrightarrow> v = [] \<longrightarrow> Suc n < length w
  \<Longrightarrow> Q"
  apply(subgoal_tac "w ! n \<in> set (butlast (w @ v))")
   apply(force)
  apply(rule nth_in_butlast_append)
   apply(force)+
  done

lemma less_not_leq: "
  m<(n::nat)
  \<Longrightarrow> \<not> (n\<le>m)"
  apply(force)
  done

lemma prefixI: "
  w@v=x
  \<Longrightarrow> prefix w x"
  apply(simp add: prefix_def)
  apply(force)
  done

lemma hlpXX1: "
  ia\<le>x
  \<Longrightarrow> n\<le>x-ia
  \<Longrightarrow> n + (x - (ia + (n::nat))) = x - ia"
  apply(force)
  done

lemma hlpXX2: "
  w@v=x
  \<Longrightarrow> v\<noteq>[]
  \<Longrightarrow> length w<length x"
  apply(force)
  done

lemma hlpXX3: "
  ia\<le>x
  \<Longrightarrow> n\<le>x-ia
  \<Longrightarrow> (n::nat)+ ia +
  (x - (ia + n)) = x"
  apply(force)
  done

lemma strict_prefix_contra: "
  strict_prefix w v
  \<Longrightarrow> w = x
  \<Longrightarrow> length v \<le> length x
  \<Longrightarrow> Q"
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  done

lemma foldl_map_not_empty_by_last: "
  w=v@[n]
  \<Longrightarrow> f n \<noteq> []
  \<Longrightarrow> foldl (@) [] (map f w) \<noteq> []"
  apply(clarsimp)
  done

lemma nat_seq_drop_last2: "
  n\<le>m
  \<Longrightarrow> \<exists>w. nat_seq n m = w @ [m]"
  apply(case_tac "n=m")
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply (metis natUptTo_n_n)
  apply(subgoal_tac "n<m")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="nat_seq n nat"
      in exI)
  apply (metis less_Suc_eq_le nat_seq_drop_last_simp rotate_simps)
  done

lemma butlast_preserves_prefix_1: "
  prefix (butlast (w@[A])) (butlast (v@[B]))
  \<Longrightarrow> prefix w v"
  apply(clarsimp)
  done

lemma prefix_butlast_drop: "
  w=v
  \<Longrightarrow> y \<noteq> []
  \<Longrightarrow> prefix (butlast x) (butlast y)
  \<Longrightarrow> prefix (butlast(w@x)) (butlast(v@y))"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      xs="x"
      in rev_cases)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      xs="y"
      in rev_cases)
    apply(clarsimp)
   apply(rename_tac ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac ys y)(*strict*)
   apply(rule_tac
      xs="v"
      in rev_cases)
    apply(rename_tac ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac ys y ysa ya)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="ya#ys"
      in exI)
   apply (metis append_Cons butlast_snoc_2)
  apply(rename_tac c ys ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs="y"
      in rev_cases)
   apply(rename_tac c ys ya)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ys ya ysa yaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ys y ya)(*strict*)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule_tac
      t="butlast SSX" for SSX
      in ssubst)
   apply(rename_tac c ys y ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac c ys y ya)(*strict*)
  apply(rule_tac
      t="butlast SSX" for SSX
      in ssubst)
   apply(rename_tac c ys y ya)(*strict*)
   apply(rule butlast_direct)
   apply(force)
  apply(rename_tac c ys y ya)(*strict*)
  apply(force)
  done

lemma equal_split_prefix_hlp1_hlp1: "
  \<alpha> @ v1 = X # l1
  \<Longrightarrow> length v1 = length v2
  \<Longrightarrow> \<alpha> @ v2 @ bx2 = X # l1 @ l2x
  \<Longrightarrow> bx2 = l2x"
  apply (metis Cons_eq_appendI append_assoc append_injective2 append_linj length_append_equal)
  done

lemma prop_of_nth_append: "
  i < length (w @ v)
  \<Longrightarrow> (\<And>i. i < length w \<Longrightarrow> P (w ! i))
  \<Longrightarrow> (\<And>i. i < length v \<Longrightarrow> P (v ! i))
  \<Longrightarrow> P ((w @ v) ! i)"
  apply(case_tac "i<length w")
   apply(rule_tac
      t="(w @ v) ! i"
      in ssubst)
    apply(rule nth_append_1)
    apply(force)
   apply(force)
  apply(rule_tac
      t="(w @ v) ! i"
      in ssubst)
   apply(rule nth_append_2)
   apply(force)
  apply(force)
  done

lemma liftB_nth: "
  i < length w
  \<Longrightarrow> liftB w ! i = teB (w!i)"
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

lemma le_diff_exists: "
  a\<le>(b::nat)
  \<Longrightarrow> \<exists>k. a+k=b"
  apply(rule_tac
      x="b-a"
      in exI)
  apply(force)
  done

lemma less_diff_exists: "
  a<(b::nat)
  \<Longrightarrow> \<exists>k. a+Suc k=b"
  apply(rule_tac
      x="b-Suc a"
      in exI)
  apply(force)
  done

lemma nat_seq_not_empty: "
  n\<le>m
  \<Longrightarrow> nat_seq n m = []
  \<Longrightarrow> Q"
  apply (metis impossible_Cons length_0_conv less_eq_nat.simps(1) nat_seq_pullout)
  done

lemma nth_append_2_prime: "
  w=u@v
  \<Longrightarrow> j=i-length u
  \<Longrightarrow> length u\<le>i
  \<Longrightarrow> w!i = v!j"
  apply(clarsimp)
  apply(rule nth_append_2)
  apply(force)
  done

lemma nth_eq_ignore_append: "
  n<length w
  \<Longrightarrow> y1=w@x1
  \<Longrightarrow> y2=w@x2
  \<Longrightarrow> y1!n = y2!n"
  apply (metis List.nth_append)
  done

lemma liftB_nth2: "
  m<length w
  \<Longrightarrow> liftB w ! m = teB b
  \<Longrightarrow> w ! m = b"
  apply (metis teB_nth_liftB DT_two_elements.inject(2))
  done

lemma nth_append_2_prime_prime_X: "
  v=w@u
  \<Longrightarrow> i=j
  \<Longrightarrow> i<length w
  \<Longrightarrow> w!i = v!j"
  apply(clarsimp)
  apply(rule sym)
  apply(rule nth_append_1)
  apply(force)
  done

lemma suffix_with_border: "
  w @ v = x @ teA A # y
  \<Longrightarrow> setA v = {}
  \<Longrightarrow> setA y = {}
  \<Longrightarrow> suffix y v"
  apply(subgoal_tac "\<exists>l'. liftB l' = v")
   prefer 2
   apply(rule_tac
      x="filterB v"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(subgoal_tac "\<exists>l'. liftB l' = y")
   prefer 2
   apply(rule_tac
      x="filterB y"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(clarsimp)
  apply(rename_tac l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "prefix w x \<or> SSX" for SSX)
   apply(rename_tac l' l'a)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac l' l'a)(*strict*)
  apply(erule disjE)
   apply(rename_tac l' l'a)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac l' l'a c)(*strict*)
   apply (metis liftB_with_nonterminal_inside)
  apply(rename_tac l' l'a)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac l' l'a c)(*strict*)
  apply(case_tac c)
   apply(rename_tac l' l'a c)(*strict*)
   apply(clarsimp)
   apply(rename_tac l' l'a)(*strict*)
   apply(case_tac l')
    apply(rename_tac l' l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac l' l'a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac l' l'a c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac l' l'a list)(*strict*)
  apply(rule_tac
      x="list"
      in exI)
  apply(force)
  done

lemma no_pre_DT_revert_position_hlp1: "
  take (length w + length v) S =
       take (length w) S @ take (length v) (drop (length w) S)"
  apply (metis append_take_drop_id length_append add.commute take_drop take_take2)
  done

lemma equal_terminal_suffix: "
  w1 @ teA A # v1
  = w2 @ teA A # v2
  \<Longrightarrow> setA v1={}
  \<Longrightarrow> setA v2={}
  \<Longrightarrow> v1=v2"
  apply (metis List.set_simps(1) append_Cons append_Nil equal_simp_triv)
  done

lemma prop_of_nth_Cons: "
  i < length (x# v)
  \<Longrightarrow> (P x)
  \<Longrightarrow> (\<And>i. i < length v \<Longrightarrow> P (v ! i))
  \<Longrightarrow> P ((x # v) ! i)"
  apply(case_tac "i")
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma case_option_split: "
  (A=None \<Longrightarrow> P Y)
  \<Longrightarrow> (\<And>X. A=Some X \<Longrightarrow> P (K X))
  \<Longrightarrow> P (case A of None \<Rightarrow> Y | Some X \<Rightarrow> K X)"
  apply(case_tac A)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

lemma if_then_else_option: "
  (if P then Some A else None) = None
  \<Longrightarrow> \<not> P"
  apply(force)
  done

lemma case_DT_two_elements_split: "
  (case X of teA a \<Rightarrow> W a | teB b \<Rightarrow> Y) = Z
  \<Longrightarrow> (\<And>a. W a\<noteq>Z)
  \<Longrightarrow> (\<exists>b. X=teB b)"
  apply(case_tac X)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

lemma liftB_length: "
  length(liftB w) = length w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma append_linj_length: "
  length a=length b
  \<Longrightarrow> a@w=b@v
  \<Longrightarrow> w=v"
  apply(rule_tac
      t="w"
      and s="drop(length a)(a@w)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="v"
      and s="drop(length b)(b@v)"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma all_set_butlast: "
  \<forall>x\<in> set (butlast w) .P x
  \<Longrightarrow> w=v@[a]
  \<Longrightarrow> ((\<And>x. x\<in> set v \<Longrightarrow> P x) \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(force)
  done

lemma maximalTermPrefix_split: "
  maxTermPrefix (liftB w@liftA v) =w"
  apply(rule_tac
      t="maxTermPrefix (liftB w@liftA v)"
      and s="maximalPrefixB (liftB w@liftA v)"
      in ssubst)
   apply (metis maxTermPrefix_shift maxTermPrefix_vs_maximalPrefixB)
  apply (metis append_Nil2 maximalPrefixB_liftA maximalPrefixB_drop_liftB)
  done

lemma last_nth3: "
    Suc x=length w
  \<Longrightarrow> last w = w ! x"
  apply(rule_tac
      xs="w"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  done

lemma last_take_nth: "
  x<length S
  \<Longrightarrow> last (take (Suc x) S) = S ! x"
  apply(rule_tac
      P="\<lambda>X. last (take (Suc x) S) = X ! x"
      and s="take (Suc x) S @ drop (Suc x) S"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="(take (Suc x) S @ drop (Suc x) S) ! x"
      and s="(take (Suc x) S) ! x"
      in ssubst)
   apply(rule nth_append_1)
   apply(force)
  apply(rule last_nth3)
  apply(force)
  done

lemma maxTermPrefix_leading_terminal: "
  maxTermPrefix (teB b # liftA v2) = [b]"
  apply (metis maxTermPrefix_pull_out insert_Nil maxTermPrefix_vs_maximalPrefixB maximalPrefixB_liftA)
  done

lemma maxTermPrefix_empty: "
  maxTermPrefix [] = []"
  apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB.simps(1))
  done

lemma maxTermPrefix_terminal_front: "
  maxTermPrefix (teA a # t) = []"
  apply(rule_tac
      t="teA a # t"
      and s="liftB [] @ teA a # t"
      in ssubst)
   apply(force)
  apply(rule maxTermPrefix_mixed_string)
  done

lemma merging_lemma1: "
  c1 = tbR_i
  \<Longrightarrow> c2 @ c1 = tbR_Si
  \<Longrightarrow> c5 @ c2 @ c1 = tbR_SSi
  \<Longrightarrow> c4 @ c1 = ig_i
  \<Longrightarrow> c3 @ c2 @ c1 = ig_Si
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> tbR_Si = takeB (length(tbR_SSi)) (ig_Si)
  \<Longrightarrow> ig_Si = w @ ig_i
  \<Longrightarrow> butn ig_Si (length ig_i) @ butn ig_i (length tbR_Si) = butn ig_Si (length tbR_SSi) @ butn tbR_Si (length tbR_i)"
  apply(rule_tac
      t="ig_Si"
      and s="c3@c2@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="ig_i"
      and s="c4@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="tbR_Si"
      and s="c2@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="tbR_SSi"
      and s="c5@c2@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="tbR_i"
      and s="c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="butn (c3 @ c2 @ c1) (length (c4 @ c1))"
      and s="butn (c3 @ c2) (length c4)"
      in ssubst)
   apply(simp (no_asm) add: butn_def)
  apply(rule_tac
      t="butn (c4 @ c1) (length (c2 @ c1))"
      and s="butn c4 (length c2)"
      in ssubst)
   apply(simp (no_asm) add: butn_def)
  apply(rule_tac
      t="butn (c3 @ c2 @ c1) (length (c5 @ c2 @ c1))"
      and s="butn c3 (length c5)"
      in ssubst)
   apply(simp (no_asm) add: butn_def)
  apply(rule_tac
      t="butn (c2 @ c1) (length c1)"
      and s="c2"
      in ssubst)
   apply(simp (no_asm) add: butn_def)
  apply(subgoal_tac "c5 \<noteq> [] \<longrightarrow> c3 = []")
   prefer 2
   apply(rule impI)
   apply(subgoal_tac "takeB (length c5) c3 = []")
    apply(subgoal_tac "c3=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(subgoal_tac "c5=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' w'a a'a)(*strict*)
    apply(simp add: takeB_def)
   apply(rule_tac
      v="tbR_Si"
      in append_injr)
   apply(rule_tac
      t="takeB (length c5) c3 @ tbR_Si"
      and s="takeB (length c5+length tbR_Si) (c3 @ tbR_Si)"
      in ssubst)
    apply(simp (no_asm) add: takeB_def)
   apply(rule_tac
      t="c3 @ tbR_Si"
      and s="ig_Si"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="length c5 + length tbR_Si"
      and s="length tbR_SSi"
      in ssubst)
    apply(force)
   apply(rule sym)
   apply(simp (no_asm))
  apply(thin_tac "tbR_Si = takeB (length tbR_SSi) ig_Si")
  apply(subgoal_tac "c2 \<noteq> [] \<longrightarrow> c4 = []")
   prefer 2
   apply(rule impI)
   apply(subgoal_tac "takeB (length c2) c4 = []")
    apply(subgoal_tac "c4=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(subgoal_tac "c2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' w'a a'a)(*strict*)
    apply(simp add: takeB_def)
   apply(rule_tac
      v="tbR_i"
      in append_injr)
   apply(rule_tac
      t="[] @ tbR_i"
      and s="takeB (length tbR_Si) ig_i"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="tbR_Si"
      and s="c2@c1"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="ig_i"
      and s="c4@c1"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="tbR_i"
      and s="c1"
      in ssubst)
    apply(force)
   apply(simp (no_asm) add: takeB_def)
  apply(thin_tac "tbR_i = takeB (length tbR_Si) ig_i")
  apply(case_tac "c4=[]")
   apply(rule_tac
      t="c4"
      and s="[]"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="butn (c3 @ c2) (length [])"
      and s="c3@c2"
      in ssubst)
    apply(simp (no_asm) add: butn_def)
   apply(rule_tac
      t="butn [] (length c2)"
      and s="[]"
      in ssubst)
    apply(simp (no_asm) add: butn_def)
   apply(simp (no_asm) add: butn_def)
   apply(case_tac "c5=[]")
    apply(force)
   apply(subgoal_tac "c3=[]")
    prefer 2
    apply(force)
   apply(force)
  apply(case_tac "c2=[]")
   apply(rule_tac
      t="c2"
      and s="[]"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="butn c4 (length [])"
      and s="c4"
      in ssubst)
    apply(simp (no_asm) add: butn_def)
   apply(case_tac "c5=[]")
    apply(rule_tac
      t="c5"
      and s="[]"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="butn c3 (length [])"
      and s="c3"
      in ssubst)
     apply(simp (no_asm) add: butn_def)
    apply(subgoal_tac "c3=w@c4")
     prefer 2
     apply(force)
    apply(rule_tac
      t="c3"
      and s="w@c4"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="butn ((w @ c4) @ []) (length c4)"
      and s="w"
      in ssubst)
     apply(simp (no_asm) add: butn_def)
    apply(force)
   apply(subgoal_tac "c3=[]")
    prefer 2
    apply(force)
   apply(rule_tac
      t="c3"
      and s="[]"
      in ssubst)
    apply(force)
   apply(force)
  apply(force)
  done

lemma merging_lemma1_prime: "
  suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> suffix (tbR_SSi) (tbR_Si)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> tbR_Si = takeB (length(tbR_SSi)) (ig_Si)
  \<Longrightarrow> suffix (ig_i) (tbR_i)
  \<Longrightarrow> suffix (ig_Si) (tbR_Si)
  \<Longrightarrow> ig_Si = w @ ig_i
  \<Longrightarrow> butn ig_Si (length ig_i) @ butn ig_i (length tbR_Si) = butn ig_Si (length tbR_SSi) @ butn tbR_Si (length tbR_i)"
  apply(unfold suffix_def)
  apply(erule exE)+
  apply(rename_tac c ca cb cc)(*strict*)
  apply(rule_tac
      ?c3.0="cc"
      and ?c1.0="tbR_i"
      and ?c4.0="cb"
      and ?c5.0="ca"
      and ?c2.0="c"
      in merging_lemma1)
         apply(rename_tac c ca cb cc)(*strict*)
         apply(force)
        apply(rename_tac c ca cb cc)(*strict*)
        apply(force)
       apply(rename_tac c ca cb cc)(*strict*)
       apply(force)
      apply(rename_tac c ca cb cc)(*strict*)
      apply(force)
     apply(rename_tac c ca cb cc)(*strict*)
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(force)
   apply(rename_tac c ca cb cc)(*strict*)
   apply(force)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(force)
  done

lemma merging_lemma2: "
  c1 = tbR_i
  \<Longrightarrow> c2 @ c1 = tbR_Si
  \<Longrightarrow> c5 @ c2 @ c1 = tbR_SSi
  \<Longrightarrow> c4 @ c1 = ig_i
  \<Longrightarrow> c3 @ c2 @ c1 = ig_Si
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> tbR_Si = takeB (length(tbR_SSi)) (ig_Si)
  \<Longrightarrow> ig_Si = take (length (ig_Si) - length (tbR_SSi)) (ig_Si) @ butn (tbR_Si) (length (tbR_i)) @ drop (length (ig_i) - length (tbR_Si)) (ig_i)"
  apply(rule_tac
      t="tbR_i"
      and s="c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="ig_Si"
      and s="c3 @ c2 @ c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="tbR_SSi"
      and s="c5 @ c2 @ c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="tbR_Si"
      and s="c2@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="ig_i"
      and s="c4@c1"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="length (c3 @ c2 @ c1) - length (c5 @ c2 @ c1)"
      and s="length c3 - length c5"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="butn (c2 @ c1) (length c1)"
      and s="c2"
      in ssubst)
   apply(simp (no_asm) add: butn_def)
  apply(rule_tac
      t="length (c4 @ c1) - length (c2 @ c1)"
      and s="length c4 - length c2"
      in ssubst)
   apply(force)
  apply(subgoal_tac "c5 \<noteq> [] \<longrightarrow> c3 = []")
   prefer 2
   apply(rule impI)
   apply(subgoal_tac "takeB (length c5) c3 = []")
    apply(subgoal_tac "c3=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(subgoal_tac "c5=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' w'a a'a)(*strict*)
    apply(simp add: takeB_def)
   apply(rule_tac
      v="tbR_Si"
      in append_injr)
   apply(rule_tac
      t="takeB (length c5) c3 @ tbR_Si"
      and s="takeB (length c5+length tbR_Si) (c3 @ tbR_Si)"
      in ssubst)
    apply(simp (no_asm) add: takeB_def)
   apply(rule_tac
      t="c3 @ tbR_Si"
      and s="ig_Si"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="length c5 + length tbR_Si"
      and s="length tbR_SSi"
      in ssubst)
    apply(force)
   apply(rule sym)
   apply(simp (no_asm))
  apply(thin_tac "tbR_Si = takeB (length tbR_SSi) ig_Si")
  apply(subgoal_tac "c2 \<noteq> [] \<longrightarrow> c4 = []")
   prefer 2
   apply(rule impI)
   apply(subgoal_tac "takeB (length c2) c4 = []")
    apply(subgoal_tac "c4=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     prefer 2
     apply(rule case_list)
    apply(erule disjE)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(subgoal_tac "c2=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
     apply(rename_tac w' a')(*strict*)
     prefer 2
     apply(rule case_list)
    apply(rename_tac w' a')(*strict*)
    apply(erule disjE)
     apply(rename_tac w' a')(*strict*)
     apply(clarsimp)
    apply(rename_tac w' a')(*strict*)
    apply(clarsimp)
    apply(rename_tac w' a' w'a a'a)(*strict*)
    apply(simp add: takeB_def)
   apply(rule_tac
      v="tbR_i"
      in append_injr)
   apply(rule_tac
      t="[] @ tbR_i"
      and s="takeB (length tbR_Si) ig_i"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="tbR_Si"
      and s="c2@c1"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="ig_i"
      and s="c4@c1"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="tbR_i"
      and s="c1"
      in ssubst)
    apply(force)
   apply(simp (no_asm) add: takeB_def)
  apply(thin_tac "tbR_i = takeB (length tbR_Si) ig_i")
  apply(case_tac "c2=[]")
   apply(thin_tac "c2 \<noteq> [] \<longrightarrow> c4 = []")
   apply(rule_tac
      t="c2"
      and s="[]"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="drop (length c4 - length []) (c4 @ c1)"
      and s="c1"
      in ssubst)
    apply(force)
   apply(case_tac "c5=[]")
    apply(force)
   apply(subgoal_tac "c3=[]")
    prefer 2
    apply(force)
   apply(thin_tac "c5 \<noteq> [] \<longrightarrow> c3 = []")
   apply(force)
  apply(erule_tac
      P="c2 \<noteq> []"
      in impE)
   apply(force)
  apply(rule_tac
      t="c4"
      and s="[]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="drop (length [] - length c2) ([] @ c1)"
      and s="c1"
      in ssubst)
   apply(force)
  apply(case_tac "c5=[]")
   apply(force)
  apply(subgoal_tac "c3=[]")
   prefer 2
   apply(force)
  apply(thin_tac "c5 \<noteq> [] \<longrightarrow> c3 = []")
  apply(force)
  done

lemma merging_lemma2_prime: "
  suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> suffix (tbR_SSi) (tbR_Si)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> tbR_Si = takeB (length(tbR_SSi)) (ig_Si)
  \<Longrightarrow> suffix (ig_i) (tbR_i)
  \<Longrightarrow> suffix (ig_Si) (tbR_Si)
  \<Longrightarrow> ig_Si = take (length (ig_Si) - length (tbR_SSi)) (ig_Si) @ butn (tbR_Si) (length (tbR_i)) @ drop (length (ig_i) - length (tbR_Si)) (ig_i)"
  apply(unfold suffix_def)
  apply(erule exE)+
  apply(rename_tac c ca cb cc)(*strict*)
  apply(rule_tac
      ?c3.0="cc"
      and ?c1.0="tbR_i"
      and ?c4.0="cb"
      and ?c5.0="ca"
      and ?c2.0="c"
      in merging_lemma2)
        apply(rename_tac c ca cb cc)(*strict*)
        apply(force)
       apply(rename_tac c ca cb cc)(*strict*)
       apply(force)
      apply(rename_tac c ca cb cc)(*strict*)
      apply(force)
     apply(rename_tac c ca cb cc)(*strict*)
     apply(force)
    apply(rename_tac c ca cb cc)(*strict*)
    apply(force)
   apply(rename_tac c ca cb cc)(*strict*)
   apply(force)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(force)
  done

lemma last_of_newignore_is_preserved1: "
  ssuffix ig_i tbR_i
  \<Longrightarrow> suffix ig_Si tbR_Si
  \<Longrightarrow> suffix (ig_Si) (ig_i)
  \<Longrightarrow> suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> last (butn (ig_i) (length (tbR_i))) =
  last (butn (ig_Si) (length (tbR_Si)))"
  apply(simp add: ssuffix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x c ca cb)(*strict*)
  apply(simp add: takeB_def)
  apply(subgoal_tac "prefix c ca \<or> SSX" for SSX)
   apply(rename_tac x c ca cb)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x c ca cb)(*strict*)
  apply(erule disjE)
   apply(rename_tac x c ca cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac x c ca cb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(subgoal_tac "x=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac x ca)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac x ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(simp add: butn_def)
  done

lemma butlast_of_newignore_is_related1: "
  ssuffix ig_i tbR_i
  \<Longrightarrow> ssuffix ig_Si tbR_Si
  \<Longrightarrow> ig_Si = w@ ig_i
  \<Longrightarrow> suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> w@ butlast (butn (ig_i) (length (tbR_i))) =
  butlast (butn (ig_Si) (length (tbR_Si)))"
  apply(clarsimp)
  apply(simp add: takeB_def suffix_def ssuffix_def)
  apply(clarsimp)
  apply(rename_tac x xa c)(*strict*)
  apply(rule_tac
      t="butn (xa @ tbR_Si) (length tbR_Si)"
      and s="xa"
      in ssubst)
   apply(rename_tac x xa c)(*strict*)
   apply(simp add: butn_def)
  apply(rename_tac x xa c)(*strict*)
  apply(subgoal_tac "xa=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac x xa c)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac x xa c)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c w' a')(*strict*)
  apply(subgoal_tac "prefix w w' \<or> SSX" for SSX)
   apply(rename_tac x c w' a')(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x c w' a')(*strict*)
  apply(erule disjE)
   apply(rename_tac x c w' a')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a' ca)(*strict*)
   apply(simp add: butn_def)
  apply(rename_tac x c w' a')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x c a' ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac x c a' ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac a')(*strict*)
   apply(simp add: butn_def)
  apply(rename_tac x c a' ca a list)(*strict*)
  apply(clarsimp)
  done

lemma ssuffix_from_suffix_for_ignore: "
  newi \<noteq>[]
  \<Longrightarrow> length newi+length tbR = length ig
  \<Longrightarrow> suffix ig tbR
  \<Longrightarrow> ssuffix ig tbR"
  apply(simp add: ssuffix_def suffix_def)
  apply(force)
  done

lemma last_of_newignore_is_preserved2: "
  ssuffix ig_i tbR_i
  \<Longrightarrow> ssuffix ig_Si tbR_Si
  \<Longrightarrow> ssuffix (ig_i) (ig_Si)
  \<Longrightarrow> suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> last (butn (ig_i) (length (tbR_i))) =
  last (butn (ig_Si) (length (tbR_Si)))"
  apply(simp add: ssuffix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa xb c)(*strict*)
  apply(simp add: takeB_def)
  apply(clarsimp)
  apply(rename_tac xa xb)(*strict*)
  apply(simp add: butn_def)
  done

lemma butlast_of_newignore_is_related2: "
  ssuffix ig_i tbR_i
  \<Longrightarrow> ssuffix ig_Si tbR_Si
  \<Longrightarrow> w@ig_Si = ig_i
  \<Longrightarrow> w\<noteq>[]
  \<Longrightarrow> suffix (tbR_Si) (tbR_i)
  \<Longrightarrow> tbR_i = takeB (length(tbR_Si)) (ig_i)
  \<Longrightarrow> butlast (butn (ig_i) (length (tbR_i))) =
  w@butlast (butn (ig_Si) (length (tbR_Si)))"
  apply(clarsimp)
  apply(simp add: takeB_def suffix_def ssuffix_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: butn_def)
  apply(subgoal_tac "xa=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w' a')(*strict*)
  apply(subgoal_tac "butlast (w @ w' @ [a']) = w @ w'")
   apply(rename_tac w' a')(*strict*)
   apply(force)
  apply(rename_tac w' a')(*strict*)
  apply(rule butlast_direct)
  apply(force)
  done

lemma disjoint_list_list: "
  wx \<in> set w
  \<Longrightarrow> vx \<in> set v
  \<Longrightarrow> set wx \<subseteq> A
  \<Longrightarrow> set vx \<subseteq> B
  \<Longrightarrow> A \<inter> B = {}
  \<Longrightarrow> set wx \<inter> set vx = {}"
  apply(force)
  done

lemma suffix_tail: "
  w2 @ liftA w2b = liftB c @ teA BX # liftA w2X
  \<Longrightarrow> suffix (BX#w2X) w2b"
  apply(subgoal_tac "prefix w2 (liftB c) \<or> prefix (liftB c) w2")
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(simp add: suffix_def)
   apply(case_tac ca)
    apply(rename_tac ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(rule liftA_inj)
    apply(rule sym)
    apply(force)
   apply(rename_tac ca a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(case_tac w2b)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list aa lista)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
    apply(rename_tac a list aa lista ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac list aa lista ab)(*strict*)
    apply (metis setA_liftB elemInsetA emptyE)
   apply(rename_tac a list aa lista b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa lista b)(*strict*)
   apply (metis setA_Concat2 setA_liftB liftA.simps(2) liftA_vs_filterA setB_liftA liftB_liftA_split eq_Nil_appendI equalityE subset_empty)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      x="filterA c"
      in exI)
  apply(rule liftA_inj)
  apply(simp add: liftA_commutes_over_concat)
  apply(rule_tac
      t="liftA (filterA c)"
      and s="c"
      in ssubst)
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule sym)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply (metis liftA.simps(2) liftA_append_setB liftA_commutes_over_concat setB_empty_then_liftA_vs_filterA)
  done

end
