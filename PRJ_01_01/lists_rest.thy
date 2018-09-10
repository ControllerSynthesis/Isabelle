section {*lists\_rest*}
theory
  lists_rest

imports
  lists_length

begin

lemma rev_nth_in_set: "
  n < length w
  \<Longrightarrow> rev w ! n  \<in> set w"
  apply (metis length_rev nth_mem set_rev)
  done

lemma drop_nth_tl_double_head: "
  Suc n < length v
  \<Longrightarrow> drop (length v - Suc (Suc n)) v @ w = drop (length v - Suc (Suc n)) v ! 0 # drop (length v - Suc n) v ! 0 # tl (drop (length v - Suc n) v) @ w"
  apply(clarsimp)
  apply(rule_tac
      t="drop (length v - Suc (Suc n)) v"
      and s=" [v ! (length v - Suc (Suc n))] @ drop (Suc (length v - Suc (Suc n))) v"
      in ssubst)
   apply (metis Cons_eq_appendI append_Nil diff_Suc_less gr_implies_not0 length_0_conv length_greater_0_conv Cons_nth_drop_Suc)
  apply(clarsimp)
  apply(rule_tac
      t="Suc (length v - Suc (Suc n))"
      and s="length v - Suc n"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="drop (length v - (Suc n)) v"
      and s=" [v ! (length v - (Suc n))] @ drop (Suc (length v - (Suc n))) v"
      in ssubst)
   apply (metis Cons_eq_appendI append_Nil diff_Suc_less gr_implies_not0 length_0_conv length_greater_0_conv Cons_nth_drop_Suc)
  apply(clarsimp)
  done

lemma nth_shift2: "
  m + length w = n
  \<Longrightarrow> (w @ v) ! n = v ! m"
  apply(clarsimp)
  apply (metis add.commute nth_append_length_plus)
  done

lemma rev_nth2: "
  length v = n + m
  \<Longrightarrow> m \<noteq> 0
  \<Longrightarrow> v ! n = (rev v) ! (m - Suc 0)"
  apply(rule sym)
  apply(rule_tac
      t="rev v ! (m - Suc 0)"
      and s="v!(length v - Suc (m-Suc 0))"
      in ssubst)
   apply(rule rev_nth)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  done

lemma take_rev_append_nth: "
  Suc (Suc (Suc n)) < length v
  \<Longrightarrow> take (length v - Suc (Suc n)) v = take (length v - Suc (Suc (Suc n))) v @ [rev v ! Suc (Suc n)]"
  apply(subgoal_tac "\<exists>m. Suc (Suc (Suc n))+m = length v \<and> m \<noteq> 0")
   prefer 2
   apply(rule_tac
      x="length v-Suc (Suc (Suc n))"
      in exI)
   apply(clarsimp)
   apply(case_tac "length v")
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat nata)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(case_tac m)
   apply(rename_tac m)(*strict*)
   apply(clarsimp)
  apply(rename_tac m nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length v - Suc (Suc n)"
      and s="Suc(Suc nat)"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length v - Suc (Suc (Suc n))"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="rev v ! Suc (Suc n)"
      and s="v!(length v - Suc (Suc(Suc n)))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule rev_nth)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="length v - Suc (Suc (Suc n))"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply (metis Suc_inject Suc_less_eq add_Suc gr0_conv_Suc less_iff_Suc_add add.commute take_Suc_conv_app_nth)
  done

lemma rotate_simps: "
  rotate1 [] = [] \<and> rotate1 (x # xs) = xs @ [x]"
  apply(simp add:rotate1_def)
  done

lemma take_shorter_butlast: "
  n < length (w @[v])
  \<Longrightarrow> x = take n (w@[v])
  \<Longrightarrow> y = take n w
  \<Longrightarrow> x = y"
  apply(force)
  done

lemma take_drop_complete: "
  take n w = w
  \<Longrightarrow> drop n w = []"
  apply (metis append_self_conv append_take_drop_id)
  done

lemma take_drop_split: "
  take n w @ c = w
  \<Longrightarrow> c = drop n w"
  apply (metis append_take_drop_id same_append_eq)
  done

lemma elem_lem1: "
  a \<notin> set wc
  \<Longrightarrow> m = n
  \<Longrightarrow> a \<notin> set wb
  \<Longrightarrow> wc @ (take (n - length wc) [a]) = take n (wb @ (take (m - length wb) [a]))
  \<Longrightarrow> \<exists>c. wc @ c = wb"
  apply(clarsimp)
  apply(case_tac "n - length wc")
   apply(clarsimp)
   apply(case_tac "n - length wb")
    apply(clarsimp)
    apply(rule_tac
      x = "drop n wb"
      in exI)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "n - length wb")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "a  \<in> set wb")
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      A = "set (take n wb)"
      in set_mp)
    apply(rename_tac nat)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t = "take n wb"
      and s = "wc@[a]"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac nat nata)(*strict*)
  apply(clarsimp)
  done

lemma take_mult_drop: "
  n \<ge> m
  \<Longrightarrow> take n w = take m w @ (take (n - m) (drop m w))"
  apply(induct w arbitrary: n m)
   apply(rename_tac n m)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n m)(*strict*)
  apply(case_tac n)
   apply(rename_tac a w n m)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n m nat)(*strict*)
  apply(case_tac m)
   apply(rename_tac a w n m nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n m nat nata)(*strict*)
  apply(clarsimp)
  done

lemma take_max_no_append: "
  take n w = w@v
  \<Longrightarrow> v = []"
  apply(induct w arbitrary: v n)
   apply(rename_tac v n)(*strict*)
   apply(force)
  apply(rename_tac a w v n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w v n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v n nat)(*strict*)
  apply(clarsimp)
  done

lemma length_take_min: "
  length (take k w) = min k (length w)"
  apply(force)
  done

lemma length_take: "
  length w > 0
  \<Longrightarrow> take n (w@v) = w
  \<Longrightarrow> length w \<le> n"
  apply(induct w arbitrary: n v)
   apply(rename_tac n v)(*strict*)
   apply(force)
  apply(rename_tac a w n v)(*strict*)
  apply(case_tac n)
   apply(rename_tac a w n v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n v nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w v nat)(*strict*)
  apply(case_tac w)
   apply(rename_tac w v nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w v nat a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac v nat a list)(*strict*)
  apply(force)
  done

lemma take_reflects_mem: "
  v @ x # y = take k w
  \<Longrightarrow> x  \<in> set w"
  apply (metis in_set_conv_decomp in_set_takeD)
  done

lemma take_nth: "
  length w = Suc k
  \<Longrightarrow> w = take k w @ [w!k]"
  apply(rule_tac
      P = "\<lambda>q. q = take k w @ [w!k]"
      and t = "w"
      and s = "take (Suc k) w "
      in ssubst)
   apply(force)
  apply(rule List.take_Suc_conv_app_nth)
  apply(force)
  done

lemma take_shift: "
  take k (w@v) = take k (w @ (take k v))"
  apply(auto)
  apply(rule_tac
      s = "k - length w"
      and t = "(ord_class.min (k - length w) k)"
      in ssubst)
   prefer 2
   apply(force)
  apply(force)
  done

lemma take_append_prime: "
  length w = n
  \<Longrightarrow> take n (w@v) = w"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(force)
  done

lemma nth_take_drop_split: "
  i < length w
  \<Longrightarrow> (take i w)@[w!i]@(drop(Suc i)w) = w"
  apply(rule_tac
      P = "\<lambda>x. take i w @ [w ! i] @ drop (Suc i) w = x"
      and t = "w"
      and s = "take i w @ (drop i w)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "[w ! i] @ drop (Suc i) w = drop i w")
   apply(force)
  apply(clarsimp)
  apply(rule List.Cons_nth_drop_Suc)
  apply(force)
  done

lemma take_append2: "
  k \<le> length w
  \<Longrightarrow> take k (w@v) = take k w"
  apply(rule_tac
      t = "take k (w@v)"
      and s = "take k w @ take (k - length w) v"
      in ssubst)
   apply(rule take_append)
  apply(clarsimp)
  done

lemma take_append_irrelevant: "
  n = k1 + (length w1) + k2
  \<Longrightarrow> take n (w1 @ (take k2 w2)) = w1 @ (take k2 w2)"
  apply(rule_tac
      t = "n"
      and s = "k1 + (length w1) + k2"
      in ssubst)
   apply(force)
  apply(thin_tac "n = k1 + (length w1) + k2")
  apply(induct w1)
   apply(clarsimp)
   apply(rule_tac
      t = "(ord_class.min (k1 + k2) k2)"
      and s = "k2"
      in ssubst)
    apply(force)
   apply(force)
  apply(rename_tac a w1)(*strict*)
  apply(clarsimp)
  done

lemma take_take1: "
  n \<ge> m
  \<Longrightarrow> take n (take m w) = take m w"
  apply(rule_tac
      t = "take n (take m w)"
      and s = "take (ord_class.min n m) xs" for n m xs
      in ssubst)
   apply(rule take_take)
  apply(rule_tac
      t = "ord_class.min n m"
      and s = "m"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma take_take_prime: "
  k \<le> l
  \<Longrightarrow> take k w = take k (take l w)"
  apply(auto)
  apply(rule_tac
      t = "ord_class.min k l"
      and s = "k"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma take_shorter: "
  k \<le> n
  \<Longrightarrow> take n w = take n v
  \<Longrightarrow> take k w = take k v"
  apply(rule_tac
      t = "take k w"
      and s = "take k (take n w)"
      in ssubst)
   apply(rule take_take_prime)
   apply(force)
  apply(rule_tac
      t = "take k v"
      and s = "take k (take n v)"
      in ssubst)
   apply(rule take_take_prime)
   apply(force)
  apply(rule_tac
      t = "take n v"
      and s = "take n w"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma take_take_bi: "
  take k w = take k v
  \<Longrightarrow> take (k - n) w = take (k - n) v"
  apply(rule_tac
      t = "take (k - n) w"
      and s = "take (k - n) (take k w)"
      in ssubst)
   apply(rule take_take_prime)
   apply(force)
  apply(rule_tac
      t = "take (k - n) v"
      and s = "take (k - n) (take k v)"
      in ssubst)
   apply(rule take_take_prime)
   apply(force)
  apply(force)
  done

lemma take_1_rev: "
  take (Suc 0) (List.rev (w@[x])) = [x]"
  apply(auto)
  done

lemma take_one: "
  k>0
  \<Longrightarrow> take k (x#w) = x#(take (k - 1) w)"
  apply(case_tac k)
   apply(auto)
  done

lemma take_nth_crop: "
  take n w = take n v
  \<Longrightarrow> k < n
  \<Longrightarrow> w!k = v!k"
  apply(rule_tac
      t = "w!k"
      and s = "(take n w)!k"
      in subst)
   apply(rule nth_take)
   apply(force)
  apply(rule_tac
      t = "v!k"
      and s = "(take n v)!k"
      in subst)
   apply(rule nth_take)
   apply(force)
  apply(force)
  done

lemma head_in_set2: "
  [a] = take (Suc 0) w
  \<Longrightarrow> a \<in> set w"
  apply(case_tac w)
   apply(auto)
  done

lemma takePrecise: "
  w = take (length w) (w@v)"
  apply(rule_tac
      t = "take (length w) (w@v)"
      and s = "take (length w) w @ take ((length w) - (length w)) v"
      in ssubst)
   apply(rule List.take_append)
  apply(force)
  done

lemma length_take_prime: "
  take k z = y
  \<Longrightarrow> length y < k
  \<Longrightarrow> take k z = z"
  apply(auto)
  done

lemma take_last: "
  length \<gamma>1 = Suc n
  \<Longrightarrow> take n \<gamma>1 @ [last \<gamma>1] = \<gamma>1"
  apply(subgoal_tac "\<exists>y a. \<gamma>1 = y@[a]")
   apply(clarsimp)
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  done

lemma append_take_drop_id_hlp: "
  take n w = x
  \<Longrightarrow> w = x@drop n w"
  apply(clarsimp)
  done

lemma take_take2: "
  take k1 (take (k1 + k2) w) = take (k1::nat) w"
  apply(rule_tac
      t = "take k1 (take (k1 + k2) w)"
      and s = "take (ord_class.min k1 (k1 + k2)) w"
      in ssubst)
   apply(rule take_take)
  apply(rule_tac
      t = "(ord_class.min k1 (k1 + k2))"
      and s = "k1"
      in ssubst)
   apply(auto)
  done

lemma takePrefix: "
  take k r = y
  \<Longrightarrow> \<exists>v. r = y @ v"
  apply(case_tac "length r \<le> k")
   apply(subgoal_tac "take k r = r")
    apply(clarsimp)
   apply(force)
  apply(subgoal_tac "\<exists>r1 r2. r = r1@r2 \<and> length r1 = k")
   apply(clarsimp)
  apply(rule_tac
      x = "take k r"
      in exI)
  apply(rule_tac
      x = "drop k r"
      in exI)
  apply(auto)
  done

lemma takeShorter: "
  length (take k z) \<le> k"
  apply(induct_tac k)
   apply(auto)
  done

lemma takeCases: "
  (\<exists>x. (take k y)@x = y) \<or> (\<exists>x. (take k y) = y@x)"
  apply(case_tac "length y \<le> k")
   apply(auto)
  apply(rule_tac
      x = "drop k y"
      in exI)
  apply(auto)
  done

lemma TakeLength1: "
  length y \<le> k
  \<Longrightarrow> (\<exists>x. (take k y)@x = y)"
  apply(auto)
  done

lemma TakeLength2: "
  length y>k
  \<Longrightarrow> (\<exists>x. (take k y)@x = y)"
  apply(rule_tac
      x = "drop k y"
      in exI)
  apply(auto)
  done

lemma revTakeSuccessImpliesTailElem: "
  take (Suc 0) (List.rev w) = x
  \<Longrightarrow> \<exists>y. w = y @ x"
  apply(case_tac "length w")
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w'@[x']")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(blast)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma setTakeIndexSubset: "
  set (take k1 v) \<subseteq> set (take (k1 + k2) v)"
  apply(induct v arbitrary: k1 k2)
   apply(rename_tac k1 k2)(*strict*)
   apply(auto)
  apply(rename_tac a v k1 k2 x)(*strict*)
  apply(case_tac k1)
   apply(rename_tac a v k1 k2 x)(*strict*)
   apply(auto)
  done

lemma drop_append: "
  w = x@v
  \<Longrightarrow> drop (length x) w = v"
  apply(force)
  done

lemma drop_distrib_append: "
  n \<le> length x
  \<Longrightarrow> drop n (x@v) = (drop n x) @ v"
  apply(induct n arbitrary: x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac n x)(*strict*)
  apply(clarsimp)
  done

lemma drop_reflects_mem: "
  v @ x # y = drop k w
  \<Longrightarrow> x  \<in> set w"
  apply(metis append_eq_append_conv2 append_take_drop_id in_set_conv_decomp)
  done

lemma drop_length: "
  length w \<le> n
  \<Longrightarrow> drop n (w@v) = drop (n - length w) v"
  apply(induct w arbitrary: n v)
   apply(rename_tac n v)(*strict*)
   apply(force)
  apply(rename_tac a w n v)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w n v)(*strict*)
   apply(force) +
  done

lemma drop_prefix_closureise: "
  drop (length w) (w@v) = v"
  apply(auto)
  done

lemma drop_append2: "
  length w = n
  \<Longrightarrow> drop n (w@v) = v"
  apply(induct w)
   apply(auto)
  done

lemma first_drop: "
  w = a # w'
  \<Longrightarrow> a # (drop (Suc 0) (w@v)) = w@v"
  apply(induct w arbitrary: a w' v)
   apply(rename_tac a w' v)(*strict*)
   apply(auto)
  done

lemma drop1: "
  drop (Suc 0) (a#w) = w"
  apply(clarsimp)
  done

lemma proper_take_away: "
  w@a#X = b#Y
  \<Longrightarrow> drop (Suc 0) (w@[a])@X = Y"
  apply(case_tac w)
   apply(auto)
  done

lemma dropPrecise: "
  v = drop (length w) (w@v)"
  apply(rule_tac
      t = "take (length w) (w@v)"
      and s = "take (length w) w @ take ((length w) - (length w)) v"
      in ssubst)
   apply(rule List.take_append)
  apply(force)
  done

lemma drop_length_leq: "
  length v \<ge> n
  \<Longrightarrow> drop n w @ x = drop n v
  \<Longrightarrow> length w \<le> length v"
  apply (metis drop_length_append le_diff_iff length_drop linear order_trans)
  done

lemma hd_drop1_id: "
  length x > 0
  \<Longrightarrow> hd x#(drop (Suc 0) x) = x"
  apply(case_tac x)
   apply(auto)
  done

lemma take_last2: "
  length \<gamma>1 = Suc na
  \<Longrightarrow> drop na \<gamma>1 = [y]
  \<Longrightarrow> y = last \<gamma>1"
  apply(subgoal_tac "\<exists>y a. \<gamma>1 = y@[a]")
   apply(clarsimp)
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  done

lemma append_take_drop_id_hlp1: "
  length w>0
  \<Longrightarrow> w!0 = x
  \<Longrightarrow> w = x#drop (Suc 0) w"
  apply(rule_tac
      t = "x#drop (Suc 0) w"
      and s = "[x]@drop (Suc 0) w"
      in ssubst)
   apply(force)
  apply(rule append_take_drop_id_hlp)
  apply(auto)
  apply(case_tac w)
   apply(auto)
  done

lemma nth_drop_0: "
  length w>0
  \<Longrightarrow> w = (w!0)#(drop (Suc 0) w)"
  apply(auto)
  apply(induct w)
   apply(auto)
  done

lemma butlast_last_prime: "
  length w > 0
  \<Longrightarrow> w = butlast w @ [last w]"
  apply(force)
  done

lemma butlast_last: "
  length w>0
  \<Longrightarrow> butlast w @ [last w] = w"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(force)
  done

lemma butlast_append: "
  length v>0
  \<Longrightarrow> butlast (w@v) = w @ butlast v"
  apply(induct w)
   apply(auto)
  done

lemma butlast_snoc_2: "
  butlast(w@v@[a]) = w@v"
  apply(simp add: butlast_append)
  done

lemma butlast_snoc_3: "
  butlast(w@v@x@[a]) = w@v@x"
  apply(simp add: butlast_append)
  done

lemma butlast_snoc_4: "
  butlast(w@v@x@y@[a]) = w@v@x@y"
  apply(simp add: butlast_append)
  done

lemma butlast_append_prime: "
  v \<noteq> []
  \<Longrightarrow> butlast v = x
  \<Longrightarrow> butlast (a@v) = a@x"
  apply(induct v rule: rev_induct)
   apply(auto)
  apply(rename_tac xa)(*strict*)
  apply(rule_tac
      t = "a@x@[xa]"
      and s = "(a@x)@[xa]"
      in ssubst)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(rule butlast_snoc)
  done

lemma butlast_pull_out: "
  w \<noteq> []
  \<Longrightarrow> w = butlast v
  \<Longrightarrow> a@w = butlast (a@v)"
  apply(induct w arbitrary: v rule: rev_induct)
   apply(rename_tac v)(*strict*)
   apply(auto)
  apply(rename_tac x xs v)(*strict*)
  apply(rule_tac
      t = "butlast v"
      and s = "xs@[x]"
      in ssubst)
   apply(rename_tac x xs v)(*strict*)
   apply(force)
  apply(rename_tac x xs v)(*strict*)
  apply(rule sym)
  apply(rule butlast_append_prime)
   apply(rename_tac x xs v)(*strict*)
   apply(force)
  apply(rename_tac x xs v)(*strict*)
  apply(force)
  done

lemma butlast_pull_out2: "
  w \<noteq> []
  \<Longrightarrow> x = last w
  \<Longrightarrow> a@w = (butlast (a@w))@[x]"
  apply(induct w rule: rev_induct)
   apply(auto)
  apply(rename_tac xs)(*strict*)
  apply(rule_tac
      t = "a@xs@[x]"
      and s = "(a@xs)@[x]"
      in ssubst)
   apply(rename_tac xs)(*strict*)
   apply(force)
  apply(rename_tac xs)(*strict*)
  apply(rule sym)
  apply(rule butlast_snoc)
  done

lemma butlast_shift: "
  w \<noteq> []
  \<Longrightarrow> butlast (v@w) = v@butlast w"
  apply(induct v)
   apply(auto)
  done

lemma trivButLast: "
  set (butlast x) \<subseteq> set x"
  apply(rule subsetI)
  apply(rename_tac xa)(*strict*)
  apply(rule List.in_set_butlastD)
  apply(clarsimp)
  done

lemma butLastSimp: "
  butlast (aa @ [v, a]) = aa @ [v]"
  apply(induct aa)
   apply(clarsimp)
  apply(rename_tac aa aaa)(*strict*)
  apply(clarsimp)
  done

lemma prop_last: "
  (w \<noteq> [] \<Longrightarrow> P (last w))
  \<Longrightarrow> (w = [] \<Longrightarrow> P a)
  \<Longrightarrow> P (last (a#w))"
  apply(auto)
  done

lemma last_triv: "
  length w = Suc 0
  \<Longrightarrow> [last w] = w"
  apply(case_tac w)
   apply(auto)
  done

lemma last_filter_select: "
  w = w'@[x]
  \<Longrightarrow> P x
  \<Longrightarrow> x = last (filter P w)"
  apply(induct w arbitrary: x)
   apply(rename_tac x)(*strict*)
   apply(auto)
  done

lemma last_append: "
  w \<noteq> []
  \<Longrightarrow> last w = last (v@w)"
  apply(force)
  done

lemma last_eq_then_eq: "
  last w = a
  \<Longrightarrow> last w = b
  \<Longrightarrow> a = b"
  apply(force)
  done

lemma lengthGT: "
  length w > 0
  \<Longrightarrow> last (a#w) = last w"
  apply(auto)
  done

lemma length0: "
  length w = 0
  \<Longrightarrow> last (a#w) = a"
  apply(auto)
  done

lemma last_triv_prime: "
  [x] = w
  \<Longrightarrow> x = last w"
  apply(auto)
  done

lemma last_append_mp: "
  set w \<subseteq> A
  \<Longrightarrow> a \<in> A
  \<Longrightarrow> x = last(a#w)
  \<Longrightarrow> x \<in> A"
  apply(auto)
  done

lemma last_transfer: "
  length w > 0
  \<Longrightarrow> x  \<in> last(y#w)
  \<Longrightarrow> x  \<in> last w"
  apply(auto)
  done

lemma last_nth: "
  length w>0
  \<Longrightarrow> Suc i = length w
  \<Longrightarrow> last w = w!i"
  apply(subgoal_tac "\<forall>i. 0 < length w \<and> Suc i = length w \<longrightarrow> last w = w!i")
   apply(blast)
  apply(rule_tac
      xs = "w"
      in rev_induct)
   apply(auto)
  done

lemma nth_append_1: "
  i < length w
  \<Longrightarrow> (w@v)!i = w!i"
  apply(rule_tac
      t = "(w@v)!i"
      and s = "(if i < length w then w ! i else v ! (i - length w))"
      in ssubst)
   apply(rule List.nth_append)
  apply(force)
  done

lemma second_of_two: "
  [a,b]!(Suc 0) = b"
  apply(clarsimp)
  done

lemma first_of_two: "
  [a,b]!0 = a"
  apply(clarsimp)
  done

lemma inSet_from_head_and_rest_nth: "
  a \<in> A
  \<Longrightarrow> w!(i - Suc 0) \<in> A
  \<Longrightarrow> (a#w)!i  \<in> A"
  apply(rule_tac
      t = "(a#w)!i"
      and s = "(if i = 0 then a else w ! (i - 1))"
      in ssubst)
   apply(rule nth_Cons')
  apply(auto)
  done

lemma nth_first: "
  a = (a#y)!0"
  apply(force)
  done

lemma length_1_cons_nth: "
  length w = Suc 0
  \<Longrightarrow> w = [w!0]"
  apply(case_tac w)
   apply(auto)
  done

lemma nth_shift_append: "
  length w \<le> x
  \<Longrightarrow> length w + y = x
  \<Longrightarrow> (w@v)!x = v!y"
  apply(force)
  done

lemma nth_0: "
  x = 0
  \<Longrightarrow> [a]!x = a"
  apply(force)
  done

lemma last_nth_in: "
  w \<noteq> []
  \<Longrightarrow> w ! (length w - Suc 0)  \<in> set w"
  apply(induct w rule: rev_induct)
   apply(auto)
  done

lemma set_elem_nth: "
  x \<in> set w
  \<Longrightarrow> \<exists>i < length w. w!i = x"
  apply(induct w)
   apply(auto)
  apply(rename_tac a w i)(*strict*)
  apply(rule_tac
      x = "Suc i"
      in exI)
  apply(force)
  done

lemma set_subset_by_nth_elem: "
  \<forall>i < length w. w!i  \<in> A
  \<Longrightarrow> set w \<subseteq> A"
  apply(induct w)
   apply(auto)
  apply(rename_tac a w x)(*strict*)
  apply(subgoal_tac "\<exists>i < length w. w!i = x")
   apply(rename_tac a w x)(*strict*)
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(rename_tac a w x)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w i)(*strict*)
  apply(auto)
  done

lemma nth_shift: "
  x = w!i
  \<Longrightarrow> y = (a#w)!(Suc i)
  \<Longrightarrow> x = y"
  apply(auto)
  done

lemma nth_set: "
  i \<le> length r
  \<Longrightarrow> i = Suc n
  \<Longrightarrow> (q # r) ! i  \<in> set r"
  apply(auto)
  done

lemma hasPositionInSet: "
  a \<in> set(b#w)
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> \<exists>i. i < length w \<and> a = w!i"
  apply(induct w)
   apply(auto)
  apply(rename_tac aX w i)(*strict*)
  apply(rule_tac
      x = "Suc i"
      in exI)
  apply(auto)
  done

lemma listEqI: "
  length w1 = length w2
  \<Longrightarrow> (\<And>i. i < length w1 \<longrightarrow> w1!i = w2!i)
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "\<And>n. \<forall>w1 w2. n = length w1 \<and> n = length w2 \<and> (\<forall>i. i < length w1 \<longrightarrow> w1!i = w2!i) \<longrightarrow> w1 = w2")
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "length w1 = length w2")
  apply(thin_tac "(\<And>i. i < length w1 \<longrightarrow> w1 ! i = w2 ! i)")
  apply(induct_tac n)
   apply(rename_tac n)(*strict*)
   apply(auto)
  apply(rename_tac na w1 w2)(*strict*)
  apply(case_tac w1)
   apply(rename_tac na w1 w2)(*strict*)
   apply(auto)
  apply(rename_tac w2 a list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac w2 a list)(*strict*)
   apply(auto)
  apply(rename_tac a list aa lista)(*strict*)
  apply(erule_tac
      x = "list"
      in allE)
  apply(erule_tac
      x = "lista"
      in allE)
  apply(auto)
  done

lemma foldl_conv_concat: "
  foldl (@) xs xss = xs @ concat xss"
  apply(induct xss arbitrary: xs)
   apply(rename_tac xs)(*strict*)
   apply(force)
  apply(rename_tac a xss xs)(*strict*)
  apply(clarsimp)
  done

lemma concat_conv_foldl: "
  concat xss = foldl (@) [] xss"
  apply (simp add: foldl_conv_concat)
  done

lemma foldl_append_initial_pullout: "
  foldl (@) (a#v) w = [a]@(foldl (@) v w)"
  apply(induct w arbitrary: a v)
   apply(rename_tac a v)(*strict*)
   apply(auto)
  done

lemma rev_map_rev: "
  List.rev (map f (List.rev w)) = map f w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma map_foldl_map_only_Some: "
  None \<notin> set w
  \<Longrightarrow> map Some (foldl (@) [] (map (case_option [] (\<lambda>a. [a])) w)) = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w aa)(*strict*)
  apply(rule_tac
      t = "foldl (@) [aa] (map (case_option [] (\<lambda>a. [a])) w)"
      and s = "[aa]@(foldl (@) [] (map (case_option [] (\<lambda>a. [a])) w))"
      in ssubst)
   apply(rename_tac w aa)(*strict*)
   apply(rule foldl_append_initial_pullout)
  apply(rename_tac w aa)(*strict*)
  apply(clarsimp)
  done

lemma map_Some_subset: "
  set (map Some w) \<subseteq> Some ` A
  \<Longrightarrow> set w \<subseteq> A"
  apply(auto)
  done

lemma map_decomp: "
  map f w = w1@[x]@ w2
  \<Longrightarrow> \<exists>w1' w2' x'. w = w1'@[x']@w2' \<and> map f w1' = w1 \<and> map f w2' = w2 \<and> f x' = x"
  apply(rule_tac
      x = "take (length w1) w"
      in exI)
  apply(rule_tac
      x = "drop (Suc(length w1)) w"
      in exI)
  apply(rule_tac
      x = "w!(length w1)"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply (metis append_take_drop_id_hlp drop_length_append le_neq_implies_less length_map list.simps(3) Cons_nth_drop_Suc self_append_conv takePrecise)
  apply (metis (no_types, hide_lams) append_Cons append_Nil append_Nil2 append_eq_append_conv2 append_self_conv drop_map drop_prefix_closureise length_append length_append_singleton length_map list.distinct(1) list.simps(8) nat_neq_iff not_add_less1 nth_append_length nth_map takePrecise take_map)
  done

lemma filter_only_Some: "
  None \<notin> set w
  \<Longrightarrow> filter (case_option False (\<lambda>x. True)) w = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w aa)(*strict*)
  apply(clarsimp)
  done

lemma filter_should_have: "
  a  \<in> set w
  \<Longrightarrow> filter P w = []
  \<Longrightarrow> P a
  \<Longrightarrow> Q"
  apply(induct w)
   apply(auto)
  apply(rename_tac aa w)(*strict*)
  apply(case_tac "P aa")
   apply(rename_tac aa w)(*strict*)
   apply(auto)
  done

lemma filter_app: "
  filter P w @ (filter P v) = filter P (w@v)"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(auto)
  done

lemma equal_hd: "
  i < Suc (length w)
  \<Longrightarrow> hd (drop i (x # map f w)) = hd (drop i (x # map f w @ wa))"
  apply(case_tac "drop i (x # map f w)")
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "drop i (x # map f w)")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac "drop i (x # map f w @ wa)")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply (metis Cons_eq_appendI List.drop_append add_Suc length_map list.size(4) add.commute plus_nat.add_0 unequal_by_first_char)
  done

lemma equal_tl: "
  i < Suc (length w)
  \<Longrightarrow> tl (drop i (x # map f w @ wa)) \<noteq> tl (drop i (x # map f w)) @ wa
  \<Longrightarrow> Q"
  apply(case_tac "drop i (x # map f w)")
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(case_tac "drop i (x # map f w)")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(case_tac "drop i (x # map f w @ wa)")
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa lista)(*strict*)
  apply(clarsimp)
  apply (metis List.drop_append add_diff_inverse diff_add_0 drop_0 drop_Suc drop_Suc_Cons length_map not_less_eq list.sel(2) tl_drop)
  done

lemma tl_drops: "
  x # w = tl (drop i (x # w))
  \<Longrightarrow> Q"
  apply (metis One_nat_def Suc_eq_plus1_left diff_less_Suc drop_Suc drop_Suc_Cons length_drop less_not_refl list.size(4) add.commute tl_drop)
  done

lemma tl_drops2: "
  x # w = tl (drop i w)
  \<Longrightarrow> Q"
  apply (metis One_nat_def Suc_eq_plus1_left diff_less_Suc drop_Suc length_drop less_not_refl list.size(4) add.commute tl_drop)
  done

lemma tl_append: "
  i < Suc (length w)
  \<Longrightarrow> tl (drop i (x # map f w)) @ wa = tl (drop i (x # map f w @ wa))"
  apply (metis drop_Suc drop_Suc_Cons equal_tl tl_drop)
  done

lemma length_eq_prepend_append_singleton: "
  A # x = y @ [B]
  \<Longrightarrow> length x = length x'
  \<Longrightarrow> length y = length y'
  \<Longrightarrow> length x' = length y'"
  apply (metis Suc_length add_Suc_shift diff_add_inverse lengthDec2 list.size(4))
  done

lemma rev_drop_nth: "
  n < length v
  \<Longrightarrow> rev v ! n = drop (length v - Suc n) v ! 0"
  apply (metis diff_Suc_less diff_self_eq_0 less_imp_diff_less Cons_nth_drop_Suc nth_first rev_nth)
  done

lemma last_drop_rev_nth: "
  w' \<noteq> []
  \<Longrightarrow> drop (length w' - Suc 0) w' = [rev w' ! 0]"
  apply (metis One_nat_def append_butlast_last_id append_eq_conv_conj hd_conv_nth hd_rev length_butlast rev_is_Nil_conv rotate_simps)
  done

lemma take_nth_rev: "
  Suc (Suc (Suc nata)) = length v
  \<Longrightarrow> take (length v - Suc (Suc nata)) v = [rev v ! Suc (Suc nata)]"
  apply(rule_tac
      t="(length v - Suc (Suc nata))"
      and s="Suc 0"
      in ssubst)
   apply(force)
  apply(case_tac v)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply (metis gr0_conv_Suc list.sel last_nth last_rev length_Suc length_rev length_rotate1 list.simps(3) rev.simps(2) rotate_simps)
  done

lemma take_last_nth_append: "
  c \<noteq> []
  \<Longrightarrow> take (length c - Suc 0) c @ [c ! (length c - Suc 0)] = c"
  apply(rule_tac xs="c" in rev_cases)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma in_set_has_position: "
  x  \<in> set w
  \<Longrightarrow> \<exists>w1 w2. w1@[x]@w2 = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x = "[]"
      in exI)
   apply(rule_tac
      x = "w"
      in exI)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(rule_tac
      x = "a#w1"
      in exI)
  apply(rule_tac
      x = "w2"
      in exI)
  apply(clarsimp)
  done

lemma map_the_filer_rev: "
  w' = map the (filter (case_option False (\<lambda>x. True)) (rev w))
  \<Longrightarrow> filter (case_option False (\<lambda>x. True)) w = rev (map Some w')"
  apply(clarsimp)
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w aa)(*strict*)
  apply(clarsimp)
  done

lemma filter_eq: "
  (\<And>x. x  \<in> set w \<Longrightarrow> P x)
  \<Longrightarrow> filter P w = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma filter_eq_apply: "
  (\<And>x. x \<in> set w \<Longrightarrow> x \<noteq> None)
  \<Longrightarrow> map the (filter (case_option False (\<lambda>x. True)) (rev w)) = map the (rev w)"
  apply(subgoal_tac "filter (case_option False (\<lambda>x. True)) (rev w) = rev w")
   apply(clarsimp)
  apply(rule filter_eq)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma tl_nth_eq: "
  w \<noteq> []
  \<Longrightarrow> [w!0] = a
  \<Longrightarrow> w = a@(tl w)"
  apply (metis append_Cons append_Nil hd_conv_nth list.collapse)
  done

lemma inv_into_f_eq_map: "
  inj_on f A
  \<Longrightarrow> set w \<subseteq> A
  \<Longrightarrow> map (inv_into A f) (map f w) = w"
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply (metis inv_into_f_eq nth_mem subsetD)
  done

lemma inv_into_f_eq_map2: "
  inj_on f A
  \<Longrightarrow> set w \<subseteq> A
  \<Longrightarrow> map (inv_into A f \<circ> f) w = w"
  apply(metis inv_into_f_eq_map map_map)
  done

lemma trivTl: "
  set (tl x) \<subseteq> set x"
  apply(induct x)
   apply(clarsimp)
  apply(rename_tac a x)(*strict*)
  apply(clarsimp)
  done

lemma trivMult: "
  (0::nat) < a
  \<Longrightarrow> a*a^n>0"
  apply(case_tac a)
   apply(arith)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma trivTl2: "
  length a > 0
  \<Longrightarrow> tl (a @ [v]) = tl a @ [v]"
  apply(clarsimp)
  done

lemma shorterEQ: "
  a@[s] = b@[s]
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> Q"
  apply(auto)
  done

lemma dropLast: "
  a@(b#c) = d@[s]
  \<Longrightarrow> \<exists>x. x @ [s] = b#c"
  apply(rule_tac
      P = "a @ b # c = d @ [s]"
      and Q = "\<exists>x. x @ [s] = b # c"
      in impE)
    apply(rule rev_induct)
     apply(clarsimp)
    apply(rename_tac x xs)(*strict*)
    apply(rule impI)
    apply(clarsimp) +
  done

lemma card1Elem1: "
  card {x} = Suc 0"
  apply(rule_tac
      s = "Suc (card {})"
      and t = "Suc 0"
      in ssubst)
   apply(rule sym)
   apply(rule_tac
      s = "card {}"
      and t = "0"
      in ssubst)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule_tac
      x = "x"
      and A = "{}"
      in card_insert_disjoint)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma card1Elem1_prime: "
  A = {a}
  \<Longrightarrow> card A = Suc 0"
  apply(rule_tac
      t = "A"
      and s = "{a}"
      in ssubst)
   apply(force)
  apply(rule card1Elem1)
  done

lemma existenceOfLast: "
  length x>0
  \<Longrightarrow> \<exists>xp xa. x = xp @ [xa]"
  apply(rule_tac
      P = "length x>0"
      and Q = "\<exists>xp xa. x = xp@[xa]"
      in impE)
    defer
    apply(blast,blast)
  apply(rule_tac
      xs = "x"
      in rev_induct)
   apply(clarsimp)
  apply(rename_tac xa xs)(*strict*)
  apply(clarsimp)
  done

lemma drop_with_elem_head: "
  length w'' \<ge> Suc n
  \<Longrightarrow> \<exists>x. x # drop (length w'' - n) w'' = drop (length w'' - Suc n) w''"
  apply(subgoal_tac "\<exists>x. Suc n+x=length w''")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="length w''-n"
      and s="Suc x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="length w''-Suc n"
      and s="x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply (metis Suc_n_not_le_n id_take_nth_drop le_add2 linorder_le_less_linear take_drop_split xt1(6))
  apply(rule_tac
      x="length w''-Suc n"
      in exI)
  apply(force)
  done

lemma drop_with_elem_head2: "
  length w'' \<ge> Suc n
  \<Longrightarrow> x # drop (length w'' - n) w'' = drop (length w'' - Suc n) w''
  \<Longrightarrow> rev w'' ! n = x"
  apply (metis length_drop less_eq_Suc_le nth_via_drop rev_nth)
  done

lemma nth_appendX: "
  i < length w
  \<Longrightarrow> w ! i = (w@v) ! i"
  apply (metis nth_append_1)
  done

lemma foldl_empty: "
  (\<And>a. a \<in> set w \<Longrightarrow> a=[])
  \<Longrightarrow> foldl (@) [] w = []"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="a"
      in meta_allE)
  apply(clarsimp)
  done

lemma exists_single: "
  length w=Suc 0
  \<Longrightarrow> \<exists>x. w=[x]"
  apply(case_tac w)
   apply(force)+
  done

lemma tl_nth: "
  Suc n<length w
  \<Longrightarrow> (tl w) ! n = w!(Suc n)"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma nth_drop: "
  i+ia<length w
  \<Longrightarrow> w ! (i + ia) = drop i w ! ia"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma nth_last_of_one: "
  v=w@[a]
  \<Longrightarrow> length w=n
  \<Longrightarrow> a=b
  \<Longrightarrow> v!n = b"
  apply(force)
  done

lemma nth_append_2: "
  i \<ge> length w
  \<Longrightarrow>(w@v)!i = v!(i - length w)"
  apply(rule_tac
      t = "(w@v)!i"
      and s = "(if i < length w then w ! i else v ! (i - length w))"
      in ssubst)
   apply(rule List.nth_append)
  apply(clarsimp)
  done

lemma nth_append_2_prime_prime: "
  n=length w
  \<Longrightarrow> (w@v)!n = v!0"
  apply(clarsimp)
  apply(rule_tac
      t="(w @ v) ! length w"
      and s="v ! (length w-length w)"
      in ssubst)
   apply(rule nth_append_2)
   apply(force)
  apply(force)
  done

lemma rev_nth: "
  i<length w
  \<Longrightarrow> (rev w)!i=w!(length w-i-Suc 0)"
  apply(induct w arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac a w i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length w-i")
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "i=length w")
    apply(rename_tac a w i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a w i)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w)(*strict*)
   apply (metis length_rev nth_append_2_prime_prime nth_first)
  apply(rename_tac a w i nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(rev w @ [a]) ! i"
      and s="(rev w) ! i"
      in ssubst)
   apply(rename_tac a w i nat)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac a w i nat)(*strict*)
  apply(erule_tac
      x="i"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac w i nat)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac w i nat)(*strict*)
   apply(force)
  apply(rename_tac w i nat)(*strict*)
  apply(subgoal_tac "length w=Suc nat+i")
   apply(rename_tac w i nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w i nat)(*strict*)
  apply(clarsimp)
  done

lemma foldl_empty2: "
  foldl (@) [] x = []
  \<Longrightarrow> i<length x
  \<Longrightarrow> x!i=[]"
  apply(induct x arbitrary: i rule: rev_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs i)(*strict*)
  apply(case_tac "i=length xs")
   apply(rename_tac xs i)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs i)(*strict*)
  apply(rule_tac
      t="(xs @ [[]]) ! i"
      and s=" xs ! i"
      in ssubst)
   apply(rename_tac xs i)(*strict*)
   apply (metis less_SucE nth_append_1)
  apply(rename_tac xs i)(*strict*)
  apply(force)
  done

lemma length_shorter_than_in_composition: "
  j<length \<pi>s
  \<Longrightarrow> length (\<pi>s ! j) \<le> length (foldl (@) [] \<pi>s)"
  apply(induct \<pi>s arbitrary: j rule: rev_induct)
   apply(rename_tac j)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs j)(*strict*)
  apply(clarsimp)
  apply(case_tac "j=length xs")
   apply(rename_tac x xs j)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs j)(*strict*)
  apply(rule_tac
      t="(xs @ [x]) ! j"
      and s=" xs ! j"
      in ssubst)
   apply(rename_tac x xs j)(*strict*)
   apply (metis less_SucE nth_append_1)
  apply(rename_tac x xs j)(*strict*)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(clarsimp)
  done

lemma distrib_add_apppend_with_map: "
  foldl (+) 0 (map length \<pi>s) = length (foldl (@) [] \<pi>s)"
  apply(induct \<pi>s rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  done

lemma split_string_into_single_item_strings: "
  foldl (@) [] (map (\<lambda>x. [x]) w) = w"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  done

lemma set_nth_foldl: "
  i < length \<alpha>
  \<Longrightarrow> set (\<alpha> ! i) \<subseteq> set (foldl (@) [] \<alpha>)"
  apply(induct \<alpha> arbitrary: i rule: rev_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs i xa)(*strict*)
  apply(case_tac "i=length xs")
   apply(rename_tac x xs i xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i xa)(*strict*)
  apply(subgoal_tac "(xs @ [x]) ! i=xs!i")
   apply(rename_tac x xs i xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in meta_allE)
   apply(force)
  apply(rename_tac x xs i xa)(*strict*)
  apply (metis less_SucE nth_append_1)
  done

lemma foldl_distrib_append: "
  foldl (@) [] (w1@w2) = (foldl (@) [] w1) @ (foldl (@) [] w2)"
  apply (metis concat_append concat_conv_foldl foldl_conv_concat)
  done

lemma hlp1: "
  na\<le>length \<alpha>
  \<Longrightarrow> w=(take na \<alpha> @ w # drop (Suc na) \<alpha>) ! na"
  apply (metis append_take_drop_id drop_distrib_append eq_Nil_appendI nat_less_le nth_list_update_eq nth_via_drop self_append_conv take_append_prime upd_conv_take_nth_drop)
  done

lemma foldl_equal: "
  length w = length v
  \<Longrightarrow> (\<And>y. y < length w \<Longrightarrow> w ! y = v ! y)
  \<Longrightarrow> foldl (@) [] w = foldl (@) [] v"
  apply(induct w arbitrary: v rule: rev_induct)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs v)(*strict*)
  apply(case_tac v)
   apply(rename_tac x xs v)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac x xs v)(*strict*)
    apply(force)
   apply(rename_tac x xs v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs v a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. v=w'@[x']")
   apply(rename_tac x xs v a list)(*strict*)
   prefer 2
   apply(rule_tac NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xs v a list)(*strict*)
  apply(thin_tac "v=a#list")
  apply(clarify)
  apply(rename_tac x xs v a list w' x')(*strict*)
  apply(erule_tac
      x="w'"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs v a list w' x')(*strict*)
   apply(force)
  apply(rename_tac x xs v a list w' x')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs v a list w' x' y)(*strict*)
   apply(erule_tac
      x="y"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac x xs w' x' y)(*strict*)
   apply(rule_tac
      t="xs!y"
      and s="(xs @ [x]) ! y"
      in ssubst)
    apply(rename_tac x xs w' x' y)(*strict*)
    apply (metis nth_append_1)
   apply(rename_tac x xs w' x' y)(*strict*)
   apply(rule_tac
      t="w'!y"
      and s="(w' @ [x']) ! y"
      in ssubst)
    apply(rename_tac x xs w' x' y)(*strict*)
    apply (metis nth_append_1)
   apply(rename_tac x xs w' x' y)(*strict*)
   apply(force)
  apply(rename_tac x xs v a list w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' x')(*strict*)
  apply(erule_tac
      x="length w'"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x xs w')(*strict*)
  apply(rule_tac
      t="(xs @ [x]) ! length w'"
      and s="x"
      in ssubst)
   apply(rename_tac x xs w')(*strict*)
   apply (metis nth_append_length)
  apply(rename_tac x xs w')(*strict*)
  apply(force)
  done

lemma foldl_decomp: "
  x<length x1
  \<Longrightarrow> foldl (@) [] (take x x1) @ x1 ! x @ foldl (@) [] (drop (Suc x) x1) = foldl (@) [] x1"
  apply(rule_tac
      t="x1 ! x @ foldl (@) [] (drop (Suc x) x1)"
      and s="foldl (@) [] ([x1 ! x] @ (drop (Suc x) x1))"
      in ssubst)
   apply(rule_tac
      t="foldl (@) [] ([x1 ! x] @ drop (Suc x) x1)"
      and s=" (foldl (@) [] ([x1 ! x]) @ (foldl (@) [] (drop (Suc x) x1))) "
      in ssubst)
    apply(simp only: foldl_distrib_append)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. foldl (@) [] (take x x1) @ foldl (@) [] ([x1 ! x] @ drop (Suc x) x1) = foldl (@) [] X"
      and s="take x x1 @ (x1!x) # (drop (Suc x) x1)"
      in ssubst)
   apply (metis append_take_drop_id Cons_nth_drop_Suc)
  apply(rule sym)
  apply(rule_tac
      t="[x1 ! x] @ drop (Suc x) x1"
      and s="x1 ! x # drop (Suc x) x1"
      in ssubst)
   apply(force)
  apply(rule foldl_distrib_append)
  done

lemma elements_preserved_under_foldl: "
  a  \<in> set w
  \<Longrightarrow> set a \<subseteq> set(foldl (@) [] w)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac aa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa w x)(*strict*)
  apply(erule disjE)
   apply(rename_tac aa w x)(*strict*)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply (metis foldl_conv_concat set_append_contra1)
  apply(rename_tac aa w x)(*strict*)
  apply(clarsimp)
  apply (metis concat_conv_foldl foldl_conv_concat set_append2 subsetE)
  done

lemma nth_drop_elem: "
  i < length \<alpha> - n
  \<Longrightarrow> \<alpha> ! (n + i)  \<in> set (drop n \<alpha>)"
  apply(induct \<alpha> arbitrary: i n)
   apply(rename_tac i n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<alpha> i n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a \<alpha> i n)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<alpha> i)(*strict*)
   apply(case_tac i)
    apply(rename_tac a \<alpha> i)(*strict*)
    apply(clarsimp)
   apply(rename_tac a \<alpha> i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<alpha> i n nat)(*strict*)
  apply(clarsimp)
  done

lemma take_drop_rev1: "
  take n (rev w) = rev (drop (length w - n) w)"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(case_tac "n-length w")
   apply(rename_tac a w n)(*strict*)
   apply(clarsimp)
   apply(case_tac "length w-n")
    apply(rename_tac a w n)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w n nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Suc (length w) - n"
      and s="Suc (Suc nat)"
      in ssubst)
    apply(rename_tac a w n nat)(*strict*)
    apply(force)
   apply(rename_tac a w n nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n nat)(*strict*)
  apply(clarsimp)
  done

lemma take_drop_rev2: "
  drop n w = rev (take (length w - n) (rev w))"
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

lemma take_drop_rev3: "
  take n w = rev (drop (length w - n) (rev w))"
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

lemma rev_inj2: "
  rev a=rev b
  \<Longrightarrow> a=b"
  apply (metis rev_rev_ident)
  done

lemma nth_rev: "
  i<length w
  \<Longrightarrow> w!i = (rev w)!(length w - (Suc i))"
  apply(induct w arbitrary: i rule: rev_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=length xs")
   apply(rename_tac x xs i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i)(*strict*)
  apply(rule_tac
      t="(xs@[x])!i"
      and s="xs!i"
      in ssubst)
   apply(rename_tac x xs i)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  done

lemma foldl_drop_head: "
  foldl (@) [] (a#w) = a@(foldl (@) [] w)"
  apply(rule_tac
      t="foldl (@) [] (a#w)"
      and s="foldl (@) [] ([a]@w)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] ([a] @ w)"
      and s=" (foldl (@) [] ([a])) @ (foldl (@) [] w) "
      in ssubst)
   apply (metis ConsApp append_Nil foldl_Cons foldl_Nil foldl_conv_concat)
  apply(force)
  done

lemma take_append1: "
  length w = n
  \<Longrightarrow> take n (w@v) = w"
  apply(force)
  done

lemma take_n_vs_take_Suc_n: "
  n<length w
  \<Longrightarrow> x=n
  \<Longrightarrow> x'=n
  \<Longrightarrow> y=Suc n
  \<Longrightarrow> (take x w) @ [w!x'] = take y w"
  apply(clarsimp)
  apply(rule_tac
      t="take (Suc n) w"
      and s="take (Suc n) ((take n w)@(w!n)#(drop(Suc n)w))"
      in ssubst)
   apply (metis append_take_drop_id_hlp Cons_nth_drop_Suc)
  apply(rule_tac
      t="take (Suc n) (take n w @ w ! n # drop (Suc n) w)"
      and s="take (Suc n) ((take n w @ [w ! n]) @ drop (Suc n) w)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="take (Suc n) ((take n w @ [w ! n]) @ drop (Suc n) w)"
      and s="take n w @ [w ! n]"
      in ssubst)
   apply(rule take_append1)
   apply(force)
  apply(force)
  done

lemma foldr_tail: "
  foldr (@) xs [] @ x = foldr (@) xs x"
  apply(induct xs arbitrary: x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac a xs x)(*strict*)
  apply(clarsimp)
  done

lemma foldl_head1: "
  \<pi>s=a#w
  \<Longrightarrow> \<pi>s ! 0 @ foldl (@) [] (drop (Suc 0) \<pi>s) = foldl (@) [] \<pi>s"
  apply (metis append_Nil drop_0 drop_Suc_Cons foldl_Nil foldl_decomp length_greater_0_conv list.simps(3) nth_Cons_0 take_0)
  done

lemma foldl_head2: "
  \<pi>s=a#w
  \<Longrightarrow> \<pi>s ! 0 @ foldl (@) [] (tl \<pi>s) = foldl (@) [] \<pi>s"
  apply(metis drop_0 drop_Suc_Cons foldl_head1 nth_first list.sel)
  done

lemma take_nth_split: "
  k<length v
  \<Longrightarrow> take k v @ [v ! k] = take (Suc k) v"
  apply (metis take_Suc_conv_app_nth)
  done

lemma foldl_tail: "
  k<length ws
  \<Longrightarrow> foldl (@) [] (take k ws) @ ws ! k = foldl (@) [] (take (Suc k) ws)"
  apply(induct ws rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(case_tac "k=length xs")
   apply(rename_tac x xs)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) [] (take (Suc k) xs)"
      and s="foldl (@) [] (take k xs) @ xs ! k"
      in ssubst)
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply (metis less_SucE nth_append_1)
  done

lemma foldl_pullout: "
  foldl (@) [] ([A]@w) = A@(foldl (@) [] w)"
  apply (metis ConsApp concat.simps(2) concat_conv_foldl foldl_conv_concat insert_Nil)
  done

lemma length_foldl_rev: "
  length (foldl (@) [] x) = length (foldl (@) [] (rev x))"
  apply(induct x rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply (metis concat_conv_foldl foldl_conv_concat length_append add.commute)
  done

lemma length_foldl_map: "
  (\<And>a. a \<in> set w \<Longrightarrow> length a = length (f a))
  \<Longrightarrow> length (foldl (@) [] (map f w)) = length (foldl (@) [] w)"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  done

lemma take_equal: "
  w = v
  \<Longrightarrow> x=take k w
  \<Longrightarrow> y=take k v
  \<Longrightarrow> x=y"
  apply(force)
  done

lemma nth_append_2_prime_XX: "
   ((w' @ [x', stack_seqA, []]) ! Suc (Suc (length w'))) =
  []"
  apply(rule_tac
      t="(w' @ [x', stack_seqA, []]) ! Suc (Suc (length w'))"
      and s="([x', stack_seqA, []]) ! (Suc (Suc (length w'))-(length w'))"
      in ssubst)
   apply (metis le_Suc_eq lessI nat_less_le nth_append_2)
  apply(clarsimp)
  done

lemma last_nth2: "
  length w = Suc n
  \<Longrightarrow> x=w @v
  \<Longrightarrow> x ! n = last w"
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w=w'@[x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule_tac NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(clarsimp)
  done

lemma length_2_seq_but_empty: "
  length x = Suc (Suc 0)
  \<Longrightarrow> foldl (@) [] x = []
  \<Longrightarrow> x = [[], []]"
  apply (metis append_take_drop_id_hlp1 drop_prefix_closureise foldl_empty2 lessI Cons_nth_drop_Suc self_append_conv zero_less_Suc)
  done

lemma nth_beyond1: "
  length w=n
  \<Longrightarrow> (w@[a])!n = a"
  apply(rule_tac
      t="(w@[a])!n"
      and s="([a])!(n-length w)"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma nth_beyond2: "
  Suc(length w)=n
  \<Longrightarrow> (w@[a,b])!n = b"
  apply(rule_tac
      t="(w@[a,b])!n"
      and s="([a,b])!(n-length w)"
      in ssubst)
   apply(rule nth_append_2)
   apply(force)
  apply(force)
  done

lemma equal_append: "
  a=c
  \<Longrightarrow> b=d
  \<Longrightarrow> a@b=c@d"
  apply(force)
  done

lemma nth_append_beyond: "
  n=length w
  \<Longrightarrow> (w@[x])!n=x"
  apply(force)
  done

lemma take_nth_drop_decomp: "
  i<length f\<pi>
  \<Longrightarrow> f\<pi> = take i f\<pi> @ [f\<pi> ! i] @ drop (Suc i) f\<pi>"
  apply (metis ConsApp id_take_nth_drop)
  done

lemma foldl_first: "
  foldl (@) A X = A @ foldl (@) [] X"
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma length_foldl: "
  length (foldl (@) A X) = length A + (length (foldl (@) [] X))"
  apply (metis concat_conv_foldl foldl_conv_concat length_append)
  done

lemma rev_last: "
  rev (w@[a]) = [a]@(rev w)"
  apply(force)
  done

lemma foldl_append_distrib: "
  (foldl (@) [] w) @ (foldl (@) [] v) = foldl (@) [] (w@v)"
  apply (metis foldl_append foldl_first)
  done

lemma empty_and_nonempty_contra: "
  w=[]
  \<Longrightarrow> length w = Suc n
  \<Longrightarrow> P"
  apply(force)
  done

lemma take_nth_drop_X: "
  n<length w
  \<Longrightarrow> w = take n w @ [w ! n] @ drop (Suc n) w"
  apply (metis ConsApp id_take_nth_drop)
  done

lemma case_list: "
  w=[] \<or> (\<exists>w' a'. w=w'@[a'])"
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w=w'@[x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(force)
  done

lemma length_foldl_append: "
  length (foldl (@) [] (w@v))=length (foldl (@) [] w)+length (foldl (@) [] v)"
  apply (metis foldl_append foldl_first length_append)
  done

lemma length_foldl_map_append: "
  length (foldl (@) [] (map f (w@v)))=length (foldl (@) [] (map f w))+length (foldl (@) [] (map f v))"
  apply(rule_tac
      t="map f (w@v)"
      and s="(map f w)@(map f v)"
      in ssubst)
   apply(rule map_append)
  apply(rule length_foldl_append)
  done

lemma foldl_set_elem: "
  x  \<in> set (foldl (@) [] w)
  \<Longrightarrow> \<exists>y \<in> set w. x \<in> set y"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "foldl (@) a w=a@foldl (@) [] w")
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(rule foldl_first)
  done

lemma hlp1_renamed: "
  w@[a]@x = v@[b]@y
  \<Longrightarrow> w=v
  \<Longrightarrow> a=b"
  apply(force)
  done

lemma foldl_take_nth_drop: "
  n<length w
  \<Longrightarrow> foldl (@) [] (take n w)
  @ foldl (@) [] ([w!n])
  @ foldl (@) [] ((drop (Suc n) w))
  = foldl (@) [] w"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w n)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w)(*strict*)
   apply (metis foldl_first)
  apply(rename_tac a w n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply (metis append_take_drop_id foldl_append foldl_drop_head foldl_first Cons_nth_drop_Suc)
  done

lemma foldl_take_nth_drop_map: "
  n<length w
  \<Longrightarrow> foldl (@) [] (map f (take n w))
  @ foldl (@) [] (map f [w!n])
  @ foldl (@) [] (map f (drop (Suc n) w))
  = foldl (@) [] (map f w)"
  apply(rule_tac
      t="map f (take n w)"
      and s="(take n (map f w))"
      in subst)
   apply(rule take_map)
  apply(rule_tac
      t="map f [w!n]"
      and s="[(map f w)!n]"
      in subst)
   apply(force)
  apply(rule_tac
      t="map f (drop (Suc n) w)"
      and s="(drop (Suc n) (map f w))"
      in subst)
   apply(rule drop_map)
  apply(rule foldl_take_nth_drop)
  apply(force)
  done

lemma Some_map_inj: "
  map Some w=map Some v
  \<Longrightarrow> w=v"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  done

lemma map_the_Some: "
  map the (map Some w) = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma nth_drop2: "
  n<length w
  \<Longrightarrow> (drop n w) = (w ! n) # (drop (Suc n) w)"
  apply (metis Cons_nth_drop_Suc)
  done

lemma set_trans_foldl: "
  x  \<in> set y
  \<Longrightarrow> y  \<in> set z
  \<Longrightarrow> x  \<in> set (foldl (@) [] z)"
  apply(induct z)
   apply(clarsimp)
  apply(rename_tac a z)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a z)(*strict*)
   apply(clarsimp)
   apply(rename_tac z)(*strict*)
   apply (metis foldl_first set_append_contra1)
  apply(rename_tac a z)(*strict*)
  apply(clarsimp)
  apply (metis foldl_first set_append_contra2)
  done

lemma set_trans_foldl_rev: "
  x  \<in> set (foldl (@) [] z)
  \<Longrightarrow> \<exists>y. x  \<in> set y \<and> y  \<in> set z"
  apply(induct z)
   apply(clarsimp)
  apply(rename_tac a z)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "foldl (@) a z = a@foldl (@) [] z")
   apply(rename_tac a z)(*strict*)
   prefer 2
   apply(rule foldl_first)
  apply(rename_tac a z)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a z)(*strict*)
   apply(force)
  apply(rename_tac a z)(*strict*)
  apply(force)
  done

lemma foldl_set_subset: "
  set w \<subseteq> set v
  \<Longrightarrow> set(foldl (@) [] w) \<subseteq> set(foldl (@) [] v)"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w v)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w v x)(*strict*)
  apply(subgoal_tac "\<exists>i<length v. v ! i = a")
   apply(rename_tac a w v x)(*strict*)
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(rename_tac a w v x)(*strict*)
  apply(clarsimp)
  apply(rename_tac w v x i)(*strict*)
  apply(subgoal_tac "foldl (@) (v ! i) w = (v ! i)@foldl (@) [] w")
   apply(rename_tac w v x i)(*strict*)
   prefer 2
   apply(rule foldl_first)
  apply(rename_tac w v x i)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac w v x i)(*strict*)
   apply(rule set_trans_foldl)
    apply(rename_tac w v x i)(*strict*)
    apply(force)
   apply(rename_tac w v x i)(*strict*)
   apply(force)
  apply(rename_tac w v x i)(*strict*)
  apply(subgoal_tac "\<exists>y. x  \<in> set y \<and> y  \<in> set w")
   apply(rename_tac w v x i)(*strict*)
   prefer 2
   apply(rule set_trans_foldl_rev)
   apply(force)
  apply(rename_tac w v x i)(*strict*)
  apply(clarsimp)
  apply(rename_tac w v x i y)(*strict*)
  apply(rule_tac
      A="set (foldl (@) [] w)"
      in set_mp)
   apply(rename_tac w v x i y)(*strict*)
   apply(erule_tac
      x="v"
      in meta_allE)
   apply(force)
  apply(rename_tac w v x i y)(*strict*)
  apply(rule_tac
      y="y"
      in set_trans_foldl)
   apply(rename_tac w v x i y)(*strict*)
   apply(force)
  apply(rename_tac w v x i y)(*strict*)
  apply(force)
  done

lemma butlast_snoc_prime: "
  w=v@[a]
  \<Longrightarrow> butlast w = v"
  apply(force)
  done

lemma left_most_occurence: "
  X  \<in> set w
  \<Longrightarrow> \<exists>w1 w2. w=w1@[X]@w2 \<and> X \<notin> set w1"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(case_tac "a=X")
   apply(rename_tac a w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w1 w2)(*strict*)
  apply(rule_tac
      x="a#w1"
      in exI)
  apply(clarsimp)
  done

lemma right_most_occurence: "
  X  \<in> set w
  \<Longrightarrow> \<exists>w1 w2. w=w1@[X]@w2 \<and> X \<notin> set w2"
  apply(induct w rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x xs)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs)(*strict*)
   apply(rule_tac
      x="xs"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac x w1 w2)(*strict*)
  apply(case_tac "x=X")
   apply(rename_tac x w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2)(*strict*)
   apply(rule_tac
      x="w1 @ X # w2"
      in exI)
   apply(clarsimp)
  apply(rename_tac x w1 w2)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(clarsimp)
  done

lemma filter_nonempty_in_set: "
  filter (\<lambda>x. x=X) w \<noteq> []
  \<Longrightarrow> X  \<in> set w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(case_tac "a=X")
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma butlast_nth: "
  Suc i<length w
  \<Longrightarrow> (butlast w)!i = w!i"
  apply(induct w arbitrary: i rule: rev_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs i)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule nth_append_1)
  apply(force)
  done

lemma not_equal_by_non_common_teA: "
  w=v
  \<Longrightarrow> A  \<in> set w
  \<Longrightarrow> A \<notin> set v
  \<Longrightarrow> Q"
  apply(force)
  done

lemma ex_swap: "
  \<exists>A B. P A B
  \<Longrightarrow> \<exists>B A. P A B"
  apply(force)
  done

lemma map_decomp_base: "
  map f w = w1@w2
  \<Longrightarrow> \<exists>w1' w2'. w=w1'@w2' \<and> map f w1'=w1 \<and> map f w2' = w2"
  apply(rule_tac
      x="take (length w1) w"
      in exI)
  apply(rule_tac
      x="drop (length w1) w"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply (metis takePrecise take_map)
  apply (metis drop_map drop_prefix_closureise)
  done

lemma map_decomp_three: "
  map f w = w1@w2@ w3
  \<Longrightarrow> \<exists>w1' w2' w3'. w=w1'@w2'@w3' \<and> map f w1'=w1 \<and> map f w2' = w2 \<and> map f w3' = w3"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?w2.0="w2@w3"
      in map_decomp_base)
   apply(force)
  apply(clarsimp)
  apply(rename_tac w1' w2')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac w1' w2')(*strict*)
   prefer 2
   apply(rule_tac
      ?w2.0="w3"
      in map_decomp_base)
   apply(force)
  apply(rename_tac w1' w2')(*strict*)
  apply(clarsimp)
  apply(rename_tac w1' w1'a w2'a)(*strict*)
  apply(force)
  done

lemma match_with_border: "
  w @ [D,S,D] @ v = [D] @ x @ [D]
  \<Longrightarrow> D \<notin> set x
  \<Longrightarrow> w=[] \<and> v=[]"
  apply(case_tac w)
   prefer 2
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac list)(*strict*)
   apply(rule_tac
      xs="v"
      in rev_cases)
    apply(rename_tac list)(*strict*)
    apply(clarsimp)
   apply(rename_tac list ys y)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      xs="v"
      in rev_cases)
   apply(clarsimp)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  done

lemma card_Pow_SucSuc: "
finite A \<Longrightarrow> card (Pow A) = Suc (Suc 0) ^ card A"
  apply(rule_tac
      t="Suc(Suc 0)"
      and s="2"
      in ssubst)
   apply(force)
  apply(rule card_Pow)
  apply(force)
  done

lemma word_decompose: "
length w1 = length v + Suc 0 + length w2
    \<Longrightarrow> take (length v) w1 @
       hd (drop (length v) w1) # drop (Suc (length v)) w1 =
       w1 \<and>
       length (drop (Suc (length v)) w1) = length w2"
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
   apply (metis less_add_Suc2 less_not_refl linorder_neqE_nat min_less_iff_conj min_less_iff_disj add.commute not_less_iff_gr_or_eq)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i<length v")
   apply(rename_tac i)(*strict*)
   apply (metis hd_drop_conv_nth less_iff_Suc_add list_update_id upd_conv_take_nth_drop)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i<Suc(length v)")
   apply(rename_tac i)(*strict*)
   apply (metis append_take_drop_id Cons_nth_drop_Suc less_Suc_eq list.sel(1) nat_neq_iff not_add_less1)
  apply(rename_tac i)(*strict*)
  apply (metis hd_drop_conv_nth less_iff_Suc_add list_update_id upd_conv_take_nth_drop)
  done

lemma union_pair_wise_equal: "
  A=A'
  \<Longrightarrow> B=B'
  \<Longrightarrow> A\<union>B = A'\<union>B'"
  apply(force)
  done

lemma no_shift_shift_conflicts1_hlp1: "
  ca @ y @ Do # w' @ [x'] = take (k - Suc 0) w'a @ take (k - Suc (length w'a)) [Do]
  \<Longrightarrow> Do  \<in> set w'a"
  apply(case_tac "(k - Suc (length w'a))")
   apply(clarsimp)
   apply(rule_tac
      t="w'a"
      and s="take (k-Suc 0) w'a @ (drop (k-Suc 0) w'a)"
      in subst)
    apply(rule append_take_drop_id)
   apply(rule_tac
      A="set (take (k - Suc 0) w'a)"
      in set_mp)
    apply (metis append_take_drop_id_hlp List.set_take_subset)
   apply (metis head_in_set set_append_contra2)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma last_in_set_X: "
  w \<noteq> []
  \<Longrightarrow> set w \<subseteq> A
  \<Longrightarrow> last w  \<in> A"
  apply(force)
  done

lemma map_list_set: "
  f ` (set w) = set (map f w)"
  apply(force)
  done

lemma distinct_by_last: "
  w=v
  \<Longrightarrow> length w > 0
  \<Longrightarrow> last w \<noteq> last v
  \<Longrightarrow> P"
  apply(force)
  done

lemma map_idI_prime: "
  \<forall>i \<in> set w. f i=i
  \<Longrightarrow> map f w = w"
  apply (metis map_idI)
  done

lemma length_shorter_1: "
  length w \<le> Suc 0
  \<Longrightarrow> w = a # v
  \<Longrightarrow> v = []"
  apply(force)
  done

lemma Max_Sat: "
  {length x| x. P x}\<noteq>{}
  \<Longrightarrow> finite {length x| x. P x}
  \<Longrightarrow> \<exists>x. P x \<and> length x = Max {length x| x. P x}"
  apply(subgoal_tac "Max {length x| x. P x}  \<in> {length x| x. P x}")
   prefer 2
   apply(rule Max_in)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(force)
  done

lemma finite_cart_image1: "
  finite A
  \<Longrightarrow> X\<subseteq>f`A
  \<Longrightarrow> finite X"
  apply(rule finite_surj)
   apply(force)
  apply(force)
  done

lemma finite_cart_image2: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> X\<subseteq>f`(A\<times>B)
  \<Longrightarrow> finite X"
  apply (metis finite_cartesian_product finite_surj)
  done

lemma finite_cart_image3: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> finite C
  \<Longrightarrow> X\<subseteq>f`(A\<times>B\<times>C)
  \<Longrightarrow> finite X"
  apply (metis finite_cartesian_product finite_surj)
  done

lemma finite_image_subset1: "
  finite A
  \<Longrightarrow> (\<And>x. finite (f x))
  \<Longrightarrow> X={x. \<exists>y \<in> A. x \<in> f y}
  \<Longrightarrow> finite X"
  apply(force)
  done

lemma finite_image_subset2: "
  finite A
  \<Longrightarrow> finite B
  \<Longrightarrow> (\<And>x y. finite (f x y))
  \<Longrightarrow> X\<subseteq>{x. \<exists>y1 \<in> A. \<exists>y2 \<in> B. x \<in> f y1 y2}
  \<Longrightarrow> finite X"
  apply(rule_tac
      B="{x. \<exists>y1 \<in> A. \<exists>y2 \<in> B. x \<in> f y1 y2}"
      in finite_subset)
   apply(force)
  apply(force)
  done

lemma finite_by_one: "
  (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a=b)
  \<Longrightarrow> finite A"
  apply(case_tac "A={}")
   apply(force)
  apply(subgoal_tac "\<exists>x. A={x}")
   prefer 2
   apply(force)
  apply(force)
  done

lemma elem_not_empty: "
  x \<in> A
  \<Longrightarrow> A\<noteq>{}"
  apply(force)
  done

lemma F_DPDARMPE__help1: "
  Suc n < length(w @ caa)
  \<Longrightarrow> drop n w @
      drop (n - length w) caa @
      drop (n - (length w + length caa)) ca =
      (w @ caa) ! n #
      drop (Suc n) w @
      drop (Suc n - length w) caa @
      drop (Suc n - (length w + length caa)) ca"
  apply(subgoal_tac "\<exists>m. Suc n+Suc m=length(w@caa)")
   prefer 2
   apply (metis add_Suc_right add_Suc_shift less_imp_Suc_add)
  apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply (metis List.drop_append add_leE Cons_nth_drop_Suc le_SucI length_append less_Suc_eq_le order_refl)
  done

lemma inj_on_preserves_inifinteness: "
  inj_on f B
  \<Longrightarrow> \<not> finite B
  \<Longrightarrow> f ` B \<subseteq> A
  \<Longrightarrow> \<not> finite A"
  apply (metis finite_imageD rev_finite_subset)
  done

lemma not_finite_nat_UNIV: "
  \<not> finite {x. (n::nat) \<le> x}"
  apply (metis add_leE finite_nat_set_iff_bounded_le infinite_Ioi mem_Collect_eq order_refl)
  done

lemma Option_Case_none: "
  (case X of None \<Rightarrow> None | Some X' \<Rightarrow> Some (F X')) = Some Y
  \<Longrightarrow> X=None
  \<Longrightarrow> Q"
  apply(force)
  done

lemma Option_Case_Some: "
  (case X of None \<Rightarrow> None | Some X' \<Rightarrow> Some (F X')) = Some Y
  \<Longrightarrow> X=Some X'
  \<Longrightarrow> F X'=Y"
  apply(force)
  done

lemma Option_Case: "
  (case X of None \<Rightarrow> None | Some X' \<Rightarrow> Some (F X')) = Some Y
  \<Longrightarrow> \<exists>X'. X=Some X' \<and> F X'=Y"
  apply(case_tac X)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(force)
  done

lemma decompose_simp: "
  I1 G
  \<Longrightarrow> O2 a (F a)
  \<Longrightarrow> O3 G (Some a)
  \<Longrightarrow> (\<And>a G F. I1 G \<Longrightarrow> O2 a (F a) \<Longrightarrow> O3 G (Some a) \<Longrightarrow> O1 G ((Some (F a))))
  \<Longrightarrow> Y=(Some (F a))
  \<Longrightarrow> O1 G Y"
  apply(force)
  done

lemma if_simp1: "
  if A then B else C
  \<Longrightarrow> A
  \<Longrightarrow> B"
  apply(force)
  done

lemma if_simp2: "
  if A then B else C
  \<Longrightarrow> \<not> A
  \<Longrightarrow> C"
  apply(force)
  done

lemma if_intro1: "
  A
  \<Longrightarrow> B
  \<Longrightarrow> if A then B else C"
  apply(force)
  done

lemma if_intro2: "
  \<not> A
  \<Longrightarrow> C
  \<Longrightarrow> if A then B else C"
  apply(force)
  done

lemma set_distinction_exists: "
  X \<noteq> Y
  \<Longrightarrow> \<exists>x. (x  \<in> X \<and> x \<notin> Y) \<or> (x  \<in> Y \<and> x \<notin> X)"
  apply(force)
  done

lemma empty_by_in_empty_set: "
  B = {}
  \<Longrightarrow> A \<subseteq> B
  \<Longrightarrow> A = {}"
  apply(force)
  done

lemma empty_by_eq_to_empty_set: "
  B = {}
  \<Longrightarrow> A = B
  \<Longrightarrow> A = {}"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification_args: "
  SEL_iF Y = ZFi
  \<Longrightarrow> SEL_iH Y = ZHi
  \<Longrightarrow> SEL_iFH Y = ZFHi
  \<Longrightarrow> SEL_oF Y = ZFo
  \<Longrightarrow> SEL_oH Y = ZHo
  \<Longrightarrow> SEL_oFH Y = ZFHo
  \<Longrightarrow> SPi_F X ZFi
  \<Longrightarrow> (SPi_F X ZFi \<Longrightarrow> SPi_H X ZHi)
  \<Longrightarrow> (SPi_H X ZHi \<Longrightarrow> SPo_H X ZHo (H X ZHi))
  \<Longrightarrow> (SPo_H X ZHo (H X ZHi) \<Longrightarrow> SPi_FH (H X ZHi) ZFHi)
  \<Longrightarrow> (\<And>P. SPo_H X ZHo (H X ZHi) \<Longrightarrow> SPo_FH (H X ZHi) ZFHo (P (H X ZHi)) \<Longrightarrow> SPo_F X ZFo (P (H X ZHi)))
  \<Longrightarrow> (\<And>X. SPi_FH X ZFHi \<Longrightarrow> SPo_FH X ZFHo (G X))
  \<Longrightarrow> SPo_F X ZFo (G (H X ZHi))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification_args2: "
  SEL_aH Y = ZHa
  \<Longrightarrow> SEL_iF Y = ZFi
  \<Longrightarrow> SEL_iH Y = ZHi
  \<Longrightarrow> SEL_iFH Y = ZFHi
  \<Longrightarrow> SEL_oF Y = ZFo
  \<Longrightarrow> SEL_oH Y = ZHo
  \<Longrightarrow> SEL_oFH Y = ZFHo
  \<Longrightarrow> SPi_F X ZFi
  \<Longrightarrow> (SPi_F X ZFi \<Longrightarrow> SPi_H X ZHi)
  \<Longrightarrow> (SPi_H X ZHi \<Longrightarrow> SPo_H X ZHo (H X ZHa))
  \<Longrightarrow> (SPo_H X ZHo (H X ZHa) \<Longrightarrow> SPi_FH (H X ZHa) ZFHi)
  \<Longrightarrow> (\<And>P. SPo_H X ZHo (H X ZHa) \<Longrightarrow> SPo_FH (H X ZHa) ZFHo (P (H X ZHa)) \<Longrightarrow> SPo_F X ZFo (P (H X ZHa)))
  \<Longrightarrow> (\<And>X. SPi_FH X ZFHi \<Longrightarrow> SPo_FH X ZFHo (G X))
  \<Longrightarrow> SPo_F X ZFo (G (H X ZHa))"
  apply(force)
  done

theorem decompose_sequential_execution_input_output_specification_args2_noHargs: "
  SEL_iF Y = ZFi
  \<Longrightarrow> SEL_iH Y = ZHi
  \<Longrightarrow> SEL_iFH Y = ZFHi
  \<Longrightarrow> SEL_oF Y = ZFo
  \<Longrightarrow> SEL_oH Y = ZHo
  \<Longrightarrow> SEL_oFH Y = ZFHo
  \<Longrightarrow> SPi_F X ZFi
  \<Longrightarrow> (SPi_F X ZFi \<Longrightarrow> SPi_H X ZHi)
  \<Longrightarrow> (SPi_H X ZHi \<Longrightarrow> SPo_H X ZHo (H X))
  \<Longrightarrow> (SPo_H X ZHo (H X) \<Longrightarrow> SPi_FH (H X) ZFHi)
  \<Longrightarrow> (\<And>P. SPo_H X ZHo (H X) \<Longrightarrow> SPo_FH (H X) ZFHo (P (H X)) \<Longrightarrow> SPo_F X ZFo (P (H X)))
  \<Longrightarrow> (\<And>X. SPi_FH X ZFHi \<Longrightarrow> SPo_FH X ZFHo (G X))
  \<Longrightarrow> SPo_F X ZFo (G (H X))"
  apply(force)
  done

lemma is_empty: "
  (\<And>x. x  \<in> A \<Longrightarrow> False)
  \<Longrightarrow> A = {}"
  apply(force)
  done

lemma take_0: "
  n=0
  \<Longrightarrow> take n w = []"
  apply(force)
  done

lemma take_1: "
  n=Suc m
  \<Longrightarrow> take n [a] = [a]"
  apply(force)
  done

lemma empty_foldl_ignore: "
  na < length \<pi>s
  \<Longrightarrow> (foldl (@) [] (take na \<pi>s) = [])
  \<Longrightarrow> foldl (@) [] (take na \<pi>s @ [e2 # \<pi>s ! na] @ drop (Suc na) \<pi>s) = e2 # foldl (@) [] \<pi>s"
  apply(induct \<pi>s arbitrary: na e2 rule: rev_induct)
   apply(rename_tac na e2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs na e2)(*strict*)
  apply(clarsimp)
  apply(case_tac "na=length xs")
   apply(rename_tac x xs na e2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs na e2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="na"
      in meta_allE)
  apply(clarsimp)
  apply(rule_tac
      t="(xs @ [x]) ! na"
      and s="xs!na"
      in ssubst)
   apply(rename_tac x xs na e2)(*strict*)
   apply (metis nth_append less_SucE)
  apply(rename_tac x xs na e2)(*strict*)
  apply(clarsimp)
  done

lemma take_all_length: "
  length w \<ge> m
  \<Longrightarrow> length (take m w) = m"
  apply(induct w)
   apply(auto)
  done

lemma select_from_drop: "
  i < length \<alpha> - Suc na
  \<Longrightarrow> (take na \<alpha> @ (lx @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! Suc (i + na) = \<alpha> ! Suc (i + na)"
  apply(rule_tac
      t="(take na \<alpha> @ (lx @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! Suc (i + na) "
      and s="((lx @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! (Suc (i + na)-(length(take na \<alpha>)))"
      in ssubst)
   apply(rule nth_append_2)
   apply(force)
  apply(rule_tac
      t="(lx @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>"
      and s=" [lx @ prod_rhs e2 @ r2] @ (drop (Suc na) \<alpha>)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="([lx @ prod_rhs e2 @ r2] @ drop (Suc na) \<alpha>) ! (Suc (i + na) - length (take na \<alpha>))"
      and s="(drop (Suc na) \<alpha>) ! ((Suc (i + na) - length (take na \<alpha>))-length([lx @ prod_rhs e2 @ r2]))"
      in ssubst)
   apply(rule nth_append_2)
   apply(force)
  apply(rule_tac
      t="length (take na \<alpha>)"
      and s="na"
      in ssubst)
   apply (metis gr_implies_not0 less_SucI nat_diff_split not_less take_all_length)
  apply(rule_tac
      t="length [lx @ prod_rhs e2 @ r2]"
      and s="Suc 0"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="(Suc (i + na) - na - Suc 0)"
      and s="i"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="Suc (i+na)"
      and s="Suc na + i"
      in ssubst)
   apply(force)
  apply (metis less_diff_conv add.commute nth_drop)
  done

lemma foldl_rev_take_drop: "
  na<length \<pi>s
  \<Longrightarrow> foldl (@) [] (drop (Suc na) \<pi>s) = []
  \<Longrightarrow> foldl (@) [] (rev (take na \<pi>s @ [e2 # \<pi>s ! na] @ drop (Suc na) \<pi>s)) = e2 # foldl (@) [] (rev \<pi>s)"
  apply(rule_tac
      t="rev (take na \<pi>s @ [e2 # \<pi>s ! na] @ drop (Suc na) \<pi>s)"
      and s=" (rev (drop (Suc na) \<pi>s)) @ ([e2 # \<pi>s ! na]) @ (rev (take na \<pi>s)) "
      in ssubst)
   apply(force)
  apply(rule_tac
      t="rev \<pi>s"
      and s="rev(take na \<pi>s @ [\<pi>s!na] @ (drop (Suc na) \<pi>s))"
      in ssubst)
   apply (metis Cons_eq_appendI append_Nil append_take_drop_id_hlp Cons_nth_drop_Suc)
  apply(rule_tac
      t="rev (take na \<pi>s @ [\<pi>s ! na] @ drop (Suc na) \<pi>s)"
      and s=" (rev (drop (Suc na) \<pi>s)) @ ([\<pi>s ! na]) @ (rev (take na \<pi>s)) "
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] (rev (drop (Suc na) \<pi>s) @ [e2 # \<pi>s ! na] @ rev (take na \<pi>s))"
      and s=" (foldl (@) [] (rev (drop (Suc na) \<pi>s))) @ (foldl (@) [] ([e2 # \<pi>s ! na] @ rev (take na \<pi>s))) "
      in ssubst)
   apply (metis foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] (rev (drop (Suc na) \<pi>s) @ [\<pi>s ! na] @ rev (take na \<pi>s))"
      and s=" (foldl (@) [] (rev (drop (Suc na) \<pi>s))) @ (foldl (@) [] ([\<pi>s ! na] @ rev (take na \<pi>s))) "
      in ssubst)
   apply (metis foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] (rev (drop (Suc na) \<pi>s))"
      and s="[]"
      in ssubst)
   apply(rule foldl_empty)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "\<exists>i<length ((drop (Suc na) \<pi>s)). ((drop (Suc na) \<pi>s))!i = a")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule_tac
      s="a  \<in> set((drop (Suc na) \<pi>s))"
      in subst)
     apply(rename_tac a)(*strict*)
     apply (rule in_set_conv_nth)
    apply(rename_tac a)(*strict*)
    apply (metis set_rev)
   apply(rename_tac a)(*strict*)
   apply(erule exE)+
   apply(rename_tac a i)(*strict*)
   apply(rule_tac
      t="a"
      and s="drop (Suc na) \<pi>s ! i"
      in ssubst)
    apply(rename_tac a i)(*strict*)
    apply(clarsimp)
   apply(rename_tac a i)(*strict*)
   apply(rule foldl_empty2)
    apply(rename_tac a i)(*strict*)
    apply(force)
   apply(rename_tac a i)(*strict*)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] ([e2 # \<pi>s ! na] @ rev (take na \<pi>s))"
      and s=" (foldl (@) [] ([e2 # \<pi>s ! na])) @(foldl (@) [] (rev (take na \<pi>s))) "
      in ssubst)
   apply (metis foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] [e2 # \<pi>s ! na]"
      and s="e2 # \<pi>s ! na"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="foldl (@) [] ([\<pi>s ! na] @ rev (take na \<pi>s))"
      and s=" (foldl (@) [] ([\<pi>s ! na])) @ (foldl (@) [] (rev (take na \<pi>s))) "
      in ssubst)
   apply (metis foldl_distrib_append)
  apply(rule_tac
      t="foldl (@) [] [\<pi>s ! na]"
      and s="\<pi>s ! na"
      in ssubst)
   apply(force)
  apply(clarsimp)
  done

end
