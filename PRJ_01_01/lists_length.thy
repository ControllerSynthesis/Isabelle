section {*lists\_length*}
theory
  lists_length

imports
  lists_set

begin

lemma drop_length_append: "
  length f \<le> length (f @ c)"
  apply(force)
  done

lemma length_diff: "
  k - length w>0
  \<Longrightarrow> length w \<le> k"
  apply(force)
  done

lemma length_shorter_append2: "
  w @ v = r
  \<Longrightarrow> length r \<le> length v
  \<Longrightarrow> w = []"
  apply(force)
  done

lemma foldl_emptyX: "
  (\<And>i. i < length w \<Longrightarrow> w!i = [])
  \<Longrightarrow> foldl (@) [] w = []"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "a = []")
   apply(rename_tac a w)(*strict*)
   prefer 2
   apply(erule_tac
      x = "0"
      in meta_allE)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "(\<And>i. i < length w \<Longrightarrow> w ! i = [])")
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w i)(*strict*)
  apply(erule_tac
      x = "Suc i"
      in meta_allE)
  apply(clarsimp)
  done

lemma border_right_by_length: "
  length w = length v
  \<Longrightarrow> a@w = b@v
  \<Longrightarrow> w = v"
  apply(rule_tac
      t = "w"
      and s = "drop(length a) (a@w)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t = "v"
      and s = "drop(length b) (b@v)"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma set_subset_drop: "
  length w = length v
  \<Longrightarrow> x@w = y@v
  \<Longrightarrow> set x \<subseteq> set y"
  apply (metis append_same_eq border_right_by_length set_eq_subset)
  done

lemma length_shorter_append: "
  f @ c = w @ [X]
  \<Longrightarrow> length f \<le> Suc (length w)"
  apply (metis drop_length_append length_append_singleton)
  done

lemma append_length_inc: "
  w1 = w2@r
  \<Longrightarrow> length w2 \<le> length w1"
  apply(force)
  done

lemma length_map_Some: "
  length w = length (map Some w)"
  apply(induct w)
   apply(auto)
  done

lemma length_Suc: "
  Suc (length w) = length (w @ [a])"
  apply(force)
  done

lemma NonEmptyListHasTailElem: "
  length w = Suc n
  \<Longrightarrow> \<exists>w' x'. w = w' @ [x']"
  apply(subgoal_tac "\<forall>w. length w = Suc n \<longrightarrow> (\<exists>w' x'. w = w' @ [x'])")
   apply(force)
  apply(thin_tac "length w = Suc n")
  apply(induct_tac n)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(case_tac w)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w)(*strict*)
  apply(case_tac w)
   apply(rename_tac n w)(*strict*)
   apply(auto)
  done

lemma lengthNonEmpty: "
  Suc 0 \<le> length ya
  \<Longrightarrow> ya \<noteq> []"
  apply(auto)
  done

lemma lengthNonEmpty2: "
  Suc 0 \<le> length ya
  \<Longrightarrow> (\<exists>y a. ya = y @ [a])"
  apply(rule_tac
      P = "Suc 0 \<le> length ya"
      and Q = "(\<exists>y a. ya = y @ [a])"
      in impE)
    apply(thin_tac "Suc 0 \<le> length ya")
    apply(induct_tac ya)
     apply(simp)
    apply(rename_tac a list)(*strict*)
    defer
    apply(auto)
  apply(rename_tac a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac a list)(*strict*)
   apply(auto)
  done

lemma lengthDec: "
  length (v @ [a]) - length [a] \<le> length v"
  apply(induct v)
   apply(auto)
  done

lemma lengthDec2: "
  length v + Suc 0 = length (v @ [a])"
  apply(induct v)
   apply(auto)
  done

lemma Suc_length: "
  length (y@[a]) = Suc (length y)"
  apply(clarsimp)
  done

lemma length2: "
  length [a,b] = Suc(Suc 0)"
  apply(auto)
  done

lemma NotNil_Length: "
  w \<noteq> []
  \<Longrightarrow> \<exists>n. length w = Suc n"
  apply(case_tac w)
   apply(auto)
  done

lemma lengthSmallerUnderDecomp: "
  a@b = c@d
  \<Longrightarrow>length c \<le> length a + length b"
  apply(rule_tac
      j = "length c + length d"
      in Nat.le_trans)
   apply(simp)
  apply(rule_tac
      s = "length (a@b)"
      in ssubst)
   apply(rule sym)
   apply(rule length_append)
  apply(rule_tac
      s = "length (c@d)"
      in ssubst)
   apply(simp)
  apply(subgoal_tac "length c + length d = length (c@d)")
   apply(simp)
  apply(rule sym)
  apply(rule length_append)
  done

end
