section {*compute\_least\_restrictive\_satisfactory\_contollers*}
theory
  compute_least_restrictive_satisfactory_contollers

imports
  composition_of_fixed_point_iterators
  compute_greatest_fixed_points

begin

lemma des_less_intro_by_um: "
  A \<le> B
  \<Longrightarrow> \<exists>w. w \<in> des_langUM B \<and> w \<notin> des_langUM A
  \<Longrightarrow> A < B"
  apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
  apply(case_tac A)
  apply(rename_tac set1 set2)(*strict*)
  apply(case_tac B)
  apply(rename_tac set1 set2 set1a set2a)(*strict*)
  apply(clarsimp)
  done

definition language_kleene_star :: "'a list set \<Rightarrow> 'a list set"
  where
    "language_kleene_star L = {foldl (@) [] ws| ws. set ws \<subseteq> L}"

definition language_kleene_star_finite :: "'a list set \<Rightarrow> nat \<Rightarrow> 'a list set"
  where
    "language_kleene_star_finite L n = {foldl (@) [] ws| ws. set ws \<subseteq> L \<and>length ws = n}"

primrec repeat :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "repeat w 0 = []"
  | "repeat w (Suc n) = w @ (repeat w n)"

lemma controllable_subset_contra: "
  w \<in> controllable_subset L1 \<Sigma>UC L2
  \<Longrightarrow> w \<in> L1
  \<Longrightarrow> u \<in> \<Sigma>UC
  \<Longrightarrow> w@[u]\<in> L2
  \<Longrightarrow> w @[u] \<notin> L1
  \<Longrightarrow> Q"
  apply(simp add: controllable_sublanguage_def controllable_subset_def controllable_word_def alphabet_to_language_def)
  apply(erule_tac
      x="w"
      in ballE)
   prefer 2
   apply(simp add: prefix_closure_def prefix_def)
  apply(force)
  done

lemma repeat_length: "
  length (repeat w n) = (length w) * n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma repeat_shorter_help: "
  a \<noteq> b
  \<Longrightarrow> repeat [a, b] n @ a # u # repeat [a, u] n @ b # c = repeat [a, b] k @ a # u # repeat [a, u] k @ [b]
  \<Longrightarrow> n\<le>k"
  apply(subgoal_tac "(length [a,b])*n+2+(length [a,u])*n+1\<le>(length [a,b])*k+2+(length [a,u])*k+1")
   apply(force)
  apply(rule_tac
      t="(length [a,b])*n"
      and s="length(repeat [a,b] n)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,b])*k"
      and s="length(repeat [a,b] k)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,u])*n"
      and s="length(repeat [a,u] n)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,u])*k"
      and s="length(repeat [a,u] k)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="length (repeat [a, b] n) + 2 + length (repeat [a, u] n) +1"
      and s="length (repeat [a, b] n @ a # u # repeat [a, u] n @[b])"
      in ssubst)
   apply(simp (no_asm))
  apply(rule_tac
      t="length (repeat [a, b] k) + 2 + length (repeat [a, u] k)+1"
      and s="length (repeat [a, b] k @ a # u # repeat [a, u] k @[b])"
      in ssubst)
   apply(simp (no_asm))
  apply(rule_tac
      t="repeat [a, b] k @ a # u # repeat [a, u] k @ [b]"
      and s="repeat [a, b] n @ a # u # repeat [a, u] n @ b # c"
      in ssubst)
   apply(force)
  apply(simp (no_asm))
  done

lemma repeat_equal_help: "
  a \<noteq> b
  \<Longrightarrow> repeat [a, b] n @ a # u # repeat [a, u] n @ [b] = repeat [a, b] k @ a # u # repeat [a, u] k @ [b]
  \<Longrightarrow> n=k"
  apply(subgoal_tac "(length [a,b])*n+2+(length [a,u])*n+1=(length [a,b])*k+2+(length [a,u])*k+1")
   apply(force)
  apply(rule_tac
      t="(length [a,b])*n"
      and s="length(repeat [a,b] n)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,b])*k"
      and s="length(repeat [a,b] k)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,u])*n"
      and s="length(repeat [a,u] n)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="(length [a,u])*k"
      and s="length(repeat [a,u] k)"
      in subst)
   apply(rule repeat_length)
  apply(rule_tac
      t="length (repeat [a, b] n) + 2 + length (repeat [a, u] n) +1"
      and s="length (repeat [a, b] n @ a # u # repeat [a, u] n @[b])"
      in ssubst)
   apply(simp (no_asm))
  apply(rule_tac
      t="length (repeat [a, b] k) + 2 + length (repeat [a, u] k)+1"
      and s="length (repeat [a, b] k @ a # u # repeat [a, u] k @[b])"
      in ssubst)
   apply(simp (no_asm))
  apply(rule_tac
      t="repeat [a, b] k @ a # u # repeat [a, u] k @ [b]"
      and s="repeat [a, b] n @ a # u # repeat [a, u] n @ [b]"
      in ssubst)
   apply(force)
  apply(simp (no_asm))
  done

lemma repeat_commute: "
  w @ (repeat w n) = repeat w n @ w"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma equal_continue: "
  w1 @ v1 @ s1
  = w2
  \<Longrightarrow> w1 @ v2 @ s2 = w2 @ t2
  \<Longrightarrow> length v1=length v2
  \<Longrightarrow> v1=v2"
  apply(clarsimp)
  done

lemma repeat_plus: "
  repeat w (n+m) = repeat w n @ repeat w m"
  apply(induct "n" arbitrary: m)
   apply(rename_tac m)(*strict*)
   apply(clarsimp)
  apply(rename_tac n m)(*strict*)
  apply(clarsimp)
  done

lemma repeat_equal_hlp1: "
  a \<noteq> b \<Longrightarrow> u\<noteq>b \<Longrightarrow>
          repeat [a, b] n @ a # u # repeat [a, u] n @ b # ys =
          repeat [a, b] k @ a # u # repeat [a, u] k \<Longrightarrow>
          n < k \<Longrightarrow> False"
  apply(subgoal_tac "prefix (repeat [a, b] n) (repeat [a, b] k) \<or> prefix (repeat [a, b] k) (repeat [a, b] n)")
   prefer 2
   apply (metis mutual_prefix_prefix)
  apply(subgoal_tac "length (repeat [a, b] n) = length [a,b] * n")
   prefer 2
   apply(rule repeat_length)
  apply(subgoal_tac "length (repeat [a, b] k) = length [a,b] * k")
   prefer 2
   apply(rule repeat_length)
  apply(erule disjE)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply (metis add_less_mono drop_length_append not_less)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "\<exists>x. n+Suc x=k")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply (metis less_delta_exists)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c x)(*strict*)
  apply(case_tac c)
   apply(rename_tac c x)(*strict*)
   apply(clarsimp)
  apply(rename_tac c x aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x aa list)(*strict*)
  apply(case_tac list)
   apply(rename_tac x aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x aa)(*strict*)
   apply(thin_tac "repeat [a, b] n @ a # u # repeat [a, u] n @ b # ys = a # b # repeat [a, b] (n + x) @ a # u # a # u # repeat [a, u] (n + x)")
   apply (simp add: repeat_plus)
  apply(rename_tac x aa list aaa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x aa aaa lista)(*strict*)
  apply(rename_tac x1 x2 xs)
  apply(rename_tac x x1 x2 xs)(*strict*)
  apply(subgoal_tac "[x1,x2] = [a,u]")
   apply(rename_tac x x1 x2 xs)(*strict*)
   prefer 2
   apply(rule_tac
      ?s1.0="xs"
      and ?w1.0="repeat [a, b] n"
      and ?w2.0="a # b # repeat [a, b] (n + x)"
      in equal_continue)
     apply(rename_tac x x1 x2 xs)(*strict*)
     apply(force)
    apply(rename_tac x x1 x2 xs)(*strict*)
    apply(force)
   apply(rename_tac x x1 x2 xs)(*strict*)
   apply(force)
  apply(rename_tac x x1 x2 xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(thin_tac "repeat [a, b] n @ a # u # repeat [a, u] n @ b # ys = a # b # repeat [a, b] (n + x) @ a # u # a # u # repeat [a, u] (n + x)")
  apply(thin_tac "length (repeat [a, b] (n + x)) = n + x + (n + x)")
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(rule_tac
      w="[a,b]"
      and n="n"
      and m="x"
      in repeat_plus)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(rule_tac
      w="[a,b]"
      and n="n"
      in repeat_commute)
  apply(rename_tac x xs)(*strict*)
  apply(subgoal_tac "repeat [a, b] n @ a # u # xs = repeat [a, b] n @ a # b # repeat [a, b] x")
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(rule_tac
      t="repeat [a, b] n @ a # u # xs"
      and s="a # b # repeat [a, b] n @ repeat [a, b] x"
      in ssubst)
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(simp (no_asm))
  apply(force)
  done

lemma repeat_equal_hlp2: "
  a \<noteq> b
  \<Longrightarrow> u \<noteq> b
  \<Longrightarrow>
       repeat [a, b] n @ a # u # repeat [a, u] n @ b # c =
       repeat [a, b] k @ a # u # repeat [a, u] k @ [b] \<Longrightarrow>
       k = n \<and> c = []"
  apply(subgoal_tac "n\<le>k")
   prefer 2
   apply(rule_tac
      k="k"
      and n="n"
      and u="u"
      and c="c"
      in repeat_shorter_help)
    apply(force)
   apply(force)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      k="k"
      and n="n"
      in repeat_equal_help)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys)(*strict*)
  apply(case_tac "n<k")
   apply(rename_tac ys)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ys)(*strict*)
  apply(rule_tac
      u="u"
      and a="a"
      and b="b"
      in repeat_equal_hlp1)
     apply(rename_tac ys)(*strict*)
     apply(force)
    apply(rename_tac ys)(*strict*)
    apply(force)
   apply(rename_tac ys)(*strict*)
   apply(force)
  apply(rename_tac ys)(*strict*)
  apply(force)
  done

lemma repeat_set: "
  set (repeat [a] n) \<subseteq> {a}"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma repeat_length2: "
  length (repeat [a] n) = n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma repeat_intro: "
  length w = n
  \<Longrightarrow> set w \<subseteq> {a}
  \<Longrightarrow> w = repeat [a] n"
  apply(induct n arbitrary: w)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n w)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac n w)(*strict*)
   apply(clarsimp)
  apply(rename_tac n w aa list)(*strict*)
  apply(force)
  done

lemma front_tail_set_one: "
  set w \<subseteq> {u}
  \<Longrightarrow> w @ [u] = u # w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

lemma equal_tail: "
  w1 @ [b] @ v1 = w2 @ [b] @ v2
  \<Longrightarrow> b \<notin> set v1
  \<Longrightarrow> b \<notin> set v2
  \<Longrightarrow> v1 = v2"
  apply(subgoal_tac "prefix w1 w2 \<or> X" for X)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c a list)(*strict*)
  apply(clarsimp)
  done

lemma equal_front: "
  w1 @ [b] @ v1 = w2 @ [b] @ v2
  \<Longrightarrow> b \<notin> set w1
  \<Longrightarrow> b \<notin> set w2
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "prefix w1 w2 \<or> X" for X)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(case_tac c)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c a list)(*strict*)
   apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(case_tac c)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c a list)(*strict*)
  apply(clarsimp)
  done

definition exampleR1 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set"
  where
    "exampleR1 n a b u =
  {an@[b]| an. set an \<subseteq> {a} \<and> length an = n}"

definition exampleR2 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set"
  where
    "exampleR2 n a b u =
  {an@[b]@un| an un. set an \<subseteq> {a} \<and> set un \<subseteq> {u} \<and> length an = length un+n}"

definition exampleR :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set"
  where
    "exampleR n a b u =
  exampleR1 n a b u
  \<union> exampleR2 n a b u"

definition exampleA :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set"
  where
    "exampleA n a b u =
  prefix_closure (append_language
  {an. set an \<subseteq> {a} \<and> length an = n}
  {an@[b]@un| an un. set an \<subseteq> {a} \<and> set un \<subseteq> {u} \<and> length an = length un})"

lemma exampleA_intro: "
  w @ c = repeat [a] n @ repeat [a] m @ [b] @ repeat [u] m
  \<Longrightarrow> w \<in> exampleA n a b u"
  apply(simp add: exampleA_def append_language_def prefix_closure_def prefix_def)
  apply(rule_tac
      x="w@c"
      in exI)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(rule_tac
      x="repeat [a] n"
      in exI)
  apply(rule conjI)
   apply(rule repeat_set)
  apply(rule conjI)
   apply(rule repeat_length2)
  apply(rule_tac
      x="repeat [a] m @ [b] @ repeat [u] m"
      in exI)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(rule_tac
      x="repeat [a] m"
      in exI)
  apply(rule_tac
      x="repeat [u] m"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule repeat_set)
  apply(rule conjI)
   apply(rule repeat_set)
  apply(simp add: repeat_length2)
  done

lemma exampleR1_in_exampleA: "
  exampleR1 n a b u \<subseteq> exampleA n a b u"
  apply(simp add: exampleR1_def append_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac an)(*strict*)
  apply(subgoal_tac "an = repeat [a] (length an)")
   apply(rename_tac an)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac an)(*strict*)
    apply(force)
   apply(rename_tac an)(*strict*)
   apply(force)
  apply(rename_tac an)(*strict*)
  apply(rule_tac
      c="[]"
      and m="0"
      in exampleA_intro)
  apply(clarsimp)
  done

lemma exampleR2_in_exampleA: "
  exampleR2 n a b u \<subseteq> exampleA n a b u"
  apply(simp add: exampleR2_def append_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac an un)(*strict*)
  apply(subgoal_tac "an = repeat [a] (length an)")
   apply(rename_tac an un)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac an un)(*strict*)
    apply(force)
   apply(rename_tac an un)(*strict*)
   apply(force)
  apply(rename_tac an un)(*strict*)
  apply(subgoal_tac "un = repeat [u] (length un)")
   apply(rename_tac an un)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac an un)(*strict*)
    apply(force)
   apply(rename_tac an un)(*strict*)
   apply(force)
  apply(rename_tac an un)(*strict*)
  apply(clarsimp)
  apply(rename_tac un)(*strict*)
  apply(rule_tac
      t="length un + n"
      and s="n+length un"
      in ssubst)
   apply(rename_tac un)(*strict*)
   apply(force)
  apply(rename_tac un)(*strict*)
  apply(simp add: repeat_plus)
  apply(rule_tac
      c="[]"
      and m="length un"
      in exampleA_intro)
  apply(clarsimp)
  done

lemma exampleR_in_exampleA: "
  exampleR n a b u \<subseteq> exampleA n a b u"
  apply(simp add: exampleR_def)
  apply(simp add: exampleR1_in_exampleA exampleR2_in_exampleA)
  done

lemma exampleR_removal_from_exampleA_part1a: "
  exampleA (Suc n) a b u \<subseteq> exampleA n a b u"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> prefix_closure (append_language {an. set an \<subseteq> {a} \<and> length an = Suc n} {an @ [b] @ un |an un. set an \<subseteq> {a} \<and> set un \<subseteq> {u} \<and> length an = length un})")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: exampleA_def)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> exampleA (Suc n) a b u")
  apply(simp add: append_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x aa c an un)(*strict*)
  apply(subgoal_tac "prefix x aa \<or> X" for X)
   apply(rename_tac x aa c an un)(*strict*)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x aa c an un)(*strict*)
  apply(erule disjE)
   apply(rename_tac x aa c an un)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x an un ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac x an un ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x an un)(*strict*)
    apply(rule_tac
      m="1"
      and c="[b,u]"
      in exampleA_intro)
    apply(clarsimp)
    apply (metis repeat.simps(2) repeat_commute repeat_intro)
   apply(rename_tac x an un ca aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x an un list)(*strict*)
   apply(subgoal_tac "x = repeat [a] (length x)")
    apply(rename_tac x an un list)(*strict*)
    prefer 2
    apply(rule repeat_intro)
     apply(rename_tac x an un list)(*strict*)
     apply(force)
    apply(rename_tac x an un list)(*strict*)
    apply(force)
   apply(rename_tac x an un list)(*strict*)
   apply(rule_tac
      m="0"
      and c="repeat [a] (length list)@[b]"
      in exampleA_intro)
   apply(clarsimp)
   apply(simp add: repeat_plus)
  apply(rename_tac x aa c an un)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac aa c an un ca)(*strict*)
  apply(rename_tac wa1 c wa2 wu1 ca)
  apply(rename_tac wa1 c wa2 wu1 ca)(*strict*)
  apply(rule_tac
      xs="wa1"
      in rev_cases)
   apply(rename_tac wa1 c wa2 wu1 ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa1 c wa2 wu1 ca ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac c wa2 wu1 ca ys)(*strict*)
  apply(rename_tac wa1)
  apply(rename_tac c wa2 wu1 ca wa1)(*strict*)
  apply(subgoal_tac "prefix ca wa2 \<or> X" for X)
   apply(rename_tac c wa2 wu1 ca wa1)(*strict*)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac c wa2 wu1 ca wa1)(*strict*)
  apply(erule disjE)
   apply(rename_tac c wa2 wu1 ca wa1)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac wu1 ca wa1 cb)(*strict*)
   apply(rename_tac wu1 wa1 wa2 wa3)
   apply(rename_tac wu1 wa1 wa2 wa3)(*strict*)
   apply(rule_tac
      m="Suc(length wa1)"
      and c="[b] @ repeat [u] (Suc (length wa1))"
      in exampleA_intro)
   apply(clarsimp)
   apply (metis repeat_intro)
  apply(rename_tac c wa2 wu1 ca wa1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c wa2 wu1 wa1 cb)(*strict*)
  apply(case_tac cb)
   apply(rename_tac c wa2 wu1 wa1 cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac wa2 wu1 wa1)(*strict*)
   apply(rule_tac
      m="Suc(length wa2)"
      and c="[b] @ repeat [u] (Suc (length wa2))"
      in exampleA_intro)
   apply(clarsimp)
   apply (metis repeat_intro)
  apply(rename_tac c wa2 wu1 wa1 cb aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c wa2 wa1 list)(*strict*)
  apply(rename_tac wu1 wa2 wa1 wu2)
  apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
  apply(rule_tac
      m="Suc(length wa2)"
      and c="wu1@[u]"
      in exampleA_intro)
  apply(simp add: repeat_plus)
  apply(subgoal_tac "wa1 = repeat [a] (length wa1)")
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
    apply(force)
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   apply(force)
  apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
  apply(subgoal_tac "wa2 = repeat [a] (length wa2)")
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
    apply(force)
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   apply(force)
  apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
  apply(subgoal_tac "wu1 = repeat [u] (length wu1)")
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
    apply(force)
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   apply(force)
  apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
  apply(subgoal_tac "wu2 = repeat [u] (length wu2)")
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
    apply(force)
   apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
   apply(force)
  apply(rename_tac wu1 wa2 wa1 wu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac wu1 wa1 wu2)(*strict*)
  apply(simp add: repeat_plus)
  apply(simp add: front_tail_set_one)
  done

lemma append_commute: "
  set (w@v) \<subseteq> {a}
  \<Longrightarrow> w@v=v@w"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa w v)(*strict*)
  apply(clarsimp)
  apply(rename_tac w v)(*strict*)
  apply (metis front_tail_set_one)
  done

lemma exampleR_removal_from_exampleA_part1: "
  a \<noteq> b
  \<Longrightarrow> exampleA (Suc n) a b u \<subseteq> exampleA n a b u - exampleR n a b u"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(rule set_mp)
    apply(rename_tac x)(*strict*)
    apply(rule exampleR_removal_from_exampleA_part1a)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: exampleR_def)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: exampleA_def exampleR1_def append_language_def prefix_def prefix_closure_def)
   apply(clarsimp)
   apply(rename_tac an aa c ana un)(*strict*)
   apply(rename_tac wa3 wa2 c wa1 wu1)
   apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
   apply(subgoal_tac "wa1 = repeat [a] (length wa1)")
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    prefer 2
    apply(rule repeat_intro)
     apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
     apply(force)
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    apply(force)
   apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
   apply(subgoal_tac "wa2 = repeat [a] (length wa2)")
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    prefer 2
    apply(rule repeat_intro)
     apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
     apply(force)
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    apply(force)
   apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
   apply(subgoal_tac "wu1 = repeat [u] (length wu1)")
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    prefer 2
    apply(rule repeat_intro)
     apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
     apply(force)
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    apply(force)
   apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
   apply(subgoal_tac "wa3 = repeat [a] (length wa3)")
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    prefer 2
    apply(rule repeat_intro)
     apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
     apply(force)
    apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
    apply(force)
   apply(rename_tac wa3 wa2 c wa1 wu1)(*strict*)
   apply(clarsimp)
   apply(rename_tac wa3 c wu1)(*strict*)
   apply(thin_tac "set (repeat [a] (length wu1)) \<subseteq> {a}")
   apply(thin_tac "set wu1 \<subseteq> {u}")
   apply(thin_tac "length (repeat [a] (length wu1)) = length wu1")
   apply(thin_tac "wu1 = repeat [u] (length wu1)")
   apply(thin_tac "wa3 = repeat [a] (length wa3)")
   apply (metis append_Cons append_assoc front_tail_set_one list.inject same_append_eq)
  apply(rename_tac x)(*strict*)
  apply(simp add: exampleA_def exampleR2_def append_language_def prefix_def prefix_closure_def)
  apply(clarsimp)
  apply(rename_tac an un aa c ana una)(*strict*)
  apply(rule_tac
      xs="aa"
      in rev_cases)
   apply(rename_tac an un aa c ana una)(*strict*)
   apply(clarsimp)
  apply(rename_tac an un aa c ana una ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac an un c ana una ys)(*strict*)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(subgoal_tac "wa1 = repeat [a] (length wa1)")
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   apply(force)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(subgoal_tac "wa2 = repeat [a] (length wa2)")
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   apply(force)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(subgoal_tac "wu1 = repeat [u] (length wu1)")
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   apply(force)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(subgoal_tac "wa3 = repeat [a] (length wa3)")
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   apply(force)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(subgoal_tac "wu2 = repeat [u] (length wu2)")
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
   apply(force)
  apply(rename_tac wa3 wu1 c wa1 wu2 wa2)(*strict*)
  apply(clarsimp)
  apply(rename_tac wu1 c wu2 wa2)(*strict*)
  apply(simp add: repeat_plus)
  apply(thin_tac "length (repeat [a] (length wu1)) = length wu1")
  apply(thin_tac "set (repeat [a] (length wu1)) \<subseteq> {a}")
  apply(thin_tac "set (repeat [a] (length wu2)) \<subseteq> {a}")
  apply(thin_tac "length (repeat [a] (length wu2)) = length wu2")
  apply(subgoal_tac "repeat [a] (length wu1) @ wa2 = wa2 @ a # repeat [a] (length wu2)")
   apply(rename_tac wu1 c wu2 wa2)(*strict*)
   apply(case_tac wu1)
    apply(rename_tac wu1 c wu2 wa2)(*strict*)
    apply(clarsimp)
   apply(rename_tac wu1 c wu2 wa2 aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac c wu2 wa2 list)(*strict*)
   apply(subgoal_tac "list=wu2")
    apply(rename_tac c wu2 wa2 list)(*strict*)
    apply(clarsimp)
   apply(rename_tac c wu2 wa2 list)(*strict*)
   apply(subgoal_tac "(length list) = (length wu2)")
    apply(rename_tac c wu2 wa2 list)(*strict*)
    apply(force)
   apply(rename_tac c wu2 wa2 list)(*strict*)
   apply(subgoal_tac "a # repeat [a] (length list) @ wa2 = wa2@a # repeat [a] (length list)")
    apply(rename_tac c wu2 wa2 list)(*strict*)
    prefer 2
    apply(rule_tac
      t="repeat [a] (length list) @ wa2"
      in ssubst)
     apply(rename_tac c wu2 wa2 list)(*strict*)
     apply(rule_tac
      a="a"
      in append_commute)
     apply (metis repeat_set set_concat_subset)
    apply(rename_tac c wu2 wa2 list)(*strict*)
    apply(clarsimp)
    apply (metis front_tail_set_one)
   apply(rename_tac c wu2 wa2 list)(*strict*)
   apply (metis list.inject repeat_length2 same_append_eq)
  apply(rename_tac wu1 c wu2 wa2)(*strict*)
  apply(rule_tac
      ?w1.0="repeat [a] (length wu1) @ wa2 "
      and b="b"
      in equal_front)
    apply(rename_tac wu1 c wu2 wa2)(*strict*)
    apply(force)
   apply(rename_tac wu1 c wu2 wa2)(*strict*)
   apply (metis repeat_set set_concat_subset singletonD subsetCE)
  apply(rename_tac wu1 c wu2 wa2)(*strict*)
  apply (metis ConsApp insert_absorb repeat.simps(2) repeat_plus repeat_set singleton_insert_inj_eq subset_code(1))
  done

lemma exampleR_removal_from_exampleA_part2: "
  a \<noteq> b
  \<Longrightarrow> exampleA n a b u - exampleR n a b u \<subseteq> exampleA (Suc n) a b u"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> prefix_closure({an. set an \<subseteq> {a} \<and> length an = n} @\<^sub>L\<^sub>L {an @ b # un |an un. set an \<subseteq> {a} \<and> set un \<subseteq> {u} \<and> length an = length un})")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: exampleA_def)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> exampleA n a b u")
  apply(simp add: exampleR2_def exampleR1_def exampleR_def prefix_closure_def prefix_def append_language_def)
  apply(clarsimp)
  apply(rename_tac x aa c an un)(*strict*)
  apply(subgoal_tac "prefix x aa \<or> X" for X)
   apply(rename_tac x aa c an un)(*strict*)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x aa c an un)(*strict*)
  apply(erule disjE)
   apply(rename_tac x aa c an un)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x an un ca)(*strict*)
   apply(rule_tac
      m="0"
      and c="repeat [a] (Suc (length ca))@[b]"
      in exampleA_intro)
   apply(clarsimp)
   apply(simp add: repeat_plus)
   apply (metis front_tail_set_one repeat_intro)
  apply(rename_tac x aa c an un)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac aa c an un ca)(*strict*)
  apply(subgoal_tac "prefix ca an \<or> X" for X)
   apply(rename_tac aa c an un ca)(*strict*)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac aa c an un ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac aa c an un ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac aa un ca cb)(*strict*)
   apply(case_tac ca)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac aa un cb)(*strict*)
    apply(rule_tac
      m="0"
      and c="[a,b]"
      in exampleA_intro)
    apply(clarsimp)
    apply (metis front_tail_set_one repeat_intro)
   apply(rename_tac aa un ca cb aaa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa un cb list)(*strict*)
   apply(rule_tac
      m="length list"
      and c="[b] @ repeat [u] (length list)"
      in exampleA_intro)
   apply(clarsimp)
   apply (metis append_assoc front_tail_set_one repeat_intro set_concat_subset)
  apply(rename_tac aa c an un ca)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac aa c an un cb)(*strict*)
  apply(case_tac cb)
   apply(rename_tac aa c an un cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa an un)(*strict*)
   apply(rule_tac
      m="length an"
      and c="[a,b] @ repeat [u] (length an)"
      in exampleA_intro)
   apply(clarsimp)
   apply (metis append_assoc front_tail_set_one repeat_intro set_concat_subset)
  apply(rename_tac aa c an un cb aaa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c an list)(*strict*)
  apply(case_tac an)
   apply(rename_tac aa c an list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa)(*strict*)
   apply(force)
  apply(rename_tac aa c an list aaa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c list lista)(*strict*)
  apply(case_tac list)
   apply(rename_tac aa c list lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa c lista)(*strict*)
   apply(rule_tac
      m="length lista"
      and c="repeat [u] (length lista)"
      in exampleA_intro)
   apply(clarsimp)
   apply (metis append_assoc front_tail_set_one repeat_intro set_concat_subset)
  apply(rename_tac aa c list lista aaa listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c lista listb)(*strict*)
  apply(case_tac c)
   apply(rename_tac aa c lista listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa lista listb)(*strict*)
   apply(erule_tac
      x="aa @ a # lista"
      in allE)
   apply(erule_tac
      x="aa @ a # lista"
      in allE)
   apply(erule_tac
      x="u#listb"
      in allE)
   apply(clarsimp)
  apply(rename_tac aa c lista listb aaa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa lista listb list)(*strict*)
  apply(rule_tac
      m="length lista"
      and c="repeat [u] (length list)"
      in exampleA_intro)
  apply(clarsimp)
  apply(simp add: repeat_plus)
  apply(subgoal_tac "lista = repeat [a] (length lista)")
   apply(rename_tac aa lista listb list)(*strict*)
   prefer 2
   apply(rule repeat_intro)
    apply(rename_tac aa lista listb list)(*strict*)
    apply(force)
   apply(rename_tac aa lista listb list)(*strict*)
   apply(force)
  apply(rename_tac aa lista listb list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa listb list)(*strict*)
  apply(simp add: repeat_plus)
  apply (metis append_Cons append_Nil append_assoc front_tail_set_one repeat_intro)
  done

lemma exampleR_removal_from_exampleA: "
  a\<noteq>b
  \<Longrightarrow> exampleA (Suc n) a b u = exampleA n a b u - exampleR n a b u"
  apply(rule antisym)
   apply(rule exampleR_removal_from_exampleA_part1)
   apply(force)
  apply(rule exampleR_removal_from_exampleA_part2)
  apply(force)
  done

lemma exampleR_nonempty: "
  exampleR n a b u \<noteq> {}"
  apply(simp add: exampleR_def exampleR1_def)
  apply(rule disjI1)
  apply(rule_tac
      x="repeat [a] n"
      in exI)
  apply(rule conjI)
   apply(rule repeat_set)
  apply(rule repeat_length2)
  done

definition exampleP :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set"
  where
    "exampleP a b u =
  prefix_closure {an@[b]@un| an un. set an \<subseteq> {a} \<and> set un \<subseteq> {u}}"

lemma controllable_subset_not_in_exampleR1: "
  a \<noteq> u
  \<Longrightarrow> b \<noteq> u
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> x \<in> controllable_subset (exampleA n a b u) {u} (exampleP a b u)
  \<Longrightarrow> x \<notin> exampleR1 n a b u"
  apply(simp add: controllable_subset_def exampleA_def exampleR_def append_language_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def exampleR1_def exampleP_def)
  apply(clarsimp)
  apply(rename_tac an)(*strict*)
  apply(erule_tac
      x="an@[b]"
      in ballE)
   apply(rename_tac an)(*strict*)
   prefer 2
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac an)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac an)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac aa c ana un)(*strict*)
   apply(case_tac ana)
    apply(rename_tac aa c ana un)(*strict*)
    prefer 2
    apply(rename_tac aa c ana un aaa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac aa c ana un)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa)(*strict*)
   apply(rule_tac
      x="aa @ b # u # repeat [u] (length aa)"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="aa"
      in exI)
   apply(rule_tac
      x="u # repeat [u] (length aa)"
      in exI)
   apply(rule conjI)
    apply(rename_tac aa)(*strict*)
    apply(force)
   apply(rename_tac aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac aa)(*strict*)
    apply(force)
   apply(rename_tac aa)(*strict*)
   apply(simp add: repeat_set)
  apply(rename_tac an)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarify)
  apply(rename_tac an v va aa c aaa ca ba baa ana un anb una)(*strict*)
  apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)
  apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
  apply(subgoal_tac "wa1=wa2@wa3")
   apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
   prefer 2
   apply(rule_tac
      b="b"
      and ?v1.0="c"
      and ?v2.0="wu1"
      in equal_front)
     apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
    apply(blast)
   apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac wa1 wa2 c wa5 ca wa3 wu1 wa4 wu2)(*strict*)
   apply(blast)
  apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
  apply(subgoal_tac "wa1=wa5@wa4")
   apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
   prefer 2
   apply(rule_tac
      b="b"
      and ?v1.0="u#ca"
      and ?v2.0="wu2"
      in equal_front)
     apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
    apply(blast)
   apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac wa1 wa2 c wa5 ca wa3 wu1 wa4 wu2)(*strict*)
   apply(blast)
  apply(rename_tac wa1 v va wa2 c wa5 ca ba baa wa3 wu1 wa4 wu2)(*strict*)
  apply(clarsimp)
  done

lemma controllable_subset_not_in_exampleR2: "
  a \<noteq> u
  \<Longrightarrow> b \<noteq> u
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> x \<in> controllable_subset (exampleA n a b u) {u} (exampleP a b u)
  \<Longrightarrow> x \<notin> exampleR2 n a b u"
  apply(simp add: controllable_subset_def exampleA_def exampleR_def append_language_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def exampleR2_def exampleP_def)
  apply(clarsimp)
  apply(rename_tac an un)(*strict*)
  apply(erule_tac
      x="an@[b]@un"
      in ballE)
   apply(rename_tac an un)(*strict*)
   prefer 2
   apply(simp add: prefix_closure_def prefix_def)
  apply(rename_tac an un)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac an un)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac an un aa c ana una)(*strict*)
   apply(subgoal_tac "an=aa@ana")
    apply(rename_tac an un aa c ana una)(*strict*)
    prefer 2
    apply(rule_tac
      b="b"
      and ?v1.0="un@c"
      and ?v2.0="una"
      in equal_front)
      apply(rename_tac an un aa c ana una)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac an un aa c ana una)(*strict*)
     apply(blast)
    apply(rename_tac an un aa c ana una)(*strict*)
    apply(simp (no_asm))
    apply(blast)
   apply(rename_tac an un aa c ana una)(*strict*)
   apply(clarsimp)
   apply(rename_tac un aa ana)(*strict*)
   apply(rule_tac
      x="aa @ ana @ b # un @ u # repeat [u] (length aa)"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="aa@ana"
      in exI)
   apply(rule_tac
      x="un@u # repeat [u] (length aa)"
      in exI)
   apply(rule conjI)
    apply(rename_tac un aa ana)(*strict*)
    apply(force)
   apply(rename_tac un aa ana)(*strict*)
   apply(rule conjI)
    apply(rename_tac un aa ana)(*strict*)
    apply(force)
   apply(rename_tac un aa ana)(*strict*)
   apply(simp add: repeat_set)
  apply(rename_tac an un)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarify)
  apply(rename_tac an un v va aa c aaa ca ba baa ana una anb unb)(*strict*)
  apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)
  apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
  apply(subgoal_tac "wa1=wa2@wa5")
   apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
   prefer 2
   apply(rule_tac
      b="b"
      and ?v1.0="wu1@c"
      and ?v2.0="wu3"
      in equal_front)
     apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
    apply(blast)
   apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
   apply(simp (no_asm))
   apply(rename_tac wa1 wu1 wa2 c wa3 ca wa5 wu3 wa4 wu2)(*strict*)
   apply(blast)
  apply(rename_tac wa1 wu1 v va wa2 c wa3 ca ba baa wa5 wu3 wa4 wu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
  apply(subgoal_tac "wa5=wa4")
   apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
   prefer 2
   apply(rule_tac
      b="b"
      and ?v1.0="wu1@u#ca"
      and ?v2.0="wu2"
      in equal_front)
     apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
    apply(blast)
   apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
   apply(blast)
  apply(rename_tac wu1 wa3 ca wa5 wa4 wu2)(*strict*)
  apply(clarsimp)
  done

lemma exampleA_without_exampleR_in_controllable_subset: "
  a \<noteq> u
  \<Longrightarrow> b \<noteq> u
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> exampleA n a b u - exampleR n a b u \<subseteq> controllable_subset (exampleA n a b u) {u} (exampleP a b u)"
  apply(simp add: controllable_subset_def exampleA_def exampleR_def append_language_def controllable_sublanguage_def controllable_word_def alphabet_to_language_def exampleR1_def exampleR2_def exampleP_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x aa c an un)(*strict*)
  apply(erule disjE)
   apply(rename_tac x aa c an un)(*strict*)
   apply(subgoal_tac "prefix x aa \<or> X" for X)
    apply(rename_tac x aa c an un)(*strict*)
    prefer 2
    apply (rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x aa c an un)(*strict*)
   apply(erule_tac
      P="x \<sqsubseteq> aa"
      in disjE)
    apply(rename_tac x aa c an un)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x an un ca)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac x an un ca)(*strict*)
     apply(force)
    apply(rename_tac x an un ca)(*strict*)
    apply(erule_tac
      x="x@ca@[b]"
      in allE)
    apply(clarsimp)
    apply(rename_tac x an un ca)(*strict*)
    apply(erule_tac
      x="x@ca"
      in allE)
    apply(erule impE)
     apply(rename_tac x an un ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac x an un ca)(*strict*)
    apply(erule impE)
     apply(rename_tac x an un ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac x an un ca)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="[b]"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="[]"
      in allE)
    apply(erule_tac
      x="[]"
      in allE)
    apply(clarsimp)
   apply(rename_tac x aa c an un)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac aa c an un ca)(*strict*)
   apply(subgoal_tac "prefix ca an \<or> X" for X)
    apply(rename_tac aa c an un ca)(*strict*)
    prefer 2
    apply (rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac aa c an un ca)(*strict*)
   apply(erule disjE)
    apply(rename_tac aa c an un ca)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac aa un ca cb)(*strict*)
     apply(force)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(thin_tac "\<forall>an un. set un \<subseteq> {u} \<longrightarrow> set an \<subseteq> {a} \<longrightarrow> aa @ ca = an @ b # un \<longrightarrow> length an \<noteq> length un + length aa")
    apply(erule_tac
      x="aa@ca@[b]@repeat [u] (length ca)"
      in allE)
    apply(clarsimp)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(erule_tac
      x="ca@[b]@repeat [u] (length ca)"
      in allE)
    apply(erule disjE)
     apply(rename_tac aa un ca cb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(erule_tac
      x="ca"
      in allE)
    apply(erule_tac
      x="repeat [u] (length ca)"
      in allE)
    apply(clarsimp)
    apply(erule impE)
     apply(rename_tac aa un ca cb)(*strict*)
     apply(rule repeat_set)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(subgoal_tac "length (repeat [u] (length ca)) = length ca")
     apply(rename_tac aa un ca cb)(*strict*)
     apply(force)
    apply(rename_tac aa un ca cb)(*strict*)
    apply(rule repeat_length2)
   apply(rename_tac aa c an un ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac aa c an un cb)(*strict*)
   apply(case_tac cb)
    apply(rename_tac aa c an un cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac aa an un)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac aa an un)(*strict*)
     apply(force)
    apply(rename_tac aa an un)(*strict*)
    apply(thin_tac "\<forall>ana un. set un \<subseteq> {u} \<longrightarrow> set ana \<subseteq> {a} \<longrightarrow> aa @ an = ana @ b # un \<longrightarrow> length ana \<noteq> length un + length aa")
    apply(erule_tac
      x="aa@an@[b]@repeat [u] (length an)"
      in allE)
    apply(clarsimp)
    apply(rename_tac aa an un)(*strict*)
    apply(erule_tac
      x="an@[b]@repeat [u] (length an)"
      in allE)
    apply(erule disjE)
     apply(rename_tac aa an un)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac aa an un)(*strict*)
    apply(erule_tac
      x="an"
      in allE)
    apply(erule_tac
      x="repeat [u] (length an)"
      in allE)
    apply(clarsimp)
    apply(erule impE)
     apply(rename_tac aa an un)(*strict*)
     apply(rule repeat_set)
    apply(rename_tac aa an un)(*strict*)
    apply(subgoal_tac "length (repeat [u] (length an)) = length an")
     apply(rename_tac aa an un)(*strict*)
     apply(force)
    apply(rename_tac aa an un)(*strict*)
    apply(rule repeat_length2)
   apply(rename_tac aa c an un cb aaa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa c an list)(*strict*)
   apply(rule_tac
      x="aa @ an"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x="aa @ an"
      in allE)
   apply(erule_tac
      P="\<lambda>un. set un \<subseteq> {u} \<longrightarrow> set (aa @ an) \<subseteq> {a} \<longrightarrow> aa @ an @ b # list = (aa @ an) @ b # un \<longrightarrow> length (aa @ an) \<noteq> length un + length aa"
      and x="list"
      in allE)
   apply(erule impE)
    apply(rename_tac aa c an list)(*strict*)
    apply(force)
   apply(rename_tac aa c an list)(*strict*)
   apply(erule impE)
    apply(rename_tac aa c an list)(*strict*)
    apply(force)
   apply(rename_tac aa c an list)(*strict*)
   apply(erule impE)
    apply(rename_tac aa c an list)(*strict*)
    apply(force)
   apply(rename_tac aa c an list)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="aa @ an @ b # list @ c"
      in allE)
   apply(clarsimp)
   apply(rename_tac aa c an list)(*strict*)
   apply(erule_tac
      x="an @ b # list @ c"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="an"
      in allE)
   apply(erule_tac
      x="list @ c"
      in allE)
   apply(clarsimp)
  apply(rename_tac x aa c an un)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c an un w ca ana cb una)(*strict*)
  apply(subgoal_tac "prefix w ana \<or> X" for X)
   apply(rename_tac aa c an un w ca ana cb una)(*strict*)
   prefer 2
   apply (rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac aa c an un w ca ana cb una)(*strict*)
  apply(erule disjE)
   apply(rename_tac aa c an un w ca ana cb una)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac aa c an un w ca cb una cc)(*strict*)
   apply(case_tac cc)
    apply(rename_tac aa c an un w ca cb una cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac aa c an un w ca cb una cc aaa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa c an un w ca ana cb una)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac aa c an un ca ana cb una cc)(*strict*)
  apply(case_tac cc)
   apply(rename_tac aa c an un ca ana cb una cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa c an un ca ana cb una cc aaa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c an un ca ana cb list)(*strict*)
  apply(subgoal_tac "ana=aa@an")
   apply(rename_tac aa c an un ca ana cb list)(*strict*)
   prefer 2
   apply(rule_tac
      b="b"
      and ?v1.0="list @ ca @ c"
      and ?v2.0="un"
      in equal_front)
     apply(rename_tac aa c an un ca ana cb list)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac aa c an un ca ana cb list)(*strict*)
    apply(blast)
   apply(rename_tac aa c an un ca ana cb list)(*strict*)
   apply(simp (no_asm))
   apply(blast)
  apply(rename_tac aa c an un ca ana cb list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa c an ca cb list)(*strict*)
  apply(rename_tac wa2 wu4 wa1 wu3 wu2 wu1)
  apply(rename_tac wa2 wu4 wa1 wu3 wu2 wu1)(*strict*)
  apply(rule_tac
      x="wa2 @ wa1"
      in exI)
  apply(clarsimp)
  apply(erule_tac
      P="\<lambda>an. \<forall>un. set un \<subseteq> {u} \<longrightarrow> set an \<subseteq> {a} \<longrightarrow> wa2 @ wa1 @ b # wu1 @ wu3 = an @ b # un \<longrightarrow> length an \<noteq> length un + length wa2"
      and x="wa2 @ wa1"
      in allE)
  apply(erule_tac
      P="\<lambda>un. set un \<subseteq> {u} \<longrightarrow> set (wa2 @ wa1) \<subseteq> {a} \<longrightarrow> wa2 @ wa1 @ b # wu1 @ wu3 = (wa2 @ wa1) @ b # un \<longrightarrow> length (wa2 @ wa1) \<noteq> length un + length wa2"
      and x="wu1 @ wu3"
      in allE)
  apply(clarsimp)
  apply(case_tac wu4)
   apply(rename_tac wa2 wu4 wa1 wu3 wu2 wu1)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa2 wu4 wa1 wu3 wu2 wu1 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa2 wa1 wu3 wu2 wu1 list)(*strict*)
  apply(rename_tac wu4)
  apply(rename_tac wa2 wa1 wu3 wu2 wu1 wu4)(*strict*)
  apply(erule_tac
      x="wa2 @ wa1 @ b # wu1 @ u # wu3@wu4"
      in allE)
  apply(clarsimp)
  apply(rename_tac wa2 wa1 wu3 wu2 wu1 wu4)(*strict*)
  apply(erule_tac
      x="wa1 @ b # wu1 @ u # wu3 @ wu4"
      in allE)
  apply(erule disjE)
   apply(rename_tac wa2 wa1 wu3 wu2 wu1 wu4)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac wa2 wa1 wu3 wu2 wu1 wu4)(*strict*)
  apply(erule_tac
      x="wa1"
      in allE)
  apply(erule_tac
      x="wu1 @ u # wu3 @ wu4"
      in allE)
  apply(clarsimp)
  done

lemma correct_next_Cn_is_computed: "
  F = Enforce_Controllable_Subset \<Sigma>UC Pum
  \<Longrightarrow> Pum = exampleP a b u
  \<Longrightarrow> P = DES Pum Pum
  \<Longrightarrow> \<Sigma>UC = {u}
  \<Longrightarrow> a \<noteq> u
  \<Longrightarrow> b \<noteq> u
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> Rum = (\<lambda>n. exampleR n a b u)
  \<Longrightarrow> Aum = (\<lambda>n. exampleA n a b u)
  \<Longrightarrow> C = (\<lambda>n. DES (Aum n) (Aum n))
  \<Longrightarrow> R = (\<lambda>n. DES (Rum n) (Rum n))
  \<Longrightarrow> F (C n) = C (Suc n)"
  apply(subgoal_tac "Rum n \<subseteq> Aum n")
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      A="exampleR n a b u"
      in set_mp)
    apply(rename_tac x)(*strict*)
    apply(simp add: exampleR_in_exampleA)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(subgoal_tac "Aum (Suc n) = (Aum n) - (Rum n)")
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and a="a"
      and b="b"
      and u="u"
      in exampleR_removal_from_exampleA)
    apply(force)
   apply(force)
  apply(subgoal_tac "Rum n \<noteq> {}")
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and a="a"
      and b="b"
      and u="u"
      in exampleR_nonempty)
   apply(force)
  apply(subgoal_tac "(\<And>C. F C \<le> C)")
   prefer 2
   apply(rename_tac Ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac C)(*strict*)
   apply(simp add: Enforce_Controllable_Subset_def DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def Let_def controllable_subset_def)
   apply(force)
  apply(clarsimp)
  apply(simp add: Enforce_Controllable_Subset_def Let_def des_langM_def des_langUM_def)
  apply(rule context_conjI)
   prefer 2
   apply(force)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    apply(simp add: controllable_subset_def)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "(\<And>C. DES (controllable_subset (case C of DES A B \<Rightarrow> A) {u} (exampleP a b u)) (controllable_subset (case C of DES A B \<Rightarrow> A) {u} (exampleP a b u) \<inter> (case C of DES A B \<Rightarrow> B)) \<le> C)")
   apply(thin_tac "exampleA (Suc n) a b u = exampleA n a b u - exampleR n a b u")
   apply(thin_tac "exampleR n a b u \<subseteq> exampleA n a b u")
   apply(thin_tac "exampleR n a b u \<noteq> {}")
   apply(simp add: exampleR_def)
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      a="a"
      and b="b"
      and u="u"
      in controllable_subset_not_in_exampleR1)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule controllable_subset_not_in_exampleR2)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(thin_tac "(\<And>C. DES (controllable_subset (case C of DES A B \<Rightarrow> A) {u} (exampleP a b u)) (controllable_subset (case C of DES A B \<Rightarrow> A) {u} (exampleP a b u) \<inter> (case C of DES A B \<Rightarrow> B)) \<le> C)")
  apply(thin_tac "exampleA (Suc n) a b u = exampleA n a b u - exampleR n a b u")
  apply(thin_tac "exampleR n a b u \<subseteq> exampleA n a b u")
  apply(thin_tac "exampleR n a b u \<noteq> {}")
  apply(rule exampleA_without_exampleR_in_controllable_subset)
    apply(force)
   apply(force)
  apply(force)
  done

theorem example_infinite_computation_of_fixed_point: "
  F = Enforce_Controllable_Subset \<Sigma>UC Pum
  \<Longrightarrow> Pum = exampleP a b u
  \<Longrightarrow> P = DES Pum Pum
  \<Longrightarrow> \<Sigma>UC = {u}
  \<Longrightarrow> a \<noteq> u
  \<Longrightarrow> b \<noteq> u
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> Rum = (\<lambda>n. exampleR n a b u)
  \<Longrightarrow> Aum = (\<lambda>n. exampleA n a b u)
  \<Longrightarrow> C = (\<lambda>n. DES (Aum n) (Aum n))
  \<Longrightarrow> R = (\<lambda>n. DES (Rum n) (Rum n))
  \<Longrightarrow> Compute_Fixed_Point_Finite n F (C 0) = C n
  \<and> Aum (Suc n) = Aum n - Rum n
  \<and> Rum n \<subseteq> Aum n
  \<and> Rum n \<noteq> {}
  \<and> F (C n) = C (Suc n)
  \<and> F (C n) < C n"
  apply(subgoal_tac "Rum n \<subseteq> Aum n")
   prefer 2
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      A="exampleR n a b u"
      in set_mp)
    apply(rename_tac x)(*strict*)
    apply(simp add: exampleR_in_exampleA)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(subgoal_tac "Aum (Suc n) = (Aum n) - (Rum n)")
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and a="a"
      and b="b"
      and u="u"
      in exampleR_removal_from_exampleA)
    apply(force)
   apply(force)
  apply(subgoal_tac "Rum n \<noteq> {}")
   prefer 2
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n"
      and a="a"
      and b="b"
      and u="u"
      in exampleR_nonempty)
   apply(force)
  apply(subgoal_tac "(\<And>C. F C \<le> C)")
   prefer 2
   apply(rename_tac Ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac C)(*strict*)
   apply(simp add: Enforce_Controllable_Subset_def DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def Let_def controllable_subset_def)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n"
      and F="F"
      and a="a"
      and b="b"
      and u="u"
      in correct_next_Cn_is_computed)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "Compute_Fixed_Point_Finite n F (C 0) = C n")
   apply(clarsimp)
   apply(simp add: Enforce_Controllable_Subset_def DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def Let_def controllable_subset_def)
   apply(force)
  apply(thin_tac "F (DES (exampleA n a b u) (exampleA n a b u)) = DES (exampleA (Suc n) a b u) (exampleA (Suc n) a b u)")
  apply(thin_tac "Rum n \<subseteq> Aum n")
  apply(thin_tac "Aum (Suc n) = Aum n - Rum n")
  apply(thin_tac "Rum n \<noteq> {}")
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F (C 0)"
      and s="F (Compute_Fixed_Point_Finite n F (C 0))"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (C 0)"
      and s="C n"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule correct_next_Cn_is_computed)
            apply(rename_tac n)(*strict*)
            apply(force)
           apply(rename_tac n)(*strict*)
           apply(force)
          apply(rename_tac n)(*strict*)
          apply(force)
         apply(rename_tac n)(*strict*)
         apply(force)
        apply(rename_tac n)(*strict*)
        apply(force)
       apply(rename_tac n)(*strict*)
       apply(force)
      apply(rename_tac n)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

definition FPiteratorInit :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorInit P S \<equiv>
  Enforce_Nonblockingness_DES
  \<circ> (Enforce_Specification_Satisfaction (inf P S))"

definition FPinit :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES"
  where
    "FPinit P S \<equiv>
  FPiteratorInit P S top"

definition FPiteratorMarked :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorMarked \<Sigma>UC P \<equiv>
  ifcomp
   Enforce_Nonblockingness_DES
   (Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P))"

definition FPiteratorStar :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorStar \<Sigma>UC P \<equiv>
  ifcomp
   Enforce_Nonblockingness_DES
   (Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P))"

definition FPiteratorOne :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorOne \<Sigma>UC P \<equiv>
  ifcomp
   Enforce_Nonblockingness_DES
   (Enforce_Controllable_Subset \<Sigma>UC (des_langUM P))"

definition FPiteratorMarkedAlt :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorMarkedAlt \<Sigma>UC P \<equiv>
  Enforce_Nonblockingness_DES
  \<circ> (Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P))
  \<circ> Enforce_Nonblockingness_DES
  \<circ> Enforce_Valid_DES"

definition FPiteratorStarAlt :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorStarAlt \<Sigma>UC P \<equiv>
  Enforce_Nonblockingness_DES
  \<circ> (Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P))
  \<circ> Enforce_Nonblockingness_DES
  \<circ> Enforce_Valid_DES"

definition FPiteratorOneAlt :: "
  '\<Sigma> set
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> ('\<Sigma> DES \<Rightarrow> '\<Sigma> DES)"
  where
    "FPiteratorOneAlt \<Sigma>UC P \<equiv>
  Enforce_Nonblockingness_DES
  \<circ> (Enforce_Controllable_Subset \<Sigma>UC (des_langUM P))
  \<circ> Enforce_Nonblockingness_DES
  \<circ> Enforce_Valid_DES"

lemma spec_simplify: "
  predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))) = (\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  done

theorem Fixed_Point_Iterator_Modify_Signature2: "
  Fixed_Point_Iterator F INP FP OUT
  \<Longrightarrow> (\<And>X. X \<in> INP' \<Longrightarrow> F X \<in> extra)
  \<Longrightarrow> INP' \<subseteq> INP \<inter> weaker \<inter> extra
  \<Longrightarrow> FP' = FP \<inter> weaker \<inter> extra
  \<Longrightarrow> OUT' \<supseteq> OUT \<inter> extra
  \<Longrightarrow> Fixed_Point_Iterator F INP' FP' OUT'"
  apply(simp add: Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(rule conjI)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(rule conjI)
   apply(rename_tac X Y)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in ballE)
    apply(rename_tac X Y)(*strict*)
    apply(erule_tac
      x="Y"
      in ballE)
     apply(rename_tac X Y)(*strict*)
     apply(force)
    apply(rename_tac X Y)(*strict*)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(rule conjI)
   apply(rename_tac X Y)(*strict*)
   apply(erule_tac
      x="X"
      in ballE)
    apply(rename_tac X Y)(*strict*)
    apply(erule_tac
      x="Y"
      in ballE)
     apply(rename_tac X Y)(*strict*)
     apply(force)
    apply(rename_tac X Y)(*strict*)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(erule_tac
      x="X"
      in ballE)
   apply(rename_tac X Y)(*strict*)
   apply(erule_tac
      x="Y"
      in ballE)
    apply(rename_tac X Y)(*strict*)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(force)
  done

theorem Fixed_Point_Iterator_Extend_Signature2: "
  Fixed_Point_Iterator F INP FP OUT
  \<Longrightarrow> (\<And>X. X \<in> INP \<inter> extra \<Longrightarrow> F X \<in> extra)
  \<Longrightarrow> INP' = INP \<inter> extra
  \<Longrightarrow> FP' = FP \<inter> extra
  \<Longrightarrow> OUT' = OUT \<inter> extra
  \<Longrightarrow> Fixed_Point_Iterator F INP' FP' OUT'"
  apply(rule_tac
      weaker="UNIV"
      and extra="extra"
      in Fixed_Point_Iterator_Modify_Signature2)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem Fixed_Point_Iterator_Modify_Signature1: "
  Fixed_Point_Iterator F INP FP (OUT \<inter> extra)
  \<Longrightarrow> Fixed_Point_Iterator F INP FP OUT"
  apply(simp add: Fixed_Point_Iterator_def)
  done

theorem Fixed_Point_Iterator_Modify_Signature1a: "
  Fixed_Point_Iterator F INP FP OUT
  \<Longrightarrow> OUT' \<supseteq> OUT
  \<Longrightarrow> Fixed_Point_Iterator F INP FP OUT'"
  apply(simp add: Fixed_Point_Iterator_def)
  apply(force)
  done

theorem Fixed_Point_Iterator_Modify_Signature1b: "
  Fixed_Point_Iterator F INP FP OUT
  \<Longrightarrow> INP' \<subseteq> INP
  \<Longrightarrow> Fixed_Point_Iterator F INP' FP OUT"
  apply(simp add: Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(erule_tac
      x="X"
      in ballE)
   apply(rename_tac X Y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(erule_tac
      x="Y"
      in ballE)
   apply(rename_tac X Y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(force)
  done

lemma Fixed_Point_Iterator_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorMarked \<Sigma>UC P)
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
  apply(unfold FPiteratorMarked_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      Qout="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
      and ?Qterm2.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
      and ?Qinter2.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C}"
      and ?Qterm1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}"
      and ?Qinter1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C}"
      and Qinp="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
      and ?F2.0="Enforce_Nonblockingness_DES"
      and ?F1.0="Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P)"
      in Conditional_Composition_of_Fixed_Point_Iterators)
      prefer 3
      apply(force)
     prefer 3
     apply(force)
    prefer 3
    apply(clarsimp)
    apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A X B"
      and s="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C \<and> IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}" for F A B
      in ssubst)
     apply(force)
    apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A B X"
      and s="({C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<union> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C})" for F A B
      in ssubst)
     apply(force)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
    apply(force)
   apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      in Fixed_Point_Iterator_Modify_Signature2)
       apply(force)
      apply(rename_tac X)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(simp add: Fixed_Point_Iterator_def DES_specification_satisfied_def)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in allE)
   apply(erule impE)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      in Fixed_Point_Iterator_Modify_Signature2)
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(simp add: Fixed_Point_Iterator_def DES_specification_satisfied_def)
  apply(clarsimp)
  apply(erule_tac
      x="X"
      in allE)
  apply(erule impE)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(force)
  done

lemma Fixed_Point_Iterator_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorStar \<Sigma>UC P)
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
  apply(unfold FPiteratorStar_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Fixed_Point_Iterator_Enforce_Star_Controllable_Subset)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?Qout.0="{C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C}"
      and ?Qterm2.0="{C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C \<and> DES_controllability \<Sigma>UC P C}"
      and ?Qinter2.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_controllability \<Sigma>UC P C}"
      and ?Qterm1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}"
      and ?Qinter1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_controllability \<Sigma>UC P C}"
      and Qinp="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
      and ?F2.0="Enforce_Nonblockingness_DES"
      and ?F1.0="Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P)"
      in Conditional_Composition_of_Fixed_Point_Iterators)
      prefer 3
      apply(force)
     prefer 3
     apply(force)
    apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      and weaker="{C. DES_nonblockingness C}"
      in Fixed_Point_Iterator_Modify_Signature2)
        apply(force)
       apply(rename_tac X)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac X)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(simp add: Fixed_Point_Iterator_def)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(simp add: DES_specification_satisfied_def)
    apply(force)
   apply(thin_tac "Fixed_Point_Iterator (Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P)) {C. IsDES C} {C. IsDES C \<and> DES_controllability \<Sigma>UC P C} {C. IsDES C \<and> DES_controllability \<Sigma>UC P C}")
   apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      and weaker="{C. DES_controllability \<Sigma>UC P C}"
      in Fixed_Point_Iterator_Modify_Signature2)
       apply(force)
      apply(rename_tac X)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(simp add: Fixed_Point_Iterator_def)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(simp add: DES_specification_satisfied_def)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A X B"
      and s="{C. if Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P) C = C then C \<in> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C} else C \<in> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<inter> {C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C \<and> DES_controllability \<Sigma>UC P C}}" for F A B
      in ssubst)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A B X"
      and s="({C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_controllability \<Sigma>UC P C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<union> {C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C})" for F A B
      in ssubst)
   apply(force)
  apply(force)
  done

lemma Fixed_Point_Iterator_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorOne \<Sigma>UC P)
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
  apply(unfold FPiteratorOne_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      in Fixed_Point_Iterator_Enforce_Controllable_Subset)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?Qout.0="{C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C}"
      and ?Qterm2.0="{C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C}"
      and ?Qinter2.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C }"
      and ?Qterm1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}"
      and ?Qinter1.0="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C}"
      and Qinp="{C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
      and ?F2.0="Enforce_Nonblockingness_DES"
      and ?F1.0="Enforce_Controllable_Subset \<Sigma>UC (des_langUM P)"
      in Conditional_Composition_of_Fixed_Point_Iterators)
      prefer 3
      apply(force)
     prefer 3
     apply(force)
    apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      and weaker="{C. DES_nonblockingness C}"
      in Fixed_Point_Iterator_Modify_Signature2)
        apply(force)
       apply(rename_tac X)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac X)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(simp add: Fixed_Point_Iterator_def)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="X"
      in allE)
    apply(clarsimp)
    apply(simp add: DES_specification_satisfied_def)
    apply(force)
   apply(thin_tac "Fixed_Point_Iterator (Enforce_Controllable_Subset \<Sigma>UC (des_langUM P)) {C. IsDES C} {C. IsDES C \<and> DES_controllability \<Sigma>UC P C} {C. IsDES C}")
   apply(rule_tac
      extra="{C. DES_specification_satisfied (inf P S) C}"
      and weaker="top"
      in Fixed_Point_Iterator_Modify_Signature2)
       apply(force)
      apply(rename_tac X)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac X)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(simp add: Fixed_Point_Iterator_def)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(simp add: DES_specification_satisfied_def)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A X B"
      and s="{C. if Enforce_Controllable_Subset \<Sigma>UC (des_langUM P) C = C then C \<in> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C} else C \<in> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<inter> {C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C}}" for F A B
      in ssubst)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A B X"
      and s="({C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C} \<inter> {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C} \<union> {C. IsDES C \<and> DES_nonblockingness C \<and> DES_specification_satisfied (inf P S) C})" for F A B
      in ssubst)
   apply(force)
  apply(force)
  done

theorem Fixed_Point_Iterator_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> Fixed_Point_Iterator
  (F \<Sigma>UC P)
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule Fixed_Point_Iterator_FPiteratorMarked)
    apply(force)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule Fixed_Point_Iterator_FPiteratorStar)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule Fixed_Point_Iterator_FPiteratorOne)
   apply(force)
  apply(force)
  done

lemma FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (FPiteratorMarkedAlt \<Sigma>UC P)
  UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))
  (predicate_AND IsDES DES_nonblockingness)"
  apply(unfold FPiteratorMarkedAlt_def)
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="(predicate_AND IsDES DES_nonblockingness)"
      and ?Qinter2.0="(predicate_AND IsDES DES_nonblockingness)"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
    apply(force)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  done

lemma FPiteratorStarAlt_is_Characteristic_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (FPiteratorStarAlt \<Sigma>UC P)
  UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))
  (predicate_AND IsDES DES_nonblockingness)"
  apply(unfold FPiteratorStarAlt_def)
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="(predicate_AND IsDES DES_nonblockingness)"
      and ?Qinter2.0="(predicate_AND IsDES DES_nonblockingness)"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and \<Sigma>UC="\<Sigma>UC"
      in Fixed_Point_Iterator_Enforce_Star_Controllable_Subset)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?Qterm1.0="{C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C}"
      and ?Qout2.0="{a. predicate_AND IsDES DES_nonblockingness a}"
      and Qinp="{a. predicate_AND IsDES DES_nonblockingness a}"
      and ?Qinter1.0="{C. IsDES C \<and> DES_controllability \<Sigma>UC P C}"
      and ?F1.0="Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P)"
      and ?F2.0="Enforce_Nonblockingness_DES"
      in Composition_of_Fixed_Point_Iterators)
     apply(rule_tac
      weaker="{C. DES_nonblockingness C}"
      and extra="top"
      in Fixed_Point_Iterator_Modify_Signature2)
         apply(force)
        apply(rename_tac X)(*strict*)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A X B"
      and s="({C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C} \<inter> {C. IsDES C \<and> DES_nonblockingness C})" for F A B
      in ssubst)
   apply(force)
  apply(force)
  done

lemma FPiteratorOneAlt_is_Characteristic_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (FPiteratorOneAlt \<Sigma>UC P)
  UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))
  (predicate_AND IsDES DES_nonblockingness)"
  apply(unfold FPiteratorOneAlt_def)
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="(predicate_AND IsDES DES_nonblockingness)"
      and ?Qinter2.0="(predicate_AND IsDES DES_nonblockingness)"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and \<Sigma>UC="\<Sigma>UC"
      in Fixed_Point_Iterator_Enforce_Controllable_Subset)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?Qterm1.0="{C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C}"
      and ?Qout2.0="{a. predicate_AND IsDES DES_nonblockingness a}"
      and Qinp="{a. predicate_AND IsDES DES_nonblockingness a}"
      and ?Qinter1.0="{C. IsDES C }"
      and ?F1.0="Enforce_Controllable_Subset \<Sigma>UC (des_langUM P)"
      and ?F2.0="Enforce_Nonblockingness_DES"
      in Composition_of_Fixed_Point_Iterators)
     apply(rule_tac
      weaker="{C. DES_nonblockingness C}"
      and extra="top"
      in Fixed_Point_Iterator_Modify_Signature2)
         apply(force)
        apply(rename_tac X)(*strict*)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      P="\<lambda>X. Fixed_Point_Iterator F A X B"
      and s="({C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C} \<inter> {C. IsDES C \<and> DES_nonblockingness C})" for F A B
      in ssubst)
   apply(force)
  apply(force)
  done

lemma FPiteratorMarkedAlt_is_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorMarkedAlt \<Sigma>UC P)
  top
  {C. IsDES C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_nonblockingness C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma FPiteratorStarAlt_is_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorStarAlt \<Sigma>UC P)
  top
  {C. IsDES C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_nonblockingness C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule FPiteratorStarAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma FPiteratorOneAlt_is_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorOneAlt \<Sigma>UC P)
  top
  {C. IsDES C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_nonblockingness C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule FPiteratorOneAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

theorem Fixed_Point_Iterator_FPiteratorMarkedAlt_FPiteratorStarAlt_FPiteratorOneAlt: "
  IsDES P
  \<Longrightarrow> F \<in> {FPiteratorMarkedAlt,FPiteratorStarAlt,FPiteratorOneAlt}
  \<Longrightarrow> Fixed_Point_Iterator
  (F \<Sigma>UC P)
  top
  {C. IsDES C \<and> DES_nonblockingness C \<and> DES_controllability \<Sigma>UC P C}
  {C. IsDES C \<and> DES_nonblockingness C}"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule FPiteratorMarkedAlt_is_Fixed_Point_Iterator)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule FPiteratorStarAlt_is_Fixed_Point_Iterator)
   apply(force)
  apply(clarsimp)
  apply(rule FPiteratorOneAlt_is_Fixed_Point_Iterator)
  apply(force)
  done

lemma FPiteratorInit_is_Characteristic_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (Enforce_Nonblockingness_DES
  \<circ> (Enforce_Specification_Satisfaction S))
  IsDES
  (predicate_AND (predicate_AND IsDES (DES_specification_satisfied S)) (predicate_AND (predicate_AND IsDES (DES_specification_satisfied S))
       (predicate_AND IsDES DES_nonblockingness)))
  (predicate_AND (predicate_AND IsDES (DES_specification_satisfied S)) (predicate_AND IsDES DES_nonblockingness))"
  apply(rule_tac
      ?Qinter2.0="predicate_AND IsDES (DES_specification_satisfied S)"
      and ?Qinter1.0="(predicate_AND IsDES (DES_specification_satisfied S))"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
    apply(force)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule conjI)
    apply(rename_tac X)(*strict*)
    apply(simp add: DES_specification_satisfied_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(force)
  done

theorem FPiteratorInit_is_Fixed_Point_Iterator: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Fixed_Point_Iterator
  (FPiteratorInit P S)
  {C. IsDES C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}
  {C. IsDES C \<and> DES_specification_satisfied (inf P S) C \<and> DES_nonblockingness C}"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   prefer 2
   apply(rule_tac
      P="P"
      and S="(inf P S)"
      in FPiteratorInit_is_Characteristic_Fixed_Point_Iterator)
    apply(force)
   apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  apply(unfold FPiteratorInit_def)
  apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator3)
    apply(force)
   apply(force)
  apply(force)
  done

lemma FPiterator_and_FPiteratorMarkedAlt_coincide: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> FPiteratorMarkedAlt \<Sigma>UC P C = FPiteratorMarked \<Sigma>UC P C"
  apply(simp add: FPiteratorMarkedAlt_def FPiteratorMarked_def)
  apply(rule_tac
      t="Enforce_Valid_DES C"
      and s="C"
      in ssubst)
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Valid_DES UNIVmap IsDES IsDES")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   apply(subgoal_tac "IsDES C = (Enforce_Valid_DES C = C)")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(blast)
   apply(force)
  apply(subgoal_tac "Enforce_Nonblockingness_DES C=C")
   prefer 2
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(erule conjE)+
   apply(blast)
  apply(simp add: ifcomp_def FPiteratorMarked_def FPinit_def FPiteratorInit_def)
  done

lemma FPiterator_and_FPiteratorStarAlt_coincide: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> FPiteratorStarAlt \<Sigma>UC P C = FPiteratorStar \<Sigma>UC P C"
  apply(simp add: FPiteratorStarAlt_def FPiteratorStar_def)
  apply(rule_tac
      t="Enforce_Valid_DES C"
      and s="C"
      in ssubst)
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Valid_DES UNIVmap IsDES IsDES")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   apply(subgoal_tac "IsDES C = (Enforce_Valid_DES C = C)")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(blast)
   apply(force)
  apply(subgoal_tac "Enforce_Nonblockingness_DES C=C")
   prefer 2
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(erule conjE)+
   apply(blast)
  apply(simp add: ifcomp_def FPiteratorMarked_def FPinit_def FPiteratorInit_def)
  done

lemma FPiterator_and_FPiteratorOneAlt_coincide: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> FPiteratorOneAlt \<Sigma>UC P C = FPiteratorOne \<Sigma>UC P C"
  apply(simp add: FPiteratorOneAlt_def FPiteratorOne_def)
  apply(rule_tac
      t="Enforce_Valid_DES C"
      and s="C"
      in ssubst)
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Valid_DES UNIVmap IsDES IsDES")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   apply(subgoal_tac "IsDES C = (Enforce_Valid_DES C = C)")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(blast)
   apply(force)
  apply(subgoal_tac "Enforce_Nonblockingness_DES C=C")
   prefer 2
   apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(erule conjE)+
   apply(blast)
  apply(simp add: ifcomp_def FPiteratorOne_def FPinit_def FPiteratorInit_def)
  done

theorem Coincidence_with_alternative_iterator_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES C
  \<Longrightarrow> DES_nonblockingness C
  \<Longrightarrow> FPiteratorMarkedAlt \<Sigma>UC P C = FPiteratorMarked \<Sigma>UC P C
  \<and> FPiteratorStarAlt \<Sigma>UC P C = FPiteratorStar \<Sigma>UC P C
  \<and> FPiteratorOneAlt \<Sigma>UC P C = FPiteratorOne \<Sigma>UC P C"
  apply (metis FPiterator_and_FPiteratorMarkedAlt_coincide FPiterator_and_FPiteratorOneAlt_coincide FPiterator_and_FPiteratorStarAlt_coincide)
  done

lemma Compute_Fixed_Point_Finite_coincides_for_FPiterator_and_FPiteratorMarkedAlt: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Q = predicate_AND IsDES DES_nonblockingness
  \<Longrightarrow> Compute_Fixed_Point_Finite n (FPiteratorMarkedAlt \<Sigma>UC P) (FPinit P S)
  = Compute_Fixed_Point_Finite n (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<and> Q (Compute_Fixed_Point_Finite n (FPiteratorMarkedAlt \<Sigma>UC P) (FPinit P S))"
  apply(unfold FPiteratorMarkedAlt_def FPiteratorMarked_def FPinit_def FPiteratorInit_def)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator (Enforce_Nonblockingness_DES\<circ>(\<lambda>C. Enforce_Specification_Satisfaction (inf P S) C)) IsDES X Y" for X Y)
   prefer 2
   apply(rule FPiteratorInit_is_Characteristic_Fixed_Point_Iterator)
    apply(force)
   apply(rule_tac
      t="inf P S"
      and s="infDES P S"
      in ssubst)
    apply (metis inf_DES_ext_def)
   apply(rule infDES_preserves_IsDES)
    apply(force)
   apply(force)
  apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and Qout="(predicate_AND IsDES DES_nonblockingness)"
      in EqualCompute_initial)
     apply(rename_tac C)(*strict*)
     prefer 4
     apply(force)
    apply(rename_tac C)(*strict*)
    prefer 3
    apply(subgoal_tac "(\<forall>X. IsDES X \<longrightarrow> (predicate_AND IsDES DES_nonblockingness) (Enforce_Nonblockingness_DES (Enforce_Specification_Satisfaction (inf P S) X)))")
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(erule_tac
      x="top"
      in allE)
    apply(erule impE)
     apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def prefix_closure_def prefix_def)
     apply(force)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(subgoal_tac "IsDES C \<and> DES_nonblockingness C")
    apply(rename_tac C)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Enforce_Valid_DES C"
      and s="C"
      in ssubst)
    apply(rename_tac C)(*strict*)
    apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Valid_DES UNIVmap IsDES IsDES")
     apply(rename_tac C)(*strict*)
     prefer 2
     apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
    apply(rename_tac C)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(erule conjE)+
    apply(erule_tac
      x="C"
      in allE)+
    apply(erule impE)
     apply(rename_tac C)(*strict*)
     apply(blast)
    apply(rename_tac C)(*strict*)
    apply(erule impE)
     apply(rename_tac C)(*strict*)
     apply(blast)
    apply(rename_tac C)(*strict*)
    apply(erule impE)
     apply(rename_tac C)(*strict*)
     apply(blast)
    apply(rename_tac C)(*strict*)
    apply(erule impE)
     apply(rename_tac C)(*strict*)
     apply(blast)
    apply(rename_tac C)(*strict*)
    apply(erule impE)
     apply(rename_tac C)(*strict*)
     apply(blast)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(subgoal_tac "Enforce_Nonblockingness_DES C=C")
    apply(rename_tac C)(*strict*)
    prefer 2
    apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
     apply(rename_tac C)(*strict*)
     prefer 2
     apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
    apply(rename_tac C)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(erule conjE)+
    apply(blast)
   apply(rename_tac C)(*strict*)
   apply(simp add: ifcomp_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule Compute_Fixed_Point_Finite_preserve_prop)
   apply(rename_tac n)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(erule conjE)+
   apply(erule_tac
      x="top"
      in allE)+
   apply(clarsimp)
   apply(simp add: topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac n X)(*strict*)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator X UNIVmap (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness)))) (predicate_AND IsDES DES_nonblockingness)" for X)
   apply(rename_tac n X)(*strict*)
   prefer 2
   apply(rule FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(rename_tac n X)(*strict*)
   apply(force)
  apply(rename_tac n X)(*strict*)
  apply(rename_tac n X)(*strict*)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def FPiteratorMarkedAlt_def)
  done

lemma Supremum_in_SCP_Controller_Least_Restrictive_Adapted_Specification: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S} \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator (\<lambda>C. Enforce_Specification_Satisfaction (inf P S) C) IsDES (predicate_AND IsDES (DES_specification_satisfied (inf P S))) (predicate_AND IsDES (DES_specification_satisfied (inf P S)))")
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
   apply(rule_tac
      t="inf P S"
      and s="infDES P S"
      in ssubst)
    apply (simp add: inf_DES_ext_def)
   apply(rule infDES_preserves_IsDES)
    apply(force)
   apply(force)
  apply(subgoal_tac "{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}={X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> inf P S}")
   prefer 2
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      s="x\<le>inf P S"
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      q="Enforce_Specification_Satisfaction (inf P S) top"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      q="Enforce_Nonblockingness_DES (Enforce_Specification_Satisfaction (inf P S) top)"
      in GFP_SOUND_le_trans)
      apply(rename_tac x)(*strict*)
      apply(unfold FPinit_def FPiteratorInit_def)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(subgoal_tac "(\<forall>X. IsDES X \<longrightarrow> Enforce_Nonblockingness_DES X \<le> X)")
      apply(rename_tac x)(*strict*)
      prefer 2
      apply(simp add: Characteristic_Fixed_Point_Iterator_def)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(erule_tac
      x="Enforce_Specification_Satisfaction (inf P S) top"
      in allE)
     apply(erule impE)
      apply(rename_tac x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(subgoal_tac "(\<forall>X::'a DES. IsDES X \<longrightarrow> IsDES (Enforce_Specification_Satisfaction (inf P S) X) \<and> DES_specification_satisfied (inf P S) (Enforce_Specification_Satisfaction (inf P S) X))")
      apply(rename_tac x)(*strict*)
      prefer 2
      apply(simp add: Characteristic_Fixed_Point_Iterator_def)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(erule_tac
      x="top"
      in allE)
     apply(erule impE)
      apply(rename_tac x)(*strict*)
      apply(simp add: SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def prefix_closure_def prefix_def)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      t="inf P S"
      and s="infDES P S"
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply (metis inf_DES_ext_def)
    apply(rename_tac x)(*strict*)
    apply(simp add: SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def prefix_closure_def prefix_def)
    apply(simp add: Enforce_Specification_Satisfaction_def)
    apply(clarsimp)
    apply(case_tac P)
    apply(rename_tac x fun1 fun2)(*strict*)
    apply(case_tac S)
    apply(rename_tac x fun1 fun2 fun1a fun2a)(*strict*)
    apply(clarsimp)
    apply(simp add: SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def IsDES_def prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="x"
      and s="Enforce_Nonblockingness_DES x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "x\<le>Enforce_Specification_Satisfaction (inf P S) top")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Enforce_Specification_Satisfaction_def)
    apply(rename_tac x)(*strict*)
    apply(rule Enforce_Nonblockingness_DES_mono)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule Enforce_Nonblockingness_DES_term)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(subgoal_tac "Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}\<le>P")
   prefer 2
   apply(rule_tac
      t="{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      and s="{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> inf P S}"
      in ssubst)
    apply(unfold FPinit_def FPiteratorInit_def)
    apply(force)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "{ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> Enforce_Nonblockingness_DES (Enforce_Specification_Satisfaction (inf P S) top))} = { (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)}")
  apply(simp only: SCP_Controller_Least_Restrictive_Direct_def SCP_Controller_Least_Restrictive_Adapted_Specification_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule Sup_DES_contained)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(simp add: SCP_Closed_Loop_Satisfactory_Direct_def)
  apply(rule order_antisym)
   prefer 2
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "x \<le> Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> P \<and> X \<le> S}")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(thin_tac "Sup ({ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)}) \<le> P")
   apply(thin_tac "DES_controllability \<Sigma>UC P x")
   apply(simp add: DES_specification_satisfied_def)
  apply(rule Sup_upper)
  apply(rule_tac
      t="inf (Sup ({ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)})) P"
      and s="(Sup ({ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)}))"
      in ssubst)
   apply(rule inf_absorb1)
   apply(force)
  apply(rule_tac
      t="{ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)}"
      and s="{ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> inf P S)}"
      in ssubst)
   apply(force)
  apply(thin_tac "Sup ({ (X::'a DES). (IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X \<and> X \<le> P \<and> X \<le> S)}) \<le> P")
  apply(thin_tac "Characteristic_Fixed_Point_Iterator (\<lambda>C::'a DES. Enforce_Specification_Satisfaction (inf P S) C) IsDES (\<lambda>C::'a DES. IsDES C \<and> DES_specification_satisfied (inf P S) C) (\<lambda>C::'a DES. IsDES C \<and> DES_specification_satisfied (inf P S) C)")
  apply(rule_tac
      t="{CL. IsDES CL \<and> CL \<le> P \<and> DES_controllability \<Sigma>UC P CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf P S) CL}"
      and s="{CL. IsDES CL \<and> DES_controllability \<Sigma>UC P CL \<and> DES_nonblockingness CL \<and> DES_specification_satisfied (inf P S) CL}"
      in ssubst)
   prefer 2
   apply(rule SCP_Controller_Least_Restrictive_Direct_contained)
    apply(force)
   apply(force)
  apply(rule antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: DES_specification_satisfied_def)
  done

lemma Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   prefer 2
   apply(rule Supremum_in_SCP_Controller_Least_Restrictive_Adapted_Specification)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="FPiteratorMarkedAlt \<Sigma>UC P"
      and Qout="(predicate_AND IsDES DES_nonblockingness)"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
      apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
       apply(rule spec_simplify)
      apply(unfold FPiteratorMarkedAlt_def)[1]
      apply(force)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(rule FPiterator_and_FPiteratorMarkedAlt_coincide)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(force)
   apply(rename_tac Ca)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(simp add: Enforce_Specification_Satisfaction_def)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(erule_tac
      x="inf P S"
      and P="\<lambda>X. IsDES X \<longrightarrow> IsDES (Enforce_Nonblockingness_DES X) \<and> DES_nonblockingness (Enforce_Nonblockingness_DES X)"
      in allE)
  apply(clarsimp)
  apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  done

lemma Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   prefer 2
   apply(rule Supremum_in_SCP_Controller_Least_Restrictive_Adapted_Specification)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorStarAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="FPiteratorStarAlt \<Sigma>UC P"
      and Qout="(predicate_AND IsDES DES_nonblockingness)"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
      apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
       apply(rule spec_simplify)
      apply(unfold FPiteratorStarAlt_def)[1]
      apply(force)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(rule FPiterator_and_FPiteratorStarAlt_coincide)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(force)
   apply(rename_tac Ca)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(simp add: Enforce_Specification_Satisfaction_def)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(erule_tac
      x="inf P S"
      and P="\<lambda>X. IsDES X \<longrightarrow> IsDES (Enforce_Nonblockingness_DES X) \<and> DES_nonblockingness (Enforce_Nonblockingness_DES X)"
      in allE)
  apply(clarsimp)
  apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  done

lemma Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   prefer 2
   apply(rule Supremum_in_SCP_Controller_Least_Restrictive_Adapted_Specification)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorOneAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="FPiteratorOneAlt \<Sigma>UC P"
      and Qout="(predicate_AND IsDES DES_nonblockingness)"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
      apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
       apply(rule spec_simplify)
      apply(unfold FPiteratorOneAlt_def)[1]
      apply(force)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(rule FPiterator_and_FPiteratorOneAlt_coincide)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(force)
   apply(rename_tac Ca)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(simp add: Enforce_Specification_Satisfaction_def)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator Enforce_Nonblockingness_DES IsDES (predicate_AND IsDES DES_nonblockingness) (predicate_AND IsDES DES_nonblockingness)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(erule_tac
      x="inf P S"
      and P="\<lambda>X. IsDES X \<longrightarrow> IsDES (Enforce_Nonblockingness_DES X) \<and> DES_nonblockingness (Enforce_Nonblockingness_DES X)"
      in allE)
  apply(clarsimp)
  apply (metis infDES_preserves_IsDES inf_DES_ext_def)
  done

theorem Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorOne)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<le> P"
  apply(subgoal_tac "IsDES top")
   prefer 2
   apply(simp add: FPinit_def FPiteratorInit_def FPiteratorMarked_def top_DES_ext_def topDES_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def IsDES_def prefix_closure_def prefix_def)
   apply(force)
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(force)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="Enforce_Nonblockingness_DES\<circ>(Enforce_Marked_Controllable_Subset \<Sigma>UC (des_langUM P))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
       apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
        apply(rule spec_simplify)
       apply(fold FPiteratorMarkedAlt_def)[1]
       apply(rule FPiteratorMarkedAlt_is_Characteristic_Fixed_Point_Iterator)
       apply(force)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(fold FPiteratorMarkedAlt_def)[1]
     apply(rule FPiterator_and_FPiteratorMarkedAlt_coincide)
      apply(rename_tac Ca)(*strict*)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(unfold FPiteratorMarkedAlt_def)[1]
    apply(force)
   apply(simp add: Fixed_Point_Iterator_def FPinit_def)
   apply(clarsimp)
   apply(force)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: Fixed_Point_Iterator_def)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: FPinit_def)
  apply(simp add: DES_specification_satisfied_def)
  apply(clarsimp)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<le> P"
  apply(subgoal_tac "IsDES top")
   prefer 2
   apply(simp add: FPinit_def FPiteratorInit_def FPiteratorMarked_def top_DES_ext_def topDES_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def IsDES_def prefix_closure_def prefix_def)
   apply(force)
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorStarAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(force)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="Enforce_Nonblockingness_DES\<circ>(Enforce_Star_Controllable_Subset \<Sigma>UC (des_langUM P))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
       apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
        apply(rule spec_simplify)
       apply(fold FPiteratorStarAlt_def)[1]
       apply(rule FPiteratorStarAlt_is_Characteristic_Fixed_Point_Iterator)
       apply(force)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(fold FPiteratorStarAlt_def)[1]
     apply(rule FPiterator_and_FPiteratorStarAlt_coincide)
      apply(rename_tac Ca)(*strict*)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(unfold FPiteratorStarAlt_def)[1]
    apply(force)
   apply(simp add: Fixed_Point_Iterator_def FPinit_def)
   apply(clarsimp)
   apply(force)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: Fixed_Point_Iterator_def)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: FPinit_def)
  apply(simp add: DES_specification_satisfied_def)
  apply(clarsimp)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<le> P"
  apply(subgoal_tac "IsDES top")
   prefer 2
   apply(simp add: FPinit_def FPiteratorInit_def FPiteratorMarked_def top_DES_ext_def topDES_def Enforce_Nonblockingness_DES_def Enforce_Specification_Satisfaction_def inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def IsDES_def prefix_closure_def prefix_def)
   apply(force)
  apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      in FPiteratorOneAlt_is_Characteristic_Fixed_Point_Iterator)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      S="S"
      and P="P"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(force)
   apply(force)
  apply(rule_tac
      t="Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)"
      and s="Sup{X. (\<lambda>C. IsDES C \<and> DES_controllability \<Sigma>UC P C \<and> DES_nonblockingness C) X \<and> X \<le> FPinit P S}"
      in ssubst)
   apply(rule_tac
      Qinp="(predicate_AND IsDES DES_nonblockingness)"
      and F="Enforce_Nonblockingness_DES\<circ>(Enforce_Controllable_Subset \<Sigma>UC (des_langUM P))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
       apply(rule_tac
      t="(\<lambda>X. IsDES X \<and> DES_controllability \<Sigma>UC P X \<and> DES_nonblockingness X)"
      and s="(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability \<Sigma>UC P))) (predicate_AND IsDES DES_nonblockingness))))"
      in subst)
        apply(rule spec_simplify)
       apply(fold FPiteratorOneAlt_def)[1]
       apply(rule FPiteratorOneAlt_is_Characteristic_Fixed_Point_Iterator)
       apply(force)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(fold FPiteratorOneAlt_def)[1]
     apply(rule FPiterator_and_FPiteratorOneAlt_coincide)
      apply(rename_tac Ca)(*strict*)
      apply(force)
     apply(rename_tac Ca)(*strict*)
     apply(force)
    apply(rename_tac Ca)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(unfold FPiteratorOneAlt_def)[1]
    apply(force)
   apply(simp add: Fixed_Point_Iterator_def FPinit_def)
   apply(clarsimp)
   apply(force)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in FPiteratorInit_is_Fixed_Point_Iterator)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: Fixed_Point_Iterator_def)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="top"
      in allE)
  apply(erule impE)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: FPinit_def)
  apply(simp add: DES_specification_satisfied_def)
  apply(clarsimp)
  apply(force)
  done

theorem Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<le> P"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(blast)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorOne)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_Properties_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Sum Sm)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "C \<le> P")
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      in ssubst)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(subgoal_tac "C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(thin_tac "C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, (Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC (DES Pum Pm)) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf (DES Pum Pm) (DES Sum Sm))) top) \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
  apply(rule context_conjI)
   apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply (metis SCP_Controller_Satisfactory_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
  done

lemma Compute_Fixed_Point_computes_Properties_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Sum Sm)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "C \<le> P")
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)"
      in ssubst)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorStar)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorStar)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(subgoal_tac "C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(thin_tac "C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, (Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point (FPiteratorStar \<Sigma>UC (DES Pum Pm)) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf (DES Pum Pm) (DES Sum Sm))) top) \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
  apply(rule context_conjI)
   apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply (metis SCP_Controller_Satisfactory_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
  done

lemma Compute_Fixed_Point_computes_Properties_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Sum Sm)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "C \<le> P")
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)"
      in ssubst)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorOne)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorOne)
      apply(rename_tac Pum Pm Sum Sm)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm)(*strict*)
   apply(force)
  apply(subgoal_tac "C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
   prefer 2
   apply(force)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(unfold FPinit_def FPiteratorInit_def)
  apply(thin_tac "C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, (Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf P S)) top)")
  apply(thin_tac "Compute_Fixed_Point (FPiteratorOne \<Sigma>UC (DES Pum Pm)) ((Enforce_Nonblockingness_DES \<circ> Enforce_Specification_Satisfaction (inf (DES Pum Pm) (DES Sum Sm))) top) \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC")
  apply(rule context_conjI)
   apply(simp add: SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Direct_def)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply(rule context_conjI)
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol SCP_UPsol_Is_Optimal)
  apply (metis SCP_Controller_Satisfactory_is_contained_in_SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller)
  done

theorem Compute_Fixed_Point_computes_Properties_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(blast)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorOne)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_SCP_UPSol_and_SCP_MPSol: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C1 \<in> SCP_UPsol P S \<Sigma>UC
  \<Longrightarrow> C2 \<in> SCP_MPsol P S \<Sigma>UC
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<and> C = C1
  \<and> C = C2"
  apply(case_tac P)
  apply(rename_tac set1 set2)(*strict*)
  apply(rename_tac Pum Pm)
  apply(rename_tac Pum Pm)(*strict*)
  apply(case_tac S)
  apply(rename_tac Pum Pm set1 set2)(*strict*)
  apply(rename_tac Sum Sm)
  apply(rename_tac Pum Pm Sum Sm)(*strict*)
  apply(case_tac C1)
  apply(rename_tac Pum Pm Sum Sm set1 set2)(*strict*)
  apply(rename_tac C1um C1m)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(rule conjI)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(rule_tac
      t="C"
      and s="Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)"
      in ssubst)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   prefer 2
   apply(rule_tac
      C="C"
      and P="P"
      and S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorMarked)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and C="C1"
      and P="P"
      and S="S"
      in Sound_Language_Computation)
       apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(simp add: SCP_UPsol_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and C="C2"
      and P="P"
      and S="S"
      in Sound_Language_Computation2)
       apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(simp add: SCP_MPsol_def)
  apply(simp add: inf_DES_ext_def infDES_def des_langUM_def des_langM_def lesseqDES_def lessDES_def less_eq_DES_ext_def less_DES_ext_def)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(subgoal_tac "C1=C2")
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in unique_SMSOL)
            apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(subgoal_tac "C=C1")
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   prefer 2
   apply(rule_tac
      \<Sigma>UC="\<Sigma>UC"
      and P="P"
      and S="S"
      in unique_SMSOL)
            apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
            apply(force)
           apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
           apply(force)
          apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
          apply(force)
         apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
         apply(force)
        apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
        apply(force)
       apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
       apply(force)
      apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
      apply(force)
     apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
     apply(force)
    apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
    apply(force)
   apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
   apply(force)
  apply(rename_tac Pum Pm Sum Sm C1um C1m)(*strict*)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC"
  apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked)
  done

lemma Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC"
  apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorStar Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorStar)
  done

lemma Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC"
  apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_is_contained_in_SCP_UPsol Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorOne Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorOne)
  done

theorem Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_UPsol P S \<Sigma>UC"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(blast)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorOne)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_Results_FPiteratorMarked: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorMarked \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorMarked \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<and> C \<le> P
  \<and> C \<in> SCP_UPsol P S \<Sigma>UC
  \<and> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_Results_FPiteratorStar: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorStar \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorStar \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<and> C \<le> P
  \<and> C \<in> SCP_UPsol P S \<Sigma>UC
  \<and> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_Results_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> C = Compute_Fixed_Point (FPiteratorOne \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (FPiteratorOne \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<and> C \<le> P
  \<and> C \<in> SCP_UPsol P S \<Sigma>UC
  \<and> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_UPsol_FPiteratorOne)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_Properties_FPiteratorOne)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_smaller_than_Plant_FPiteratorOne)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      P="P"
      and S="S"
      in Compute_Fixed_Point_computes_SCP_Controller_Least_Restrictive_Adapted_Specification_using_FPiteratorOne)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem Compute_Fixed_Point_Results_FPiteratorMarked_FPiteratorStar_FPiteratorOne: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C \<in> SCP_Controller_Least_Restrictive_Adapted_Specification P S \<Sigma>UC
  \<and> C \<le> P
  \<and> C \<in> SCP_UPsol P S \<Sigma>UC
  \<and> IsDES C
  \<and> C \<in> SCP_Controller_Satisfactory P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop P S \<Sigma>UC
  \<and> C \<in> SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller P S \<Sigma>UC"
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_Results_FPiteratorMarked)
      apply(force)
     apply(force)
    apply(blast)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      S="S"
      in Compute_Fixed_Point_Results_FPiteratorStar)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      S="S"
      in Compute_Fixed_Point_Results_FPiteratorOne)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem additional_property_on_minimality_satisfied: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F \<in> {FPiteratorMarked,FPiteratorStar,FPiteratorOne}
  \<Longrightarrow> C = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)
  \<Longrightarrow> Compute_Fixed_Point_dom (F \<Sigma>UC P, FPinit P S)
  \<Longrightarrow> C = Inf (SCP_Controller_Least_Restrictive P S \<Sigma>UC)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Compute_Fixed_Point_Results_FPiteratorMarked_FPiteratorStar_FPiteratorOne)
       prefer 5
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "C \<in> SCP_Controller_Least_Restrictive P S \<Sigma>UC")
   prefer 2
   apply (metis SCP_Controller_Least_Restrictive_Adapted_Specification_def SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive SCP_Controller_Least_Restrictive_Simplified_is_equal_to_SCP_Controller_Least_Restrictive_Direct SCP_Controller_Least_Restrictive__with_adapted_specification_is_equal_to__SCP_Controller_Least_Restrictive)
  apply(clarsimp)
  apply(simp add: SCP_Controller_Satisfactory_Maximal_Closed_Loop_Minimal_Controller_def)
  apply(rule antisym)
   prefer 2
   apply(rule Inf_lower)
   apply(simp add: SCP_Controller_Least_Restrictive_def)
   apply(clarsimp)
  apply(rule Inf_greatest)
  apply(simp add: SCP_Controller_Least_Restrictive_def)
  apply(clarsimp)
  apply(subgoal_tac "inf (Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)) P = Compute_Fixed_Point (F \<Sigma>UC P) (FPinit P S)")
   prefer 2
   apply (metis inf.absorb2 inf.commute)
  apply(clarsimp)
  apply (metis inf_le1)
  done

end
