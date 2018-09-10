section {*basic*}
theory
  basic

imports
  CONFIG

begin

(*AN EXAMPLE IN THE THESIS*)
lemma "p \<Longrightarrow> q \<Longrightarrow> p \<and> q \<longrightarrow> s \<Longrightarrow> s"
  apply(rule_tac P="p\<and>q" and Q="s" in mp)
   apply(assumption)
  apply(rule_tac P="p" and Q="q" in conjI)
   apply(assumption)
  apply(assumption)
  done

lemma prop_max: "
  (a \<ge> b \<Longrightarrow> P a)
  \<Longrightarrow> (b \<ge> a \<Longrightarrow> P b)
  \<Longrightarrow> P (max a (b::nat))"
  apply(case_tac "a \<ge> b")
   apply(rule_tac
      t = "max a b"
      and s = "a"
      in ssubst)
    apply(rule Orderings.max_absorb1)
    apply(force)
   apply(force)
  apply(rule_tac
      t = "max a b"
      and s = "b"
      in ssubst)
   apply(rule Orderings.max_absorb2)
   apply(force)
  apply(force)
  done

lemma prop_min: "
  (a \<ge> b \<Longrightarrow> P b)
  \<Longrightarrow> (b \<ge> a \<Longrightarrow> P a)
  \<Longrightarrow> P (min a (b::nat))"
  apply(case_tac "a \<ge> b")
   apply(rule_tac
      t = "min a b"
      and s = "b"
      in ssubst)
    apply(rule Orderings.min_absorb2)
    apply(force)
   apply(force)
  apply(rule_tac
      t = "min a b"
      and s = "a"
      in ssubst)
   apply(rule Orderings.min_absorb1)
   apply(force)
  apply(force)
  done

lemma nat_le_step: "
  a \<ge> x
  \<Longrightarrow> b \<ge> y
  \<Longrightarrow> a - x \<le> b - (y::nat)
  \<Longrightarrow> a + c = b
  \<Longrightarrow> y \<le> x + c"
  apply(arith)
  done

lemma ex_least_nat_le_prime: "
  P (n::nat)
  \<Longrightarrow> \<exists>k \<le> n. (\<forall>i < k. \<not> P i) \<and> P k"
  apply(case_tac "P 0")
   defer
   apply(rule ex_least_nat_le)
    apply(force)
   apply(force)
  apply(rule_tac
      x = "0"
      in exI)
  apply(clarsimp)
  done

lemma universal_by_not_exists_contra: "
  (\<And>i. i \<le> k \<Longrightarrow> \<not> P i \<Longrightarrow> (\<forall>j < i. P j) \<Longrightarrow> False)
  \<Longrightarrow> \<forall>i \<le> k. P (i::nat)"
  apply(rule ccontr)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      P = "\<lambda>x. \<not> P x"
      and n = "i"
      in ex_least_nat_le_prime)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ka)(*strict*)
  apply(erule_tac
      x = "ka"
      in meta_allE)
  apply(force)
  done

lemma property_preseved_under_steps_is_invariant2_prime: "
  P m
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<forall>i. m \<le> i \<and> i < m + n \<longrightarrow> (P i \<longrightarrow> P (Suc i))
  \<Longrightarrow> P x"
  apply(induct x)
   apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "m = Suc x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma case_tac_to_disj: "
  D
  \<Longrightarrow> A \<and> D \<longrightarrow> B
  \<Longrightarrow> A \<longleftrightarrow> \<not> C
  \<Longrightarrow> (A \<longrightarrow> B) \<and> (C \<longrightarrow> D)"
  apply(auto)
  done

lemma uniqueI: "
  \<exists>x. P x \<and> (\<forall> y. P y \<longrightarrow> x = y)
  \<Longrightarrow> \<exists>!x. P x"
  apply(auto)
  done

lemma uniqueE: "
  \<exists>!x. P x
  \<Longrightarrow> \<exists>x. P x \<and> (\<forall> y. P y \<longrightarrow> x = y)"
  apply(auto)
  done

lemma elimITE: "
  (if P then None else Some x) = Some y
  \<Longrightarrow> \<not> P"
  apply(case_tac P)
   apply(force)
  apply(force)
  done

lemma elimITE2: "
  (if P then None else Some x) = Some y
  \<Longrightarrow> x = y"
  apply(case_tac P)
   apply(force)
  apply(force)
  done

lemma MetaMP: "
  Q
  \<Longrightarrow> Q \<Longrightarrow> R
  \<Longrightarrow> R"
  apply(auto)
  done

lemma TriCirc: "
  A \<longrightarrow> B
  \<Longrightarrow> B \<longrightarrow> C
  \<Longrightarrow> C \<longrightarrow> A
  \<Longrightarrow> A \<longleftrightarrow> B \<and> B \<longleftrightarrow> C \<and> C \<longleftrightarrow> A"
  apply(blast)
  done

lemma aequI: "
  p \<longrightarrow> q 
  \<Longrightarrow> q \<longrightarrow> p 
  \<Longrightarrow> p \<longleftrightarrow> q"
  apply(auto)
  done

lemma propSym: "
  A \<and> B
  \<Longrightarrow> B \<and> A"
  apply(auto)
  done

lemma unequal_maps_differ_somewhere: "
  f \<noteq> g
  \<Longrightarrow> \<exists>x. f x \<noteq> g x"
  apply(case_tac "\<exists>x. f x \<noteq> g x")
   apply(blast)
  apply(subgoal_tac "f = g")
   apply(blast)
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(blast)
  done

lemma meta_modus_ponens: "
  P
  \<Longrightarrow> (P \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  apply(auto)
  done

lemma equal_unique: "
  P = Q
  \<Longrightarrow> \<exists>!x. Q x
  \<Longrightarrow> \<exists>!x. P x"
  apply(force)
  done

lemma monotonicSelector: "
  \<forall>e. ((\<forall>(i::nat) j. i < j \<and> j \<le> e \<longrightarrow> f i \<ge> f j) \<longrightarrow> (\<forall>d::nat. f 0 \<ge> d \<and> f e \<le> d \<longrightarrow> (\<exists>!(k::nat). k \<le> e \<and> (\<forall>l \<le> k. f l \<ge> d) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < d))))"
  apply(rule allI)
  apply(rename_tac e)(*strict*)
  apply(induct_tac e)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rule HOL.ex_ex1I)
    apply(rule_tac
      x = "0"
      in exI)
    apply(simp)
   apply(rename_tac k y)(*strict*)
   apply(simp)
  apply(rename_tac e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d)(*strict*)
  apply(erule_tac
      x = "d"
      and P = "\<lambda>d. d \<le> f 0 \<and> f n \<le> d \<longrightarrow> (\<exists>!k. k \<le> n \<and> (\<forall>l \<le> k. d \<le> f l) \<and> (\<forall>l>k. l \<le> n \<longrightarrow> f l < d))"
      in allE)
  apply(rename_tac n d)(*strict*)
  apply(clarsimp)
  apply(case_tac "f n < d")
   apply(rename_tac n d)(*strict*)
   apply(erule impE)
    apply(rename_tac n d)(*strict*)
    apply(arith)
   apply(rename_tac n d)(*strict*)
   apply(erule HOL.ex1E)
   apply(rename_tac n d k)(*strict*)
   apply(rule HOL.ex_ex1I)
    apply(rename_tac n d k)(*strict*)
    apply(rule_tac
      x = "k"
      in exI)
    apply(erule conjE) +
    apply(rule conjI)
     apply(rename_tac n d k)(*strict*)
     apply(arith)
    apply(rename_tac n d k)(*strict*)
    apply(rule conjI)
     apply(rename_tac n d k)(*strict*)
     apply(blast)
    apply(rename_tac n d k)(*strict*)
    apply(rule allI)
    apply(rename_tac n d k l)(*strict*)
    apply(erule_tac
      x = "l"
      and P = "\<lambda>l. k < l \<longrightarrow> l \<le> n \<longrightarrow> f l < d"
      in allE)
    apply(rule impI)
    apply(rule impI)
    apply(erule impE)
     apply(rename_tac n d k l)(*strict*)
     apply(blast)
    apply(rename_tac n d k l)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "l = Suc n")
     apply(rename_tac n d k l)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d k)(*strict*)
     apply(erule_tac
      x = "n"
      and P = "\<lambda>i. \<forall>j. i < j \<and> j \<le> Suc n \<longrightarrow> f j \<le> f i"
      in allE)
     apply(erule_tac
      x = "Suc n"
      and P = "\<lambda>j. n < j \<and> j \<le> Suc n \<longrightarrow> f j \<le> f n"
      in allE)
     apply(clarsimp)
    apply(rename_tac n d k l)(*strict*)
    apply(arith)
   apply(rename_tac n d k ka y)(*strict*)
   apply(erule conjE) +
   apply(rule_tac
      Q = "False"
      in contrapos_np)
    apply(rename_tac n d k ka y)(*strict*)
    apply(blast)
   apply(rename_tac n d k ka y)(*strict*)
   apply(case_tac "ka < y")
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule_tac
      x = "Suc ka"
      and P = "\<lambda>x. x \<le> y \<longrightarrow> d \<le> f x"
      in allE)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule_tac
      x = "Suc ka"
      and P = "\<lambda>x. ka < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < d"
      in allE)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(arith)
   apply(rename_tac n d k ka y)(*strict*)
   apply(subgoal_tac "y < ka")
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. x \<le> ka \<longrightarrow> d \<le> f x"
      in allE)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. y < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < d"
      in allE)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(erule impE)
     apply(rename_tac n d k ka y)(*strict*)
     apply(arith)
    apply(rename_tac n d k ka y)(*strict*)
    apply(arith)
   apply(rename_tac n d k ka y)(*strict*)
   apply(arith)
  apply(rename_tac n d)(*strict*)
  apply(subgoal_tac "f n \<ge> d")
   apply(rename_tac n d)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(arith)
  apply(rename_tac n d)(*strict*)
  apply(case_tac "f (Suc n) < d")
   apply(rename_tac n d)(*strict*)
   apply(rule HOL.ex_ex1I)
    apply(rename_tac n d)(*strict*)
    apply(rule_tac
      x = "n"
      in exI)
    apply(rule conjI)
     apply(rename_tac n d)(*strict*)
     apply(arith)
    apply(rename_tac n d)(*strict*)
    apply(rule conjI)
     apply(rename_tac n d)(*strict*)
     apply(rule allI)
     apply(rename_tac n d l)(*strict*)
     apply(rule impI)
     apply(subgoal_tac "f n \<le> f l")
      apply(rename_tac n d l)(*strict*)
      apply(arith)
     apply(rename_tac n d l)(*strict*)
     apply(case_tac "n = l")
      apply(rename_tac n d l)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d l)(*strict*)
     apply(erule_tac
      x = "l"
      in allE)
     apply(erule_tac
      x = "n"
      in allE)
     apply(erule_tac
      P = "l < n \<and> n \<le> Suc n"
      in impE)
      apply(rename_tac n d l)(*strict*)
      apply(rule conjI)
       apply(rename_tac n d l)(*strict*)
       apply(arith)
      apply(rename_tac n d l)(*strict*)
      apply(arith)
     apply(rename_tac n d l)(*strict*)
     apply(simp)
    apply(rename_tac n d)(*strict*)
    apply(rule allI)
    apply(rename_tac n d l)(*strict*)
    apply(rule impI)
    apply(rule impI)
    apply(clarsimp)
    apply(subgoal_tac "Suc n = l")
     apply(rename_tac n d l)(*strict*)
     apply(force)
    apply(rename_tac n d l)(*strict*)
    apply(arith)
   apply(rename_tac n d k y)(*strict*)
   apply(erule conjE) +
   apply(rule_tac
      Q = "False"
      in contrapos_np)
    apply(rename_tac n d k y)(*strict*)
    apply(blast)
   apply(rename_tac n d k y)(*strict*)
   apply(case_tac "k < y")
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>x. x \<le> y \<longrightarrow> d \<le> f x"
      in allE)
    apply(erule_tac
      P = "Suc k \<le> y"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>x. k < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < d"
      in allE)
    apply(erule_tac
      P = "k < Suc k"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      P = "Suc k \<le> Suc n"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(arith)
   apply(rename_tac n d k y)(*strict*)
   apply(subgoal_tac "y < k")
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. x \<le> k \<longrightarrow> d \<le> f x"
      in allE)
    apply(erule_tac
      P = "Suc y \<le> k"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. y < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < d"
      in allE)
    apply(erule_tac
      P = "y < Suc y"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(erule_tac
      P = "Suc y \<le> Suc n"
      in impE)
     apply(rename_tac n d k y)(*strict*)
     apply(arith)
    apply(rename_tac n d k y)(*strict*)
    apply(arith)
   apply(rename_tac n d k y)(*strict*)
   apply(arith)
  apply(rename_tac n d)(*strict*)
  apply(subgoal_tac "f (Suc n) = d")
   apply(rename_tac n d)(*strict*)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rename_tac n d)(*strict*)
   apply(arith)
  apply(rename_tac n)(*strict*)
  apply(rule HOL.ex_ex1I)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      x = "Suc n"
      in exI)
   apply(rule conjI)
    apply(rename_tac n)(*strict*)
    apply(arith)
   apply(rename_tac n)(*strict*)
   apply(rule conjI)
    apply(rename_tac n)(*strict*)
    apply(rule allI)
    apply(rename_tac n l)(*strict*)
    apply(rule impI)
    apply(case_tac "Suc n = l")
     apply(rename_tac n l)(*strict*)
     apply(clarsimp)
    apply(rename_tac n l)(*strict*)
    apply(erule_tac
      x = "l"
      in allE)
    apply(erule_tac
      x = "Suc n"
      in allE)
    apply(erule_tac
      P = "l < Suc n \<and> Suc n \<le> Suc n"
      in impE)
     apply(rename_tac n l)(*strict*)
     apply(rule conjI)
      apply(rename_tac n l)(*strict*)
      apply(arith)
     apply(rename_tac n l)(*strict*)
     apply(arith)
    apply(rename_tac n l)(*strict*)
    apply(simp)
   apply(rename_tac n)(*strict*)
   apply(rule allI)
   apply(rename_tac n l)(*strict*)
   apply(rule impI)
   apply(rule impI)
   apply(clarsimp)
  apply(rename_tac n k y)(*strict*)
  apply(erule conjE) +
  apply(rule_tac
      Q = "False"
      in contrapos_np)
   apply(rename_tac n k y)(*strict*)
   apply(blast)
  apply(rename_tac n k y)(*strict*)
  apply(case_tac "k < y")
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>x. x \<le> y \<longrightarrow> f (Suc n) \<le> f x"
      in allE)
   apply(erule_tac
      P = "Suc k \<le> y"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      x = "Suc k"
      and P = "\<lambda>x. k < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < f (Suc n)"
      in allE)
   apply(erule_tac
      P = "k < Suc k"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      P = "Suc k \<le> Suc n"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(arith)
  apply(rename_tac n k y)(*strict*)
  apply(subgoal_tac "y < k")
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. x \<le> k \<longrightarrow> f (Suc n) \<le> f x"
      in allE)
   apply(erule_tac
      P = "Suc y \<le> k"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      x = "Suc y"
      and P = "\<lambda>x. y < x \<longrightarrow> x \<le> Suc n \<longrightarrow> f x < f (Suc n)"
      in allE)
   apply(erule_tac
      P = "y < Suc y"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(erule_tac
      P = "Suc y \<le> Suc n"
      in impE)
    apply(rename_tac n k y)(*strict*)
    apply(arith)
   apply(rename_tac n k y)(*strict*)
   apply(arith)
  apply(rename_tac n k y)(*strict*)
  apply(arith)
  done

lemma monotonicSelector2: "
  \<forall>(i::nat) j. i < j \<and> j \<le> e \<longrightarrow> f i \<ge> f j
  \<Longrightarrow> f 0 \<ge> d
  \<Longrightarrow> f e \<le> (d::nat)
  \<Longrightarrow> \<exists>!(k::nat). k \<le> e \<and> (\<forall>l \<le> k. f l \<ge> d) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> (\<not>(d \<le> f l)))"
  apply(subgoal_tac "\<exists>!k. k \<le> e \<and> (\<forall>l \<le> k. d \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < d)")
   prefer 2
   apply(rule_tac
      P = "f 0 \<ge> d \<and> f e \<le> d"
      and Q = "\<exists>!k. k \<le> e \<and> (\<forall>l \<le> k. d \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < d)"
      in impE)
     prefer 3
     apply(simp)
    prefer 2
    apply(simp)
   apply(rule_tac
      x = "d"
      and P = "\<lambda>d. d \<le> f 0 \<and> f e \<le> d \<longrightarrow> (\<exists>!k. k \<le> e \<and> (\<forall>l \<le> k. d \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < d))"
      in allE)
    prefer 2
    apply(simp)
   apply(rule_tac
      P = "\<forall>i j. i < j \<and> j \<le> e \<longrightarrow> f j \<le> f i"
      and Q = "\<forall>x. x \<le> f 0 \<and> f e \<le> x \<longrightarrow> (\<exists>!k. k \<le> e \<and> (\<forall>l \<le> k. x \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < x))"
      in impE)
     prefer 3
     apply(simp)
    prefer 2
    apply(simp)
   apply(rule_tac
      x = "e"
      and P = "\<lambda>e. (\<forall>i j. i < j \<and> j \<le> e \<longrightarrow> f j \<le> f i) \<longrightarrow> (\<forall>x. x \<le> f 0 \<and> f e \<le> x \<longrightarrow> (\<exists>!k. k \<le> e \<and> (\<forall>l \<le> k. x \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < x)))"
      in allE)
    prefer 2
    apply(simp)
   apply(rule_tac
      f = "f"
      in monotonicSelector)
  apply(rule_tac
      Q = "\<lambda>k. k \<le> e \<and> (\<forall>l \<le> k. d \<le> f l) \<and> (\<forall>l>k. l \<le> e \<longrightarrow> f l < d)"
      in equal_unique)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rename_tac x k l)(*strict*)
    apply(erule_tac
      x = "l"
      and P = "\<lambda>l. l \<le> k \<longrightarrow> d \<le> f l"
      in allE)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule le_boolI')
   apply(rule impI)
   apply(erule conjE) +
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule allI)
   apply(rename_tac x l)(*strict*)
   apply(rule impI) +
   apply(subgoal_tac "f l < d")
    apply(rename_tac x l)(*strict*)
    apply(force)
   apply(rename_tac x l)(*strict*)
   apply(erule_tac
      x = "l"
      and P = "\<lambda>l. \<forall>j. l < j \<and> j \<le> e \<longrightarrow> f j \<le> f l"
      in allE)
   apply(force)
  apply(force)
  done

lemma ignore_case_distinction: "
  B
  \<Longrightarrow> A \<or> C
  \<Longrightarrow> (A \<longrightarrow> B) \<and> (C \<longrightarrow> B)"
  apply(force)
  done

lemma ex1UseUnique: "
  \<exists>!x. P x
  \<Longrightarrow> P b
  \<Longrightarrow> P c
  \<Longrightarrow> b = c"
  apply(auto)
  done

lemma BEST_INDUCT: "
  \<forall>x. f x = 0 \<longrightarrow> P x
  \<Longrightarrow> \<forall>k < n. (\<forall>x. f x \<le> k \<longrightarrow> P x) \<longrightarrow> (\<forall>x. f x = Suc k \<longrightarrow> P x)
  \<Longrightarrow> f a = (n::nat)
  \<Longrightarrow> P a"
  apply(subgoal_tac "\<forall>l. l \<le> n \<longrightarrow> (\<forall>x. f x \<le> l \<longrightarrow> P x)")
   apply(force)
  apply(rule allI)
  apply(rename_tac l)(*strict*)
  apply(induct_tac l)
   apply(rename_tac l)(*strict*)
   apply(clarsimp)
  apply(rename_tac l na)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x)(*strict*)
  apply(erule_tac
      x = "n"
      in allE)
  apply(clarsimp)
  apply(case_tac "f x = Suc n")
   apply(rename_tac n x)(*strict*)
   apply(erule_tac
      x = "x"
      and P = "\<lambda>x. f x = Suc n \<longrightarrow> P x"
      in allE)
   apply(force)
  apply(rename_tac n x)(*strict*)
  apply(erule_tac
      x = "x"
      and P = "\<lambda>x. f x \<le> n \<longrightarrow> P x"
      in allE)
  apply(force)
  done

lemma BEST_INDUCT2: "
  \<forall>k \<le> n. ((\<forall>x. \<forall>l < k. x  \<in> f l \<longrightarrow> P x) \<longrightarrow> (\<forall>x. \<forall>l \<le> k. x  \<in> f l \<longrightarrow> P x))
  \<Longrightarrow> a  \<in> (f (n::nat))
  \<Longrightarrow> P a"
  apply(subgoal_tac "\<forall>l. l \<le> n \<longrightarrow> (\<forall>x. \<forall>m \<le> l. x  \<in> f m \<longrightarrow> P x)")
   apply(force)
  apply(rule allI)
  apply(rename_tac l)(*strict*)
  apply(induct_tac l)
   apply(rename_tac l)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x = "0"
      in allE)
   apply(clarsimp)
  apply(rename_tac l na)(*strict*)
  apply(rule impI) +
  apply(rule allI) +
  apply(rename_tac l na x m)(*strict*)
  apply(rule impI) +
  apply(case_tac "m \<le> na")
   apply(rename_tac l na x m)(*strict*)
   apply(erule impE)
    apply(rename_tac l na x m)(*strict*)
    apply(arith)
   apply(rename_tac l na x m)(*strict*)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule_tac
      x = "m"
      and P = "\<lambda>m. m \<le> na \<longrightarrow> x  \<in> f m \<longrightarrow> P x"
      in allE)
   apply(erule impE)
    apply(rename_tac l na x m)(*strict*)
    apply(arith)
   apply(rename_tac l na x m)(*strict*)
   apply(force)
  apply(rename_tac l na x m)(*strict*)
  apply(subgoal_tac "m = Suc na")
   apply(rename_tac l na x m)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac l na x m)(*strict*)
  apply(thin_tac "\<not> m \<le> na")
  apply(thin_tac "m \<le> Suc na")
  apply(erule_tac
      x = "m"
      in allE)
  apply(erule_tac
      P = "m \<le> n"
      in impE)
   apply(rename_tac l na x m)(*strict*)
   apply(arith)
  apply(rename_tac l na x m)(*strict*)
  apply(erule_tac
      P = "\<forall>x l. l < m \<longrightarrow> x  \<in> f l \<longrightarrow> P x"
      in impE)
   apply(rename_tac l na x m)(*strict*)
   apply(erule impE)
    apply(rename_tac l na x m)(*strict*)
    apply(arith)
   apply(rename_tac l na x m)(*strict*)
   apply(rule allI) +
   apply(rename_tac l na x m xa la)(*strict*)
   apply(erule_tac
      x = "xa"
      in allE)
   apply(erule_tac
      x = "la"
      in allE)
   apply(rule impI) +
   apply(erule impE)
    apply(rename_tac l na x m xa la)(*strict*)
    apply(arith)
   apply(rename_tac l na x m xa la)(*strict*)
   apply(erule impE)
    apply(rename_tac l na x m xa la)(*strict*)
    apply(arith)
   apply(rename_tac l na x m xa la)(*strict*)
   apply(force)
  apply(rename_tac l na x m)(*strict*)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule_tac
      x = "m"
      in allE)
  apply(force)
  done

lemma applyFunctionBack: "
  d1 = d2
  \<Longrightarrow> f d1 = a
  \<Longrightarrow> f d2 = b
  \<Longrightarrow> a = b"
  apply(blast)
  done

lemma XXXsmaller: "
  a \<ge> b
  \<Longrightarrow> a \<ge> c
  \<Longrightarrow> a - b \<le> a - c
  \<Longrightarrow> c \<le> (b::nat)"
  apply(arith)
  done

lemma wlogNatProp: "
   (\<And>x y. P x y \<Longrightarrow> P y x)
  \<Longrightarrow> (\<And>x y. x \<le> y \<Longrightarrow> P x y \<Longrightarrow> y \<le> x)
  \<Longrightarrow> P x y
  \<Longrightarrow> x = (y::nat)"
  apply(case_tac "x \<le> y")
   apply(rule order_antisym)
    apply(blast)
   apply(force)
  apply(case_tac "y \<le> x")
   apply(rule order_antisym)
    apply(force)
   apply(force)
  apply(arith)
  done

lemma THE_eq_prop: "
  \<exists>!y. P y
  \<Longrightarrow> (THE y. P y) = z
  \<Longrightarrow> P z"
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(rule HOL.theI')
  apply(force)
  done

lemma THE_default_ex1I: "
  THE_default a P = b
  \<Longrightarrow> a \<noteq> b
  \<Longrightarrow> \<exists>!x. P x"
  apply(case_tac "\<exists>!x. P x")
   apply(blast)
  apply(subgoal_tac "THE_default a P = a")
   apply(force)
  apply(rule Fun_Def.THE_default_none)
  apply(blast)
  done

lemma trivNat: "
  \<not> n < i
  \<Longrightarrow> i \<le> (n::nat)"
  apply(auto)
  done

lemma less_eq_Suc_le_raw: "
  (<) = (\<lambda>n. (\<le>) (Suc (n::nat)))"
  apply(rule ext)
  apply(rename_tac n)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma Some_inj: "
  Some x=Some y
  \<Longrightarrow> x=y"
  apply(force)
  done

lemma ex_least_nat_le_prime_prime: "
  P (n::nat)
  \<Longrightarrow> x\<le>n
  \<Longrightarrow> \<exists>k. x\<le>k \<and> k\<le>n \<and> P k \<and> (\<forall>i. x\<le>i \<and> i<k \<longrightarrow> (\<not>(P i)))"
  apply(subgoal_tac "\<exists>k\<le>n. (\<forall>i<k. \<not> P i) \<and> P k" for n P)
   prefer 2
   apply(rule_tac
      P="\<lambda>n. P (x+n)"
      and n="n-x"
      in ex_least_nat_le_prime)
   apply(force)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(subgoal_tac "k+x\<le>n")
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      x="k+x"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      t="k+x"
      and s="x+k"
      in ssubst)
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k i)(*strict*)
  apply(erule_tac
      x="i-x"
      in allE)
  apply(force)
  done

lemma min_alt: "
  (min (a::nat) b = a \<and> a \<le> b) \<or> (min a b = b \<and> b \<le> a)"
  apply(case_tac "a\<le>b")
   apply(rule disjI1)
   apply(rule conjI)
    apply(arith)
   apply(force)
  apply(rule disjI2)
  apply(rule conjI)
   apply(arith)
  apply(force)
  done

lemma to_mutual_sub1: "
  a \<le> c + b - d 
  \<Longrightarrow> a - b \<le> c - (d::nat)"
  apply(force)
  done

lemma to_mutual_sub2: "
  a + b - c \<le> (k::nat)
  \<Longrightarrow> a - c \<le> k - b"
  apply(force)
  done

lemma mutual_sub_to_add: "
  a - d \<le> c - b
  \<Longrightarrow> d \<le> a
  \<Longrightarrow> b \<le> c
  \<Longrightarrow> a + b \<le> c + (d::nat)"
  apply(force)
  done

lemma less_delta_exists: "
  x < y
  \<Longrightarrow> \<exists>k. x + Suc k = y"
  apply(metis add_Suc_right less_iff_Suc_add)
  done

lemma leq_delta_exists: "
  x \<le> (y::nat)
  \<Longrightarrow> \<exists>k. x + k = y"
  apply(rule_tac
      x = "y - x"
      in exI)
  apply(force)
  done

lemma induct01: "
  P 0
  \<Longrightarrow> P (Suc 0)
  \<Longrightarrow> (\<And>n. n>0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n))
  \<Longrightarrow> P m"
  apply(induct_tac m)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(case_tac "n = 0")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma Max_in_Prop: "
  finite A
  \<Longrightarrow> A \<noteq> {}
  \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P x)
  \<Longrightarrow> P (Max A)"
  apply (metis Max_in)
  done

lemma ex_max_limited: "
  P (x::nat)
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> \<exists>k \<le> n. P k \<and> (\<forall>k'. k < k' \<and> k' \<le> n \<longrightarrow> \<not> (P k'))"
  apply(rule_tac
      x = "Max {x. P x \<and> x \<le> n}"
      in exI)
  apply(subgoal_tac "finite {x. P x \<and> x \<le> n}")
   apply(subgoal_tac "{x. P x \<and> x \<le> n} \<noteq> {}")
    apply(rule conjI)
     apply(simp)
    apply(rule conjI)
     apply(simp)
     apply(clarsimp)
     apply(rename_tac xa)(*strict*)
     apply (rule Max_in_Prop)
       apply(rename_tac xa)(*strict*)
       apply(force)
      apply(rename_tac xa)(*strict*)
      apply(force)
     apply(rename_tac xa xaa)(*strict*)
     apply(force)
    apply(clarsimp)
    apply(rename_tac xa k')(*strict*)
    apply(erule_tac
      x = "k'"
      in allE)
    apply(force)
   apply (metis Collect_empty_eq)
  apply (metis finite_Collect_conjI finite_Collect_le_nat)
  done

lemma ex_max_limited_prime: "
  P (n::nat) 
  \<Longrightarrow> (\<forall>k > m. \<not> (P k)) 
  \<Longrightarrow> (\<exists>x. n \<le> x \<and> x \<le> m \<and> P x \<and> (\<forall>x'. x < x' \<longrightarrow> \<not> P x'))"
  apply(subgoal_tac "\<exists>k\<le>n. P k \<and> (\<forall>k'. k < k' \<and> k' \<le> n \<longrightarrow> \<not> P k')" for n P)
   prefer 2
   apply(rule_tac
      P="\<lambda>x. P x"
      and x="n"
      and n="m"
      in ex_max_limited)
    apply(force)
   apply(case_tac "n\<le>m")
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      x="k"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac k)(*strict*)
   apply(case_tac "n\<le>k")
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(erule_tac
      x="n"
      and P="\<lambda>n. m < n \<longrightarrow> \<not> P n"
      in allE)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k x')(*strict*)
  apply(erule_tac
      x="x'"
      and P="\<lambda>x'. m < x' \<longrightarrow> \<not> P x'"
      in allE)
  apply(clarsimp)
  done

lemma someI_eq: "
  P a 
  \<Longrightarrow> (\<And>y1 y2. P y1 \<Longrightarrow> P y2 \<Longrightarrow> y1 = y2)
  \<Longrightarrow> (SOME x. P x) = a"
  apply(rule someI2)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma theI_unique_existence: "
  \<exists>! x. P x 
  \<Longrightarrow> \<exists>x. x = (THE x. P x) \<and> P x"
  apply (metis theI)
  done

lemma someI_existence: "
  \<exists>x. P x 
  \<Longrightarrow> \<exists>x. x = (SOME x. P x) \<and> P x"
  apply (metis someI)
  done

lemma ex_ex1I_double: "
  \<exists>x y. P x y
  \<Longrightarrow> (\<And>x1 y1 x2 y2. P x1 y1 \<Longrightarrow> P x2 y2 \<Longrightarrow> x1=x2 \<and> y1=y2)
  \<Longrightarrow> \<exists>!x. \<exists>! y. P x y"
  apply(metis)
  done

lemma nat_induct_border: "
  P 0
  \<Longrightarrow> (\<And>n. Suc n \<le> m \<Longrightarrow> P n \<Longrightarrow> P (Suc n))
  \<Longrightarrow> i \<le> m
  \<Longrightarrow> P i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  done

lemma nat_induct_border_prime: "
  P X
  \<Longrightarrow> (\<And>n. Suc n \<le> X \<Longrightarrow> x \<le> n \<Longrightarrow> P (Suc n) \<Longrightarrow> P n)
  \<Longrightarrow> i \<le> X
  \<Longrightarrow> x \<le> i
  \<Longrightarrow> P i"
  apply(induct "X-i" arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa i)(*strict*)
  apply(clarsimp)
  done

lemma ex1_eq: "
  \<exists>!x. \<exists>!y. P x y
  \<Longrightarrow> (\<forall>x y. P x y \<longleftrightarrow> Q x y)
  \<Longrightarrow> \<exists>!x. \<exists>! y. Q x y"
  apply(metis)
  done

lemma twoUnique_to_oneUnique: "
  \<exists>!x. \<exists>!y. P x y
  \<Longrightarrow> (\<And>x y. P x y \<longleftrightarrow> Q x)
  \<Longrightarrow> \<exists>!x. Q x"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule ex_ex1I)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x xa y)(*strict*)
  apply(erule_tac
      x="xa"
      in allE)
  apply(erule_tac
      x="y"
      in allE)
  apply(clarsimp)
  apply(force)
  done

lemma notEQ: "
  P
  \<Longrightarrow> \<not> Q
  \<Longrightarrow> P \<noteq> Q"
  apply(force)
  done

lemma ex1I_prime: "
  P a
  \<Longrightarrow> (\<And>z. P a \<Longrightarrow> P z \<Longrightarrow> a = z)
  \<Longrightarrow> \<exists>!x. P x"
  apply(rule_tac
      a="a"
      in ex1I)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma split_into_butlast_and_last: "
  i < Suc n
  \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> P i)
  \<Longrightarrow> P n
  \<Longrightarrow> P i"
  apply(case_tac "i<n")
   apply(force)
  apply(subgoal_tac "i=n")
   prefer 2
   apply(force)
  apply(force)
  done

lemma meta_allE': "
  (\<And>x. PROP P x)
  \<Longrightarrow> (PROP P x \<Longrightarrow> (\<And>x. PROP P x) \<Longrightarrow> PROP W)
  \<Longrightarrow> PROP W"
  apply(erule_tac meta_impE)
   apply(erule_tac x="x" in meta_allE)
   apply(force)
  apply(erule_tac meta_impE)
   apply(force)
  apply(force)
  done

lemma meta_allE_two: "
  (\<And>x. P x \<Longrightarrow> Q x)
  \<Longrightarrow> P y1
  \<Longrightarrow> P y2
  \<Longrightarrow> Q y1 \<and> Q y2"
  apply(erule_tac x="y1" in meta_allE')
  apply(erule_tac x="y2" in meta_allE)
  apply(force)
  done

lemma foldl_extract: "
  foldl (+) x w = x + foldl (+) (0::nat) w"
  apply(induct w arbitrary: x rule: list.induct)
   apply(force)
  apply(rule_tac t="foldl (+) x (x1 # x2)" in ssubst)
   apply(rule foldl_Cons)
  apply(rule_tac t="foldl (+) 0 (x1 # x2)" in ssubst)
   apply(rule foldl_Cons)
  apply(erule_tac x="x + x1" in meta_allE')
  apply(erule_tac x="0 + x1" in meta_allE)
  apply(force)
  done

end
