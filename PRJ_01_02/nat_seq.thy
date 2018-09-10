section {*nat\_seq*}
theory
  nat_seq

imports
  partial_functions

begin

function (domintros) nat_seq :: "
  nat
  \<Rightarrow> nat
  \<Rightarrow> nat list"
  where
    "nat_seq n m =
  (if n \<le> m then [n]@nat_seq (Suc n) m else [])"
   apply(rename_tac P x)(*strict*)
   apply(auto)
  done

lemma nat_seq_termination: "
  nat_seq_dom (x, y)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(n,m). True"
      and RECURSIVE_COND = "\<lambda>(n,m). n \<le> m"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(n,m). (Suc n,m)"
      and MEASURE = "\<lambda>(n,m). Suc m - n"
      in partial_termination_wf)
      apply(auto)
   apply(rename_tac a b)(*strict*)
   apply(rule nat_seq.domintros)
   apply(blast)
  apply(rename_tac a b)(*strict*)
  apply(rule nat_seq.domintros)
  apply(auto)
  done

lemma nat_seqEmpty: "
  n>m
  \<Longrightarrow> nat_seq n m = []"
  apply(rule_tac
      t = "nat_seq n m"
      and s = " (if n \<le> m then [n] @ nat_seq (Suc n) m else [])"
      in ssubst)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(clarsimp)
  done

lemma nat_seq_Shift_length: "
  length (nat_seq n m) = length (nat_seq (n + k) (m + k))"
  apply(induct m arbitrary: n k)
   apply(rename_tac n k)(*strict*)
   apply(rule_tac
      t = "nat_seq n 0"
      and s = " (if n \<le> 0 then [n] @ nat_seq (Suc n) 0 else [])"
      in ssubst)
    apply(rename_tac n k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (Suc 0) 0"
      and s = " (if (Suc 0) \<le> 0 then [Suc 0] @ nat_seq (Suc (Suc 0)) 0 else [])"
      in ssubst)
    apply(rename_tac n k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac n k)(*strict*)
    apply(clarsimp)
    apply(rename_tac k)(*strict*)
    apply(rule_tac
      t = "nat_seq k k"
      and s = " (if k \<le> k then [k] @ nat_seq (Suc k) k else [])"
      in ssubst)
     apply(rename_tac k)(*strict*)
     apply(rule nat_seq.psimps)
     apply(rule nat_seq_termination)
    apply(rename_tac k)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t = "nat_seq (Suc k) k"
      and s = " (if (Suc k) \<le> k then [Suc k] @ nat_seq (Suc (Suc k)) k else [])"
      in ssubst)
     apply(rename_tac k)(*strict*)
     apply(rule nat_seq.psimps)
     apply(rule nat_seq_termination)
    apply(rename_tac k)(*strict*)
    apply(clarsimp)
   apply(rename_tac n k)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (n + k) k"
      and s = " (if (n + k) \<le> k then [n + k] @ nat_seq (Suc (n + k)) k else [])"
      in ssubst)
    apply(rename_tac n k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n k)(*strict*)
  apply(rule_tac
      t = "nat_seq n (Suc m)"
      and s = " (if n \<le> (Suc m) then [n] @ nat_seq (Suc n) (Suc m) else [])"
      in ssubst)
   apply(rename_tac m n k)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac m n k)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "length (nat_seq (Suc n) (Suc m))"
      and s = "length (nat_seq n m)"
      in ssubst)
    apply(rename_tac m n k)(*strict*)
    apply(rule_tac
      s = "length (nat_seq (n + (Suc 0)) (m + (Suc 0)))"
      and t = "length (nat_seq n m)"
      in ssubst)
     apply(rename_tac m n k)(*strict*)
     apply(blast)
    apply(rename_tac m n k)(*strict*)
    apply(force)
   apply(rename_tac m n k)(*strict*)
   apply(rule_tac
      t = "nat_seq (n + k) (Suc (m + k))"
      and s = " (if (n + k) \<le> (Suc(m + k)) then [n + k] @ nat_seq (Suc (n + k)) (Suc(m + k)) else [])"
      in ssubst)
    apply(rename_tac m n k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac m n k)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "Suc (n + k)"
      and s = "n + (Suc k)"
      in ssubst)
    apply(rename_tac m n k)(*strict*)
    apply(arith)
   apply(rename_tac m n k)(*strict*)
   apply(rule_tac
      t = "Suc (m + k)"
      and s = "m + (Suc k)"
      in ssubst)
    apply(rename_tac m n k)(*strict*)
    apply(arith)
   apply(rename_tac m n k)(*strict*)
   apply(blast)
  apply(rename_tac m n k)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (n + k) (Suc (m + k))"
      and s = " (if (n + k) \<le> (Suc(m + k)) then [n + k] @ nat_seq (Suc (n + k)) (Suc(m + k)) else [])"
      in ssubst)
   apply(rename_tac m n k)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k)(*strict*)
  apply(clarsimp)
  done

lemma nat_seq_length: "
  m \<ge> n
  \<Longrightarrow> length (nat_seq n m) = m - n + 1"
  apply(subgoal_tac "n \<le> m \<longrightarrow> length (nat_seq n m) = m - n + 1")
   apply(blast)
  apply(thin_tac "m \<ge> n")
  apply(induct m arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(auto)
   apply(rule_tac
      t = "nat_seq 0 0"
      and s = " (if 0 \<le> 0 then [0] @ nat_seq (Suc 0) 0 else [])"
      in ssubst)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (Suc 0) 0"
      and s = " (if (Suc 0) \<le> 0 then [Suc 0] @ nat_seq (Suc (Suc 0)) 0 else [])"
      in ssubst)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(clarsimp)
  apply(rename_tac m n)(*strict*)
  apply(rule_tac
      t = "nat_seq n (Suc m)"
      and s = " (if n \<le> (Suc m) then [n] @ nat_seq (Suc n) (Suc m) else [])"
      in ssubst)
   apply(rename_tac m n)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "length (nat_seq (Suc n) (Suc m))"
      and s = "length (nat_seq n m)"
      in ssubst)
   apply(rename_tac m n)(*strict*)
   apply(rule_tac
      t = "Suc n"
      and s = "n + (Suc 0)"
      in ssubst)
    apply(rename_tac m n)(*strict*)
    apply(arith)
   apply(rename_tac m n)(*strict*)
   apply(rule_tac
      t = "Suc m"
      and s = "m + (Suc 0)"
      in ssubst)
    apply(rename_tac m n)(*strict*)
    apply(arith)
   apply(rename_tac m n)(*strict*)
   apply(rule sym)
   apply(rule nat_seq_Shift_length)
  apply(rename_tac m n)(*strict*)
  apply(case_tac "Suc m - n = 0")
   apply(rename_tac m n)(*strict*)
   apply(clarsimp)
   apply(rename_tac m)(*strict*)
   apply(rule_tac
      t = "nat_seq (Suc m) m"
      and s = " (if (Suc m) \<le> m then [Suc m] @ nat_seq (Suc (Suc m)) m else [])"
      in ssubst)
    apply(rename_tac m)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac m)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n)(*strict*)
  apply(rule_tac
      t = "Suc m - n"
      and s = "Suc (m - n)"
      in ssubst)
   apply(rename_tac m n)(*strict*)
   apply(arith)
  apply(rename_tac m n)(*strict*)
  apply(force)
  done

lemma nat_seq_length_Suc0: "
  w = nat_seq (Suc 0) m
  \<Longrightarrow> m>0
  \<Longrightarrow> length w = m"
  apply(subgoal_tac "\<forall>m. length (nat_seq (Suc 0) (Suc m)) = Suc m")
   apply(case_tac m)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(erule_tac
      x = "nat"
      in allE)
   apply(clarsimp)
  apply(thin_tac "w = nat_seq (Suc 0) m")
  apply(thin_tac "0 < m")
  apply(rule allI) +
  apply(rename_tac m)(*strict*)
  apply(induct_tac m)
   apply(rename_tac m)(*strict*)
   apply(rule_tac
      t = "nat_seq (Suc 0) (Suc 0)"
      and s = " (if (Suc 0) \<le> (Suc 0) then [Suc 0] @ nat_seq (Suc (Suc 0)) (Suc 0) else [])"
      in ssubst)
    apply(rename_tac m)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac m)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (Suc (Suc 0)) (Suc 0)"
      and s = " (if (Suc (Suc 0)) \<le> (Suc 0) then [Suc (Suc 0)] @ nat_seq (Suc (Suc (Suc 0))) (Suc 0) else [])"
      in ssubst)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(clarsimp)
  apply(rename_tac m n)(*strict*)
  apply(rule_tac
      t = "nat_seq (Suc 0) (Suc (Suc n))"
      and s = " (if (Suc 0) \<le> (Suc (Suc n)) then [Suc 0] @ nat_seq (Suc (Suc 0)) (Suc (Suc n)) else [])"
      in ssubst)
   apply(rename_tac m n)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "(Suc (Suc n)) - (Suc (Suc 0)) + 1"
      and t = "length (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule nat_seq_length)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(arith)
  done

lemma nat_seq_Shift_nth: "
  i \<le> (m - n)
  \<Longrightarrow> n \<le> m
  \<Longrightarrow> nat_seq (n + k) (m + k) ! i = k + (nat_seq n m ! i)"
  apply(subgoal_tac "i \<le> m - n \<and> n \<le> m \<longrightarrow> nat_seq (n + k) (m + k) ! i = k + nat_seq n m ! i")
   apply(blast)
  apply(thin_tac "i \<le> m - n")
  apply(thin_tac "n \<le> m")
  apply(induct m arbitrary: n k i)
   apply(rename_tac n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq n 0"
      and s = " (if n \<le> 0 then [n] @ nat_seq (Suc n) 0 else [])"
      in ssubst)
    apply(rename_tac n k i)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k i)(*strict*)
   apply(clarsimp)
   apply(rename_tac k)(*strict*)
   apply(auto)
   apply(rule_tac
      t = "nat_seq (Suc 0) 0"
      and s = " (if (Suc 0) \<le> 0 then [Suc 0] @ nat_seq (Suc (Suc 0)) 0 else [])"
      in ssubst)
    apply(rename_tac k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      t = "nat_seq k k"
      and s = " (if k \<le> k then [k] @ nat_seq (Suc k) k else [])"
      in ssubst)
    apply(rename_tac k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "nat_seq n (Suc m)"
      and s = " (if n \<le> (Suc m) then [n] @ nat_seq (Suc n) (Suc m) else [])"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (n + k) (Suc (m + k))"
      and s = " (if (n + k) \<le> (Suc (m + k)) then [n + k] @ nat_seq (Suc (n + k)) (Suc (m + k)) else [])"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac m n k i)(*strict*)
   apply(auto)
  apply(rename_tac m n k nat)(*strict*)
  apply(rename_tac i)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc (m + k)"
      and s = "m + (Suc k)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc (n + k)"
      and s = "n + (Suc k)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc m"
      and s = "m + (Suc 0)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc n"
      and s = "n + (Suc 0)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(case_tac "i \<le> m - n \<and> n \<le> m")
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq (n + Suc k) (m + Suc k) ! i"
      and s = "(Suc k) + nat_seq n m ! i"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(blast)
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq (n + Suc 0) (m + Suc 0) ! i"
      and s = "(Suc 0) + nat_seq n m ! i"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(blast)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(arith)
  done

lemma nat_seq_nth_ignore_tail: "
  i \<le> m - n
  \<Longrightarrow> n \<le> m
  \<Longrightarrow> nat_seq n m ! i = nat_seq n (m + k) ! i"
  apply(subgoal_tac "i \<le> m - n \<and> n \<le> m \<longrightarrow> nat_seq n m ! i = nat_seq n (m + k) ! i")
   apply(blast)
  apply(thin_tac "i \<le> m - n")
  apply(thin_tac "n \<le> m")
  apply(induct m arbitrary: n k i)
   apply(rename_tac n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq n 0"
      and s = " (if n \<le> 0 then [n] @ nat_seq (Suc n) 0 else [])"
      in ssubst)
    apply(rename_tac n k i)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k i)(*strict*)
   apply(clarsimp)
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      t = "nat_seq 0 k"
      and s = " (if 0 \<le> k then [0] @ nat_seq (Suc 0) k else [])"
      in ssubst)
    apply(rename_tac k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n k i)(*strict*)
  apply(rule impI)
  apply(rule_tac
      t = "nat_seq n (Suc m)"
      and s = " (if n \<le> (Suc m) then [n] @ nat_seq (Suc n) (Suc m) else [])"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq n (Suc (m + k))"
      and s = " (if n \<le> (Suc(m + k)) then [n] @ nat_seq (Suc n) (Suc(m + k)) else [])"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac m n k i)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n k i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac m n k nat)(*strict*)
  apply(rename_tac i)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc n"
      and s = "n + (Suc 0)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(rule_tac
      t = "Suc m"
      and s = "m + (Suc 0)"
      in ssubst)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(case_tac "i \<le> m - n \<and> n \<le> m")
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq (n + Suc 0) (m + Suc 0) ! i"
      and s = "(Suc 0) + (nat_seq n m) ! i"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(rule nat_seq_Shift_nth)
     apply(rename_tac m n k i)(*strict*)
     apply(blast)
    apply(rename_tac m n k i)(*strict*)
    apply(clarsimp)
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq n m ! i"
      and s = "nat_seq n (m + k) ! i"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(blast)
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "Suc n"
      and s = "n + (Suc 0)"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(arith)
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "Suc (m + k)"
      and s = "m + k + (Suc 0)"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(arith)
   apply(rename_tac m n k i)(*strict*)
   apply(rule_tac
      t = "nat_seq (n + Suc 0) (m + k + Suc 0) ! i"
      and s = "(Suc 0) + (nat_seq n (m + k)) ! i"
      in ssubst)
    apply(rename_tac m n k i)(*strict*)
    apply(rule nat_seq_Shift_nth)
     apply(rename_tac m n k i)(*strict*)
     apply(arith)
    apply(rename_tac m n k i)(*strict*)
    apply(arith)
   apply(rename_tac m n k i)(*strict*)
   apply(arith)
  apply(rename_tac m n k i)(*strict*)
  apply(clarsimp)
  apply(arith)
  done

lemma nat_seq_nth_compute: "
  n \<le> m
  \<Longrightarrow> k \<le> m - n
  \<Longrightarrow> nat_seq n m ! k = n + k"
  apply(subgoal_tac "k \<le> m - n \<and> n \<le> m \<longrightarrow> nat_seq n m ! k = n + k")
   apply(blast)
  apply(thin_tac "k \<le> m - n")
  apply(thin_tac "n \<le> m")
  apply(induct m arbitrary: n k i)
   apply(rename_tac n k)(*strict*)
   apply(rule_tac
      t = "nat_seq n 0"
      and s = " (if n \<le> 0 then [n] @ nat_seq (Suc n) 0 else [])"
      in ssubst)
    apply(rename_tac n k)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac n k)(*strict*)
   apply(clarsimp)
  apply(rename_tac m n k)(*strict*)
  apply(auto)
  apply(rule_tac
      t = "nat_seq n (Suc m)"
      and s = " (if n \<le> (Suc m) then [n] @ nat_seq (Suc n) (Suc m) else [])"
      in ssubst)
   apply(rename_tac m n k)(*strict*)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(rename_tac m n k)(*strict*)
  apply(clarsimp)
  apply(case_tac k)
   apply(rename_tac m n k)(*strict*)
   apply(auto)
  apply(rename_tac m n nat)(*strict*)
  apply(rule_tac
      t = "nat_seq (Suc n) (Suc m) ! nat"
      and s = "(Suc 0) + (nat_seq n m) ! nat "
      in ssubst)
   apply(rename_tac m n nat)(*strict*)
   apply(rule_tac
      t = "Suc n"
      and s = "n + (Suc 0)"
      in ssubst)
    apply(rename_tac m n nat)(*strict*)
    apply(arith)
   apply(rename_tac m n nat)(*strict*)
   apply(rule_tac
      t = "Suc m"
      and s = "m + (Suc 0)"
      in ssubst)
    apply(rename_tac m n nat)(*strict*)
    apply(arith)
   apply(rename_tac m n nat)(*strict*)
   apply(rule nat_seq_Shift_nth)
    apply(rename_tac m n nat)(*strict*)
    apply(arith)
   apply(rename_tac m n nat)(*strict*)
   apply(arith)
  apply(rename_tac m n nat)(*strict*)
  apply(rule_tac
      t = "nat_seq n m ! nat"
      and s = "n + nat"
      in ssubst)
   apply(rename_tac m n nat)(*strict*)
   apply(case_tac "n \<le> m \<and> nat \<le> m - n")
    apply(rename_tac m n nat)(*strict*)
    apply(blast)
   apply(rename_tac m n nat)(*strict*)
   apply(arith)
  apply(rename_tac m n nat)(*strict*)
  apply(arith)
  done

lemma natUptTo_n_n: "
  nat_seq n n = [n]"
  apply(rule_tac
      t = "nat_seq n n"
      and s = " (if n \<le> n then [n] @ nat_seq (Suc n) n else [])"
      in ssubst)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (Suc n) n"
      and s = " (if (Suc n) \<le> n then [Suc n] @ nat_seq (Suc (Suc n)) n else [])"
      in ssubst)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(clarsimp)
  done

lemma natUptTo_n_Sucn: "
  nat_seq n (Suc n) = [n,Suc n]"
  apply(rule_tac
      t = "nat_seq n (Suc n)"
      and s = " (if n \<le> (Suc n) then [n] @ nat_seq (Suc n) (Suc n) else [])"
      in ssubst)
   apply(rule nat_seq.psimps)
   apply(rule nat_seq_termination)
  apply(clarsimp)
  apply(rule natUptTo_n_n)
  done

lemma nat_seq_length_prime: "
  length (nat_seq n m) = m + 1 - n"
  apply(case_tac "n \<le> m")
   apply(rule_tac
      t = "m + 1 - n"
      and s = "m - n + 1"
      in ssubst)
    apply(force)
   apply(rule nat_seq_length)
   apply(force)
  apply(clarsimp)
  apply(rule nat_seqEmpty)
  apply(force)
  done

lemma nat_seq_in_interval: "
  i  \<in> set (nat_seq n m)
  \<Longrightarrow> n \<le> i \<and> i \<le> m"
  apply(subgoal_tac "\<exists>k < length (nat_seq n m). (nat_seq n m) ! k = i")
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(subgoal_tac "length (nat_seq n m) = m + 1 - n")
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(case_tac "n \<le> m")
   apply(rename_tac k)(*strict*)
   apply(rule_tac
      t = "nat_seq n m ! k"
      and s = "n + k"
      in ssubst)
    apply(rename_tac k)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac k)(*strict*)
     apply(force)
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  done

lemma nat_seq_drop_last: "
  nat_seq n (Suc (n + ka)) = nat_seq n (n + ka) @ [Suc (n + ka)]"
  apply(rule listEqI)
   apply (metis Suc_eq_plus1 add_Suc_right diff_add_inverse length_Suc nat_seq_length_prime add.commute)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length(nat_seq n (Suc (n + ka))) = (Suc (n+ka)) - n + Suc 0")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis One_nat_def Suc_diff_le Suc_eq_plus1 Suc_eq_plus1_left le_Suc_eq le_add1 nat_seq_length_prime add.commute)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length(nat_seq n ((n + ka))) = ((n+ka)) - n + Suc 0")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis One_nat_def Suc_diff_le Suc_eq_plus1 Suc_eq_plus1_left le_add1 nat_seq_length_prime add.commute)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=Suc ka")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply (metis add_Suc_right diff_add_inverse le_add1 le_refl nat_seq_nth_compute nth_append_length)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(nat_seq n (n + ka) @ [Suc (n + ka)]) ! i"
      and s="(nat_seq n (n + ka)) ! i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply (metis List.nth_append less_SucE add.commute)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "i<Suc ka")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      s="n+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule nat_seq_nth_compute)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma nat_seq_drop_last_simp: "
  n\<le>m
  \<Longrightarrow> nat_seq n (Suc m) = nat_seq n m @ [Suc m]"
  apply (metis le_iff_add nat_seq_drop_last natUptTo_n_n)
  done

lemma nat_seq_drop_last_prime: "
  nat_seq (Suc 0) (Suc m) = nat_seq (Suc 0) m @ [Suc m]"
  apply (metis nat_seq_drop_last_simp less_Suc0 nat_seqEmpty natUptTo_n_n self_append_conv2 trivNat)
  done

lemma nat_seq_drop_first: "
  a = m
  \<Longrightarrow> b = m + n
  \<Longrightarrow> b = b'
  \<Longrightarrow> c = Suc m
  \<Longrightarrow> nat_seq a b = [m]@(nat_seq c b')"
  apply(subgoal_tac "length (nat_seq m (m + n)) = (m + n) + 1 - m")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc m) (m + n)) = (m + n) + 1 - (Suc m)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq m (m + n) ! i"
      and s = "m + i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t = "nat_seq (Suc m) (m + n) ! nat"
      and s = "(Suc m) + nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma nat_seq_split: "
  a = x
  \<Longrightarrow> a = a'
  \<Longrightarrow> b = x + y + z
  \<Longrightarrow> b = b'
  \<Longrightarrow> c = x + y
  \<Longrightarrow> c = c'
  \<Longrightarrow> nat_seq a b = nat_seq a' c @ (tl(nat_seq c' b'))"
  apply(clarsimp)
  apply(induct "y" arbitrary: z)
   apply(rename_tac z)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length(nat_seq x (x + z)) = (x + z) + 1 - x")
    apply(rename_tac z)(*strict*)
    apply(clarsimp)
    apply(rule tl_nth_eq)
     apply(rename_tac z)(*strict*)
     apply(force)
    apply(rename_tac z)(*strict*)
    apply(rule_tac
      t = "nat_seq x (x + z) ! 0"
      and s = "x + 0"
      in ssubst)
     apply(rename_tac z)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac z)(*strict*)
      apply(force)
     apply(rename_tac z)(*strict*)
     apply(clarsimp)
    apply(rename_tac z)(*strict*)
    apply(clarsimp)
    apply (metis natUptTo_n_n)
   apply(rename_tac z)(*strict*)
   apply (metis nat_seq_length_prime)
  apply(rename_tac y z)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x = "Suc z"
      in meta_allE)
  apply(clarsimp)
  apply(thin_tac "nat_seq x (Suc (x + y + z)) = nat_seq x (x + y) @ tl (nat_seq (x + y) (Suc (x + y + z)))")
  apply(rule_tac
      t = "nat_seq (x + y) (Suc (x + y + z))"
      and s = "[x + y]@(nat_seq (Suc (x + y)) (Suc (x + y + z)))"
      in ssubst)
   apply(rename_tac y z)(*strict*)
   apply(rule nat_seq_drop_first)
      apply(rename_tac y z)(*strict*)
      apply(force)
     apply(rename_tac y z)(*strict*)
     apply(force)
    apply(rename_tac y z)(*strict*)
    apply(force)
   apply(rename_tac y z)(*strict*)
   apply(force)
  apply(rename_tac y z)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (Suc(x + y)) (Suc (x + y + z))"
      and s = "[Suc(x + y)]@(nat_seq (Suc(Suc (x + y))) (Suc (x + y + z)))"
      in ssubst)
   apply(rename_tac y z)(*strict*)
   apply(rule nat_seq_drop_first)
      apply(rename_tac y z)(*strict*)
      apply(force)
     apply(rename_tac y z)(*strict*)
     apply(force)
    apply(rename_tac y z)(*strict*)
    apply(force)
   apply(rename_tac y z)(*strict*)
   apply(force)
  apply(rename_tac y z)(*strict*)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "length(nat_seq x (x + y)) = (x + y) + 1 - x")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply (metis nat_seq_length_prime)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "length(nat_seq x (Suc(x + y))) = (Suc(x + y)) + 1 - x")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply (metis nat_seq_length_prime)
  apply(rename_tac y)(*strict*)
  apply(rule listEqI)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq x (Suc (x + y)) ! i"
      and s = "x + i"
      in ssubst)
   apply(rename_tac y i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac y i)(*strict*)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(force)
  apply(rename_tac y i)(*strict*)
  apply(case_tac "i = Suc y")
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply (metis nth_append_length)
  apply(rename_tac y i)(*strict*)
  apply (metis diff_add_inverse2 le_add2 less_Suc_eq_le less_antisym nat_seq_nth_compute add.commute nth_append_1)
  done

lemma nat_seq_interval: "
  x \<le> n
  \<Longrightarrow> n \<le> y
  \<Longrightarrow> n  \<in> set (nat_seq x y)"
  apply(rule_tac
      s = "(\<exists>i < length xs. xs ! i = x)" for xs x
      in ssubst)
   apply(rule in_set_conv_nth)
  apply(rule_tac
      t = "length (nat_seq x y)"
      and s = "y + 1 - x"
      in ssubst)
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule_tac
      x = "n - x"
      in exI)
  apply(rule conjI)
   apply(force)
  apply(rule_tac
      t = "nat_seq x y ! (n - x)"
      and s = "x + (n - x)"
      in ssubst)
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(force)
  done

lemma nat_seq_last: "
  m < n
  \<Longrightarrow> nat_seq (Suc m) (n - Suc 0) @ [n] = nat_seq (Suc m) n"
  apply(subgoal_tac "length (nat_seq (Suc m) (n - Suc 0)) = (n - Suc 0) + 1 - (Suc m)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc m) n) = n + 1 - (Suc m)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule listEqI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. m + (Suc x) = n")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule less_delta_exists)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i x)(*strict*)
  apply(case_tac "i < x")
   apply(rename_tac i x)(*strict*)
   apply(rule_tac
      t = "(nat_seq (Suc m) (m + x) @ [Suc (m + x)]) ! i"
      and s = "nat_seq (Suc m) (m + x) ! i"
      in ssubst)
    apply(rename_tac i x)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i x)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (Suc m) (m + x) ! i"
      and s = "Suc m + i"
      in ssubst)
    apply(rename_tac i x)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i x)(*strict*)
     apply(force)
    apply(rename_tac i x)(*strict*)
    apply(force)
   apply(rename_tac i x)(*strict*)
   apply(rule sym)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i x)(*strict*)
    apply(force)
   apply(rename_tac i x)(*strict*)
   apply(force)
  apply(rename_tac i x)(*strict*)
  apply(subgoal_tac "i = x")
   apply(rename_tac i x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t = "(nat_seq (Suc m) (m + x) @ [Suc (m + x)]) ! x"
      and s = "[Suc (m + x)] ! (x - length (nat_seq (Suc m) (m + x)))"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule_tac
      t = "Suc (m + x)"
      and s = "Suc m + x"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule nat_seq_nth_compute)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma nat_seq_drop_first2: "
  Suc x=n-m
  \<Longrightarrow> nat_seq m (n-Suc 0) = [m]@(nat_seq (Suc m) (n-Suc 0))"
  apply(subgoal_tac "length (nat_seq m (n - Suc 0)) = (n - Suc 0) + 1 - m")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc m) (n - Suc 0)) = (n - Suc 0) + 1 - (Suc m)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq m (n - Suc 0) ! i"
      and s="m + i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc m) (n - Suc 0) ! nat"
      and s="(Suc m) + nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    defer
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma nat_seq_pullout: "
  n\<le>m
  \<Longrightarrow> nat_seq n m = n#(nat_seq (Suc n) m)"
  apply (metis Cons_eq_appendI Suc_diff_le diff_Suc_Suc nat_seq_drop_first2 eq_Nil_appendI minus_nat.diff_0)
  done

lemma int_interval_singleton: "
  [x..x] = [x]"
  apply (metis less_irrefl order_refl upto_aux_rec upto_code zle_diff1_eq)
  done

lemma int_interval_drop_last: "
  x\<le>y
  \<Longrightarrow> [x..y+1] = [x..y]@[y+1]"
  apply (metis add_diff_cancel upto_rec2 zle_add1_eq_le zless_add1_eq)
  done

lemma int_interval_vs_nat_seq: "
  map nat [int n..int m] = nat_seq n m"
  apply(case_tac "n>m")
   apply(clarsimp)
   apply (metis nat_seqEmpty)
  apply(induct "m-n" arbitrary: m) 
   apply(clarsimp)
   apply (metis int_interval_singleton list.simps(8) list.simps(9) natUptTo_n_n nat_int)
  apply(case_tac m)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "n = nata-x")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "Suc nata \<ge> nata - x")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(erule_tac x="nata" in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(force)
  apply(rule_tac t="[int (nata - x)..1 + int nata]" and s="[int (nata - x)..int nata]@[int nata+1]" in ssubst)
   apply(rule_tac t="1 + int nata" and s="int nata+1" in ssubst)
    apply(force)
   apply(rule int_interval_drop_last)
   apply(force)
  apply(rule_tac t="nat_seq (nata - x) (Suc nata)" and s="nat_seq (nata - x) (nata)@[Suc nata]" in
      ssubst)
   apply(rule nat_seq_drop_last_simp)
   apply(force)
  apply(force)
  done

end
