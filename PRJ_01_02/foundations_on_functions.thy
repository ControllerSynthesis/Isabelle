section {*foundations\_on\_functions*}
theory
  foundations_on_functions

imports
  partial_functions

begin

definition left_total_on :: "
  ('A \<Rightarrow> 'B \<Rightarrow> bool)
  \<Rightarrow> 'A set
  \<Rightarrow> 'B set
  \<Rightarrow> bool"
  where
    "left_total_on R A B \<equiv>
  \<forall>a \<in> A. \<exists>b \<in> B. R a b"

definition right_total_on :: "
  ('A \<Rightarrow> 'B \<Rightarrow> bool)
  \<Rightarrow> 'A set
  \<Rightarrow> 'B set
  \<Rightarrow> bool"
  where
    "right_total_on R A B \<equiv>
  \<forall>b \<in> B. \<exists>a \<in> A. R a b"

definition bijection_on :: "
  ('a \<Rightarrow> 'b \<Rightarrow> bool)
  \<Rightarrow> 'a set
  \<Rightarrow> 'b set
  \<Rightarrow> bool"
  where
    "bijection_on F A B \<equiv>
  (\<forall>a \<in> A. \<exists>!b \<in> B. F a b)
  \<and> (\<forall>b \<in> B. \<exists>!a \<in> A. F a b)"

lemma bijection_on_RT: "
  bijection_on F A B
  \<Longrightarrow> a \<in> A
  \<Longrightarrow> \<exists>b\<in> B. F a b"
  apply(simp add: bijection_on_def)
  apply(force)
  done

lemma bijection_on_LT: "
  bijection_on F A B
  \<Longrightarrow> b \<in> B
  \<Longrightarrow> \<exists>a\<in> A. F a b"
  apply(simp add: bijection_on_def)
  apply(force)
  done

lemma bijection_on_RU: "
  bijection_on F A B
  \<Longrightarrow> a \<in> A
  \<Longrightarrow> b1 \<in> B
  \<Longrightarrow> b2 \<in> B
  \<Longrightarrow> F a b1
  \<Longrightarrow> F a b2
  \<Longrightarrow> b1 = b2"
  apply(simp add: bijection_on_def)
  apply(force)
  done

lemma bijection_on_LU: "
  bijection_on F A B
  \<Longrightarrow> b \<in> B
  \<Longrightarrow> a1 \<in> A
  \<Longrightarrow> a2 \<in> A
  \<Longrightarrow> F a1 b
  \<Longrightarrow> F a2 b
  \<Longrightarrow> a1=a2"
  apply(simp add: bijection_on_def)
  apply(force)
  done

lemma bijection_on_intro: "
  (\<forall>a\<in> A. \<exists>b\<in> B. F a b)
  \<Longrightarrow> (\<forall>b\<in> B. \<exists>a\<in> A. F a b)
  \<Longrightarrow> (\<forall>a\<in> A. \<forall>b1\<in> B. \<forall>b2\<in> B. F a b1 \<longrightarrow> F a b2 \<longrightarrow> b1 = b2)
  \<Longrightarrow> (\<forall>b\<in> B. \<forall>a1\<in> A. \<forall>a2\<in> A. F a1 b \<longrightarrow> F a2 b \<longrightarrow> a1 = a2)
  \<Longrightarrow> bijection_on F A B"
  apply(simp add: bijection_on_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(erule_tac
      x="a"
      in ballE)
    prefer 2
    apply(force)
   apply(erule_tac
      x="a"
      in ballE)
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(rule_tac
      a="b"
      in ex1I)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(erule_tac
      x="b"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="b"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      a="a"
      in ex1I)
   apply(force)
  apply(force)
  done

definition LT_ON :: "('\<Sigma> \<times> 'b)set \<Rightarrow> '\<Sigma> set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "LT_ON R A B = (\<forall>x \<in> A. \<exists>y \<in> B. (x,y) \<in> R)"


end

