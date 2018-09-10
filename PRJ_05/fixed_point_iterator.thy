section {*fixed\_point\_iterator*}
theory
  fixed_point_iterator

imports
  PRJ_05__ENTRY

begin

definition UNIVmap :: "'a \<Rightarrow> bool" where
  "UNIVmap \<equiv> \<lambda>x. True"

definition predicate_AND :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "predicate_AND F1 F2 = (\<lambda>x. F1 x \<and> F2 x)"

definition predicate_OR :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "predicate_OR F1 F2 = (\<lambda>x. F1 x \<or> F2 x)"

declare UNIVmap_def [simp add]
declare predicate_AND_def [simp add]
declare predicate_OR_def [simp add]

lemma GFP_SOUND_le_trans: "
  p\<le>(q::'a::order)
  \<Longrightarrow> q\<le>r
  \<Longrightarrow> p\<le>r"
  apply(rule order_trans_rules)
    apply(force)
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(force)
  done

definition Fixed_Point_Iterator :: "
  ('a::order \<Rightarrow> 'a)
  \<Rightarrow> 'a set
  \<Rightarrow> 'a set
  \<Rightarrow> 'a set
  \<Rightarrow> bool"
  where
    "Fixed_Point_Iterator F Qinp Qterm Qout \<equiv>
  \<forall>X \<in> Qinp. \<forall>Y \<in> Qinp.
     F X \<le> X
  \<and> (X \<le> Y \<longrightarrow> F X \<le> F Y)
  \<and> F X \<in> Qout
  \<and> (X \<in> Qterm \<longleftrightarrow> F X = X)"

definition Characteristic_Fixed_Point_Iterator :: "
  ('a::order \<Rightarrow> 'a)
  \<Rightarrow> ('a \<Rightarrow> bool)
  \<Rightarrow> ('a \<Rightarrow> bool)
  \<Rightarrow> ('a \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout \<equiv>
  (\<forall>X \<in> Collect Qinp. F X \<le> X)
  \<and> (\<forall>X \<in> Collect Qinp. Qterm X \<longleftrightarrow> F X = X)
  \<and> (\<forall>X \<in> Collect Qinp. Qout (F X))
  \<and> (\<forall>X \<in> Collect Qinp. \<forall>Y \<in> Collect Qinp. X \<le> Y \<longrightarrow> F X \<le> F Y)"

corollary Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1: "
  Fixed_Point_Iterator F (Collect Qinp) (Collect Qterm) (Collect Qout)
  = Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def Fixed_Point_Iterator_def)
  apply(rule antisym)
   apply(force)
  apply(force)
  done

corollary Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator2: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. x\<in> Qinp) (\<lambda>x. x\<in> Qterm) (\<lambda>x. x\<in> Qout)
  = Fixed_Point_Iterator F Qinp Qterm Qout"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def Fixed_Point_Iterator_def)
  apply(rule antisym)
   apply(force)
  apply(force)
  done

lemma Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points: "
  Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout
  \<Longrightarrow>
  (\<forall>X \<in> Collect Qinp. \<forall>Y \<in> Collect Qinp. F X < X \<longrightarrow> Y < X \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F X)"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(force)
  done

theorem Fixed_Point_Iterator_does_not_skip_Fixed_Points: "
  Fixed_Point_Iterator F Qinp Qterm Qout
  \<Longrightarrow> X \<in> Qinp
  \<Longrightarrow> Y \<in> Qinp
  \<Longrightarrow> F X < X
  \<Longrightarrow> Y < X
  \<Longrightarrow> F Y = Y
  \<Longrightarrow> Y \<le> F X"
  apply(simp add: Fixed_Point_Iterator_def)
  apply(force)
  done

definition Characteristic_Fixed_Point_IteratorDec :: "('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Characteristic_Fixed_Point_IteratorDec F Qinp Qterm Qout \<equiv> (
  (\<forall>X. F X \<le> X)
  \<and> (\<forall>X\<in> Collect Qinp. Qterm X \<longleftrightarrow> (F X = X))
  \<and> (\<forall>X\<in> Collect Qinp. Qout (F X))
  \<and> (\<forall>X. \<forall>Y. X \<le> Y \<longrightarrow> F X \<le> F Y))"

lemma Characteristic_Fixed_Point_Iterator_to_Characteristic_Fixed_Point_IteratorDec: "
  Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout
  \<Longrightarrow> (\<And>C. \<not>Qinp C \<Longrightarrow> F C \<le> C)
  \<Longrightarrow> (\<forall>X. \<forall>Y. X \<le> Y \<longrightarrow> F X \<le> F Y)
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinp Qterm Qout"
  apply(simp add: Characteristic_Fixed_Point_IteratorDec_def Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(erule_tac
      x="X"
      in allE)+
  apply(clarsimp)
  done

lemma Characteristic_Fixed_Point_IteratorDec_to_Characteristic_Fixed_Point_Iterator: "
  Characteristic_Fixed_Point_IteratorDec F Qinp Qterm Qout
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout"
  apply(simp add: Characteristic_Fixed_Point_IteratorDec_def Characteristic_Fixed_Point_Iterator_def)
  done

lemma Characteristic_Fixed_Point_Iterator_weakening: "
  Characteristic_Fixed_Point_Iterator F Qinp Qterm Qout
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator F Qinp Qterm UNIVmap"
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

lemma Characteristic_Fixed_Point_IteratorDec_does_not_skip_Fixed_Points: "
  Characteristic_Fixed_Point_IteratorDec F Qinp Qterm Qout
  \<Longrightarrow>
  (\<forall>X \<in> Collect Qinp. \<forall>Y \<in> Collect Qinp. F X < X \<longrightarrow> Y < X \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F X)"
  apply (metis Characteristic_Fixed_Point_IteratorDec_to_Characteristic_Fixed_Point_Iterator Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points)
  done

lemma Characteristic_Composition_of_Fixed_Point_Iterators: "
  Characteristic_Fixed_Point_Iterator F1 Qinp Qterm1 Qinter1
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator F2 Qinter2 Qterm2 Qout2
  \<Longrightarrow> (\<And>Q. Qinter1 Q \<longrightarrow> Qinter2 Q )
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (F2 \<circ> F1) Qinp (predicate_AND Qterm1 Qterm2) Qout2"
  apply(simp (no_asm) add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule context_conjI)
   apply(subgoal_tac "\<forall>X::'a. Qinter1 X \<longrightarrow> F2 X \<le> X")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule_tac
      q="F1 X"
      in GFP_SOUND_le_trans)
    apply(rename_tac X)(*strict*)
    apply(erule_tac
      x="F1 X"
      in allE)
    apply(clarsimp)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(force)
  apply(rule context_conjI)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

theorem Composition_of_Fixed_Point_Iterators: "
  Fixed_Point_Iterator F1 Qinp Qterm1 Qinter1
  \<Longrightarrow> Fixed_Point_Iterator F2 Qinter2 Qterm2 Qout2
  \<Longrightarrow> Qinter1 \<subseteq> Qinter2
  \<Longrightarrow> Fixed_Point_Iterator (F2 \<circ> F1) Qinp (Qterm1 \<inter> Qterm2) Qout2"
  apply(rule_tac
      t="Fixed_Point_Iterator (F2 \<circ> F1) Qinp (Qterm1 \<inter> Qterm2) Qout2"
      in subst)
   apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator2)
  apply(rule_tac
      P="\<lambda>X. X"
      and s="Characteristic_Fixed_Point_Iterator (F2 \<circ> F1) Qinp (predicate_AND Qterm1 Qterm2) Qout2" for Qinp Qterm1 Qterm2 Qout2
      in ssubst)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="\<lambda>x. x \<in> Qinter1"
      and ?Qinter2.0="\<lambda>x. x \<in> Qinter2"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule_tac
      P="\<lambda>X. X"
      in subst)
     apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1)
    apply(rule_tac
      t="{x. x \<in> Qinp}"
      and s="Qinp"
      in ssubst)
     apply(blast)
    apply(rule_tac
      t="{x. x \<in> Qterm1}"
      and s="Qterm1"
      in ssubst)
     apply(blast)
    apply(rule_tac
      t="{x. x \<in> Qinter1}"
      and s="Qinter1"
      in ssubst)
     apply(blast)
    apply(blast)
   apply(rule_tac
      P="\<lambda>X. X"
      in subst)
    apply(rule Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1)
   apply(rule_tac
      t="{x. x \<in> Qout2}"
      and s="Qout2"
      in ssubst)
    apply(blast)
   apply(rule_tac
      t="{x. x \<in> Qterm2}"
      and s="Qterm2"
      in ssubst)
    apply(blast)
   apply(rule_tac
      t="{x. x \<in> Qinter2}"
      and s="Qinter2"
      in ssubst)
    apply(blast)
   apply(blast)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

definition ifcomp :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "ifcomp F2 F1 \<equiv> \<lambda>C. if F1 C = C then C else (F2 \<circ> F1)C"

lemma Characteristic_Conditional_Composition_of_Fixed_Point_Iterators: "
  Characteristic_Fixed_Point_Iterator F1 Qinp Qterm1 Qinter1
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator F2 Qinter2 Qterm2 Qout
  \<Longrightarrow> (\<And>Q. Qinter1 Q \<longrightarrow> Qinter2 Q )
  \<Longrightarrow> (\<And>Q. Qinp Q \<and> Qterm1 Q \<longrightarrow> Qterm2 Q)
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (ifcomp F2 F1) Qinp (\<lambda>C. if F1 C=C then
Qterm1 C\<and>Qinp C else Qterm1 C\<and>Qterm2 C) (predicate_OR (predicate_AND (predicate_AND Qinp Qinter1) Qterm1) Qout)"
  apply(simp (no_asm) add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule context_conjI)
   apply(subgoal_tac "\<forall>X::'a. Qinter1 X \<longrightarrow> F2 X \<le> X")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(rule_tac
      q="F1 X"
      in GFP_SOUND_le_trans)
    apply(rename_tac X)(*strict*)
    apply(erule_tac
      x="F1 X"
      in allE)
    apply(simp add: ifcomp_def)
    apply(clarsimp)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(case_tac "F1 X = X")
    apply(rename_tac X)(*strict*)
    apply(simp add: ifcomp_def)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="X"
      in allE)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(simp add: ifcomp_def)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(force)
  apply(rule context_conjI)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(case_tac "F1 X = X")
    apply(rename_tac X)(*strict*)
    apply(simp add: ifcomp_def)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(simp add: ifcomp_def)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(rename_tac X Y)(*strict*)
  apply(case_tac "F1 X = X")
   apply(rename_tac X Y)(*strict*)
   apply(simp add: ifcomp_def)
   apply(clarsimp)
   apply(subgoal_tac "\<forall>X. Qinter2 X \<longrightarrow> (\<forall>Y. Qinter2 Y \<longrightarrow> X \<le> Y \<longrightarrow> F2 X \<le> F2 Y)")
    apply(rename_tac X Y)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X Y)(*strict*)
   apply(erule_tac
      x="F1 X"
      and P="\<lambda>x. Qinter2 x \<longrightarrow> (\<forall>Y. Qinter2 Y \<longrightarrow> x \<le> Y \<longrightarrow> F2 x \<le> F2 Y)"
      in allE)
   apply(erule impE)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(erule_tac
      x="F1 Y"
      and P="\<lambda>x. Qinter2 x \<longrightarrow> F1 X \<le> x \<longrightarrow> F2 (F1 X) \<le> F2 x"
      in allE)
   apply(erule impE)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X Y)(*strict*)
   apply(erule impE)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(subgoal_tac "(\<forall>X. Qinter2 X \<longrightarrow> Qterm2 X = (F2 X = X))")
    apply(rename_tac X Y)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X Y)(*strict*)
   apply(erule_tac
      x="F1 X"
      and P="\<lambda>x. Qinter2 x \<longrightarrow> Qterm2 x = (F2 x = x)"
      in allE)
   apply(erule impE)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(force)
   apply(rename_tac X Y)(*strict*)
   apply(subgoal_tac "Qterm2 (F1 X)")
    apply(rename_tac X Y)(*strict*)
    apply(clarsimp)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(simp add: ifcomp_def)
  apply(case_tac "F1 Y=Y")
   apply(rename_tac X Y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      q="F1 X"
      in GFP_SOUND_le_trans)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X Y)(*strict*)
   apply(rule_tac
      q="X"
      in GFP_SOUND_le_trans)
    apply(rename_tac X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X Y)(*strict*)
   apply(force)
  apply(rename_tac X Y)(*strict*)
  apply(clarsimp)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

lemma Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof: "
  P (Fixed_Point_Iterator F (Collect Q1) (Collect Q2) (Collect Q3))
  \<Longrightarrow> P (Characteristic_Fixed_Point_Iterator F Q1 Q2 Q3)"
  apply(simp add: Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1)
  done

lemma Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator2_proof: "
  P (Characteristic_Fixed_Point_Iterator F (\<lambda>x. x\<in> Qinp) (\<lambda>x. x\<in> Qterm) (\<lambda>x. x\<in> Qout))
  \<Longrightarrow> P (Fixed_Point_Iterator F Qinp Qterm Qout)"
  apply(simp add: Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator2)
  done

theorem Conditional_Composition_of_Fixed_Point_Iterators: "
  Fixed_Point_Iterator F1 Qinp Qterm1 Qinter1
  \<Longrightarrow> Fixed_Point_Iterator F2 Qinter2 Qterm2 Qout
  \<Longrightarrow> Qinter1 \<subseteq> Qinter2
  \<Longrightarrow> Qinp \<inter> Qterm1 \<subseteq> Qterm2
  \<Longrightarrow> Fixed_Point_Iterator
  (ifcomp F2 F1)
  Qinp
  {C. if F1 C=C then C \<in> Qterm1 \<inter> Qinp else C \<in> Qterm1 \<inter> Qterm2}
  ((Qinp \<inter> Qinter1 \<inter> Qterm1) \<union> Qout)"
  apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator2_proof)
  apply(rule_tac
      P="\<lambda>X. X"
      and s="Characteristic_Fixed_Point_Iterator (ifcomp F2 F1) (\<lambda>x. x \<in> Qinp) (\<lambda>C. if F1 C=C then (\<lambda>x. x \<in> Qterm1) C\<and>(\<lambda>x. x \<in> Qinp) C else (\<lambda>x. x \<in> Qterm1) C\<and>(\<lambda>x. x \<in> Qterm2) C) (predicate_OR (predicate_AND (predicate_AND (\<lambda>x. x \<in> Qinp) (\<lambda>x. x \<in> Qinter1))(\<lambda>x. x \<in> Qterm1)) (\<lambda>x. x \<in> Qout))"
      in subst)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="\<lambda>x. x \<in> Qinter1"
      and ?Qinter2.0="\<lambda>x. x \<in> Qinter2"
      in Characteristic_Conditional_Composition_of_Fixed_Point_Iterators)
     apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
     apply(force)
    apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
    apply(force)
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

definition Characteristic_Fixed_Point_IteratorX :: "('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Characteristic_Fixed_Point_IteratorX F Qterm \<equiv> (
  (\<forall>X. F X \<le> X)
  \<and> (\<forall>X. Qterm X \<longleftrightarrow> (F X = X))
  \<and> (\<forall>X Y. X \<le> Y \<longrightarrow> F X \<le> F Y))"

lemma Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator: "
  Characteristic_Fixed_Point_IteratorX F Qterm= Characteristic_Fixed_Point_Iterator F UNIVmap Qterm UNIVmap"
  apply(rule order_antisym)
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def Characteristic_Fixed_Point_Iterator_def)
  apply(simp add: Characteristic_Fixed_Point_IteratorX_def Characteristic_Fixed_Point_Iterator_def)
  done

lemma Characteristic_Fixed_Point_IteratorX_does_not_skip_Fixed_Points: "
  Characteristic_Fixed_Point_IteratorX F Qterm
  \<Longrightarrow> (\<forall>X Y. F X < X \<longrightarrow> Y < X \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F X)"
  apply (metis Characteristic_Fixed_Point_IteratorX_def le_less)
  done

lemma Supremum_to_gfp: "
  Characteristic_Fixed_Point_IteratorX F Qterm
  \<Longrightarrow> Sup{X. Qterm X} = gfp F"
  apply(unfold Characteristic_Fixed_Point_IteratorX_def)
  apply(rule_tac
      t="gfp F"
      and s="Sup{u. u \<le> F u}"
      in ssubst)
   apply(simp only: gfp_def)
  apply(rule_tac
      t="{X. Qterm X}"
      and s="{u. u \<le> F u}"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in allE)+
  apply(force)
  done

lemma gfp_invariant: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> gfp (\<lambda>X. F (inf X (F Y))) = gfp (\<lambda>X. F (inf X Y))"
  apply(rule order_antisym)
   apply(simp add: gfp_def)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule_tac
      q="F (inf x (F Y))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "inf x (F Y) \<le> inf x Y")
    apply(rename_tac x)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "F Y \<le> Y")
    apply(rename_tac x)(*strict*)
    apply (rule inf_mono order_refl)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  apply(simp add: gfp_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(rule Sup_upper)
  apply(clarsimp)
  apply(subgoal_tac "F (inf x Y) \<le> F x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "F (inf x Y) \<le> F Y")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "F x \<le> x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x= F (inf x Y)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      q="F (inf x Y)"
      in GFP_SOUND_le_trans)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "inf x Y \<le> inf x (F Y)")
   apply(rename_tac x)(*strict*)
   apply(unfold Characteristic_Fixed_Point_IteratorX_def)
   apply(erule conjE)+
   apply(erule_tac
      x="inf x Y"
      and P="\<lambda>X. \<forall>Ya\<ge>X. F X \<le> F Ya"
      in allE)
   apply(erule_tac
      x="inf x (F Y)"
      and P="\<lambda>X. inf x Y \<le> X \<longrightarrow> F (inf x Y) \<le> F X"
      in allE)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(fold Characteristic_Fixed_Point_IteratorX_def)
  apply(subgoal_tac "x\<le>Y")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
   apply(clarsimp)
   apply(rule_tac
      q="F Y"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "inf x Y = x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      t="inf x Y = x"
      and s="x\<le>Y"
      in subst)
    apply(rename_tac x)(*strict*)
    apply (rule le_iff_inf)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma computation_via_Compute_Fixed_Point_Finite_hlp1: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> F A \<noteq> A
  \<Longrightarrow> F (F A) \<noteq> F A
  \<Longrightarrow> gfp F < A
  \<Longrightarrow> gfp F < F A"
  apply(subgoal_tac "(\<forall>X Y. F X < X \<longrightarrow> Y < X \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F X)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_IteratorX_does_not_skip_Fixed_Points)
   apply(force)
  apply(erule_tac
      x="A"
      in allE)
  apply(subgoal_tac "F A \<le> A")
   apply(clarsimp)
   apply(erule impE)
    apply(force)
   apply(erule_tac
      x="gfp F"
      in allE)
   apply(erule impE)
    apply(force)
   apply(subgoal_tac "mono F")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorX_def mono_def)
   apply(erule impE)
    apply (metis gfp_unfold)
   apply(case_tac "gfp F = F A")
    apply (metis gfp_unfold)
   apply(force)
  apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  done

lemma computation_via_Compute_Fixed_Point_Finite_hlp2: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> F A \<noteq> A
  \<Longrightarrow> F (F A) = F A
  \<Longrightarrow> gfp F < A
  \<Longrightarrow> F A = gfp F"
  apply(subgoal_tac "mono F")
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorX_def mono_def)
  apply(rule order_antisym)
   apply (metis gfp_upperbound order_eq_refl)
  apply(subgoal_tac "(\<forall>X Y. F X < X \<longrightarrow> Y < X \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F X)")
   prefer 2
   apply(rule Characteristic_Fixed_Point_IteratorX_does_not_skip_Fixed_Points)
   apply(force)
  apply(erule_tac
      x="A"
      in allE)
  apply(subgoal_tac "F A \<le> A")
   apply(clarsimp)
   apply(erule impE)
    apply(force)
   apply(erule_tac
      x="gfp F"
      in allE)
   apply(erule impE)
    apply(force)
   apply(erule impE)
    apply (metis gfp_unfold)
   apply(case_tac "gfp F = F A")
    apply (metis)
   apply(force)
  apply(simp add: Characteristic_Fixed_Point_IteratorX_def)
  done

end
