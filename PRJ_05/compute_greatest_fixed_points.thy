section {*compute\_greatest\_fixed\_points*}
theory
  compute_greatest_fixed_points

imports
  fixed_point_iterator

begin

function (domintros) Compute_Fixed_Point :: "('a DES \<Rightarrow> 'a DES) \<Rightarrow> 'a DES \<Rightarrow> 'a DES" where
  "Compute_Fixed_Point F D = (if(D=F D)then D else Compute_Fixed_Point F (F D))"
   apply(rename_tac P x)(*strict*)
   apply(force)+
  done

primrec Compute_Fixed_Point_Finite :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Compute_Fixed_Point_Finite 0 F D = D"
| "Compute_Fixed_Point_Finite (Suc n) F D = Compute_Fixed_Point_Finite n F (F D)"

lemma Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply: "
  Compute_Fixed_Point_Finite n F (F A) = Compute_Fixed_Point_Finite (Suc n) F A"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  done

lemma Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp: "
  \<forall>A. F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite (Suc n) F A"
  apply(induct n rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x A)(*strict*)
  apply(case_tac x)
   apply(rename_tac x A)(*strict*)
   apply(clarsimp)
  apply(rename_tac x A nat)(*strict*)
  apply(clarsimp)
  done

lemma Compute_Fixed_Point_Finite_preserve_prop: "
  Q S
  \<Longrightarrow> (\<And>X. Q X \<Longrightarrow> Q (F X))
  \<Longrightarrow> Q (Compute_Fixed_Point_Finite n F S)"
  apply(induct n)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply: "
  F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite (Suc n) F A"
  apply(subgoal_tac "\<forall>A. F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite (Suc n) F A")
   apply(force)
  apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
  done

lemma compute_by_Compute_Fixed_Point_Finite: "
  Compute_Fixed_Point_dom (F,A)
  \<Longrightarrow> \<exists>n. Compute_Fixed_Point F A = Compute_Fixed_Point_Finite n F A \<and> F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite n F A"
  apply(induct rule: Compute_Fixed_Point.pinduct)
  apply(rename_tac F D)(*strict*)
  apply(case_tac "D=F D")
   apply(rename_tac F D)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Compute_Fixed_Point F D"
      and s="D"
      in ssubst)
    apply(rename_tac F D)(*strict*)
    apply(rule_tac
      t="Compute_Fixed_Point F D"
      and s="(if D = F D then D else Compute_Fixed_Point F (F D))" for D F
      in ssubst)
     apply(rename_tac F D)(*strict*)
     apply(rule Compute_Fixed_Point.psimps)
     apply(force)
    apply(rename_tac F D)(*strict*)
    apply(force)
   apply(rename_tac F D)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(force)
  apply(rename_tac F D)(*strict*)
  apply(clarsimp)
  apply(rename_tac F D n)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="Compute_Fixed_Point F D"
      and s="(if D = F D then D else Compute_Fixed_Point F (F D))" for D F
      in ssubst)
   apply(rename_tac F D n)(*strict*)
   apply(rule Compute_Fixed_Point.psimps)
   apply(force)
  apply(rename_tac F D n)(*strict*)
  apply(force)
  done

lemma computation_via_Compute_Fixed_Point_Finite_hlp: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> (F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top = gfp F)
  \<and> (F (Compute_Fixed_Point_Finite n F top) \<noteq> Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top > gfp F)"
  apply(induct n)
   apply(clarsimp)
   apply(rule conjI)
    apply(simp add: gfp_def)
    apply(clarsimp)
    apply(rule order_antisym)
     apply(rule Sup_upper)
     apply(clarsimp)
    apply(clarsimp)
   apply(clarsimp)
   apply(subgoal_tac "mono F")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorX_def mono_def)
   apply (metis gfp_unfold order_less_le top_greatest)
  apply(rename_tac n)(*strict*)
  apply(case_tac "F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F top)"
      and s="F (Compute_Fixed_Point_Finite n F top)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F top)"
      and s="Compute_Fixed_Point_Finite (Suc n) F top"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
    apply(rename_tac n)(*strict*)
    apply(rule sym)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "Compute_Fixed_Point_Finite n F (F top) = F (Compute_Fixed_Point_Finite n F top)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F top)"
      and s="Compute_Fixed_Point_Finite (Suc n) F top"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
    apply(rename_tac n)(*strict*)
    apply(rule sym)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(thin_tac "Compute_Fixed_Point_Finite n F (F top) = F (Compute_Fixed_Point_Finite n F top)")
   apply(subgoal_tac "\<exists>A. A = Compute_Fixed_Point_Finite n F top")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule exE)+
   apply(rename_tac n A)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F top"
      and s="A"
      in ssubst)
    apply(rename_tac n A)(*strict*)
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(subgoal_tac "F A \<noteq> A \<and> F (F A) = F A")
    apply(rename_tac n A)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(subgoal_tac "gfp F < A")
    apply(rename_tac n A)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(thin_tac "F (Compute_Fixed_Point_Finite n F top) \<noteq> Compute_Fixed_Point_Finite n F top")
   apply(thin_tac "F (F (Compute_Fixed_Point_Finite n F top)) = F (Compute_Fixed_Point_Finite n F top)")
   apply(thin_tac "A = Compute_Fixed_Point_Finite n F top")
   apply(thin_tac "gfp F < Compute_Fixed_Point_Finite n F top")
   prefer 2
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "Compute_Fixed_Point_Finite n F (F top) = F (Compute_Fixed_Point_Finite n F top)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F top)"
      and s="Compute_Fixed_Point_Finite (Suc n) F top"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
    apply(rename_tac n)(*strict*)
    apply(rule sym)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(thin_tac "Compute_Fixed_Point_Finite n F (F top) = F (Compute_Fixed_Point_Finite n F top)")
   apply(subgoal_tac "\<exists>A. A = Compute_Fixed_Point_Finite n F top")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule exE)+
   apply(rename_tac n A)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F top"
      and s="A"
      in ssubst)
    apply(rename_tac n A)(*strict*)
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(subgoal_tac "F A \<noteq> A \<and> F (F A) \<noteq> F A")
    apply(rename_tac n A)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(subgoal_tac "gfp F < A")
    apply(rename_tac n A)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n A)(*strict*)
   apply(thin_tac "F (Compute_Fixed_Point_Finite n F top) \<noteq> Compute_Fixed_Point_Finite n F top")
   apply(thin_tac "F (F (Compute_Fixed_Point_Finite n F top)) \<noteq> F (Compute_Fixed_Point_Finite n F top)")
   apply(thin_tac "A = Compute_Fixed_Point_Finite n F top")
   apply(thin_tac "gfp F < Compute_Fixed_Point_Finite n F top")
   apply(erule conjE)+
   apply(rule computation_via_Compute_Fixed_Point_Finite_hlp1)
      apply(rename_tac n A)(*strict*)
      apply(force)+
  apply(rename_tac n A)(*strict*)
  apply(rule computation_via_Compute_Fixed_Point_Finite_hlp2)
     apply(rename_tac n A)(*strict*)
     apply(force)+
  done

lemma computation_via_Compute_Fixed_Point_Finite: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top
  \<Longrightarrow> Compute_Fixed_Point_Finite n F top = gfp F"
  apply(subgoal_tac "(F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top = gfp F) \<and> (F (Compute_Fixed_Point_Finite n F top) \<noteq> Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top > gfp F)")
   apply(force)
  apply(rule computation_via_Compute_Fixed_Point_Finite_hlp)
  apply(force)
  done

lemma computation_via_compute: "
  Characteristic_Fixed_Point_IteratorX F Q
  \<Longrightarrow> Compute_Fixed_Point_dom (F,top)
  \<Longrightarrow> Compute_Fixed_Point F top = (gfp F)"
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point F A = Compute_Fixed_Point_Finite n F A \<and> F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite n F A" for A)
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "Compute_Fixed_Point_dom (F, top)")
  apply(thin_tac "Compute_Fixed_Point F top = Compute_Fixed_Point_Finite n F top")
  apply(rule computation_via_Compute_Fixed_Point_Finite)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma Characteristic_Compute_Fixed_Point_computes_gfp: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm (\<lambda>x. True)
  \<Longrightarrow> Compute_Fixed_Point_dom (F, top)
  \<Longrightarrow> Compute_Fixed_Point F top = gfp F"
  apply(rule computation_via_compute)
   prefer 2
   apply(force)
  apply(simp add: Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator)
  done

theorem Compute_Fixed_Point_computes_gfp: "
  Fixed_Point_Iterator F UNIV Qterm UNIV
  \<Longrightarrow> Compute_Fixed_Point_dom (F, top)
  \<Longrightarrow> Compute_Fixed_Point F top = gfp F"
  apply(rule_tac
      Qterm="\<lambda>x. x\<in> Qterm"
      in Characteristic_Compute_Fixed_Point_computes_gfp)
   prefer 2
   apply(force)
  apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
  apply(force)
  done

lemma gfp_not_fixed_point: "
  F X \<noteq> X
  \<Longrightarrow> mono F
  \<Longrightarrow> gfp F \<noteq> X"
  apply (metis gfp_unfold)
  done

lemma gfp_fixed_point: "
  F X = X
  \<Longrightarrow> X \<le> gfp F"
  apply (metis gfp_upperbound order_eq_refl)
  done

lemma gfp_mixed_fixed_point: "
  (\<And>X. F X \<le> X)
  \<Longrightarrow> (\<And>X Y. X \<le> Y \<Longrightarrow> F X \<le> F Y)
  \<Longrightarrow> F (gfp (\<lambda>X. F (inf X S))) = gfp (\<lambda>X. F (inf X S))"
  apply(rule order_antisym)
   apply(force)
  apply(simp add: gfp_def)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(fold gfp_def)
  apply(subgoal_tac "F (gfp (\<lambda>u. F (inf u S))) \<le> gfp (\<lambda>u. F (inf u S))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "\<And>X. F X \<le> X")
  apply(rule_tac
      q="F(inf x S)"
      in GFP_SOUND_le_trans)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(erule_tac
      x="inf x S"
      in meta_allE)
   apply(erule_tac
      x="gfp (\<lambda>u. F (inf u S))"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "F (gfp (\<lambda>u. F (inf u S))) \<le> gfp (\<lambda>u. F (inf u S))")
   apply(simp add: gfp_def)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply (metis le_infI1)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma Compute_Fixed_Point_Finite_smaller_than_input: "
  (\<And>C. F C \<le> (C::'\<Sigma> DES))
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S \<le> S"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      in meta_allE)
  apply(force)
  done

lemma computation_via_Compute_Fixed_Point_Finite_initial_hlp: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> (F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X (S::'\<Sigma> DES))))
  \<and> (F (Compute_Fixed_Point_Finite n F S) \<noteq> Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S > gfp (\<lambda>X. F (inf X S)))"
  apply(induct n)
   apply(clarsimp)
   apply(case_tac "S=F S")
    apply(clarsimp)
    apply(simp add: gfp_def)
    apply(rule order_antisym)
     apply(rule Sup_upper)
     apply(clarsimp)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      q="F(inf x S)"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      q="F S"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> F X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="inf x S"
      in allE)
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "gfp (\<lambda>X. F (inf X S)) \<noteq> S")
    apply(subgoal_tac "gfp (\<lambda>X. F (inf X S)) \<le> S")
     apply(force)
    apply(simp add: gfp_def)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F (inf x S) \<le> inf x S")
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> F X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="inf x S"
      in allE)
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rule gfp_not_fixed_point)
    apply(force)
   apply(simp add: mono_def)
   apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> (\<forall>Y. UNIVmap Y \<longrightarrow> X \<le> Y \<longrightarrow> F X \<le> F Y))")
    apply(rename_tac x y)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac x y)(*strict*)
   apply(erule_tac
      x="inf x S"
      in allE)
   apply(erule impE)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(rename_tac x y)(*strict*)
   apply(erule_tac
      x="inf y S"
      in allE)
   apply(erule impE)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(rename_tac x y)(*strict*)
   apply(erule impE)
    apply(rename_tac x y)(*strict*)
    apply(clarsimp)
    apply (metis le_infI1)
   apply(rename_tac x y)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(case_tac "F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S")
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="gfp (\<lambda>X. F (inf X S))"
      and s="F (gfp (\<lambda>X. F (inf X S)))"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="gfp (\<lambda>X. F (inf X S))"
      and s="Compute_Fixed_Point_Finite n F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="F (Compute_Fixed_Point_Finite n F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac n)(*strict*)
    apply(rule gfp_fixed_point)
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "Compute_Fixed_Point_Finite (Suc n) F S \<le> S")
     apply(rename_tac n)(*strict*)
     prefer 2
     apply(rule Compute_Fixed_Point_Finite_smaller_than_input)
     apply(rename_tac n C)(*strict*)
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="inf (Compute_Fixed_Point_Finite (Suc n) F S) S"
      and s="(Compute_Fixed_Point_Finite (Suc n) F S)"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply (metis inf_DES_ext_def inf_absorb1)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(clarsimp)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      and P="\<lambda>X. F X < X \<longrightarrow> (\<forall>Y<X. F Y = Y \<longrightarrow> Y \<le> F X)"
      in allE)
   apply(rename_tac n)(*strict*)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      and P="\<lambda>X. F X \<le> X"
      in allE)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule_tac
      x="gfp (\<lambda>X. F (inf X S))"
      and P="\<lambda>x. x < Compute_Fixed_Point_Finite n F S \<longrightarrow> F x = x \<longrightarrow> x \<le> F (Compute_Fixed_Point_Finite n F S)"
      in allE)
   apply(rename_tac n)(*strict*)
   apply(rename_tac n)(*strict*)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(rule gfp_mixed_fixed_point)
     apply(rename_tac n X)(*strict*)
     apply(force)
    apply(rename_tac n X Y)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) \<le> Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) = Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) = Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F S"
      and s="gfp (\<lambda>X. F (inf X S))"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>X. F X \<le> X")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F S) \<le> Compute_Fixed_Point_Finite n F S")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) \<le> Compute_Fixed_Point_Finite n F (F S)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<forall>X. F X \<le> X")
  apply(subgoal_tac "X" for X)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(clarsimp)
  apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      and P="\<lambda>X. F X < X \<longrightarrow> (\<forall>Y<X. F Y = Y \<longrightarrow> Y \<le> F X)"
      in allE)
  apply(rename_tac n)(*strict*)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      and P="\<lambda>X. F X \<le> X"
      in allE)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="gfp (\<lambda>X. F (inf X S))"
      and P="\<lambda>Y. Y < Compute_Fixed_Point_Finite n F S \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F (Compute_Fixed_Point_Finite n F S)"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "F (gfp (\<lambda>X. F (inf X S))) = gfp (\<lambda>X. F (inf X S))")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule gfp_mixed_fixed_point)
    apply(rename_tac n X)(*strict*)
    apply(force)
   apply(rename_tac n X Y)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(case_tac "gfp (\<lambda>X. F (inf X S)) = F (Compute_Fixed_Point_Finite n F S)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply (simp add: Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
  done

lemma computation_via_Compute_Fixed_Point_Finite_initial: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X (S::'\<Sigma> DES)))"
  apply(subgoal_tac "(F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X S))) \<and> (F (Compute_Fixed_Point_Finite n F S) \<noteq> Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S > gfp (\<lambda>X. F (inf X S)))")
   apply(force)
  apply(rule computation_via_Compute_Fixed_Point_Finite_initial_hlp)
  apply(force)
  done

lemma computation_via_compute_initial: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (F, S)
  \<Longrightarrow> Compute_Fixed_Point F S = (gfp (\<lambda>X. F (inf X S)))"
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point F A = Compute_Fixed_Point_Finite n F A \<and> F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite n F A" for A)
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "Compute_Fixed_Point_dom (F, S)")
  apply(thin_tac "Compute_Fixed_Point F S = Compute_Fixed_Point_Finite n F S")
  apply(rule computation_via_Compute_Fixed_Point_Finite_initial)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma Supremum_to_gfp_initial: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (F, S)
  \<Longrightarrow> Compute_Fixed_Point F S = Sup{X. Qterm X \<and> X \<le> S}"
  apply(rule_tac
      t="Sup{X. Qterm X \<and> X \<le> S}"
      and s="(gfp (\<lambda>X. F (inf X S)))"
      in ssubst)
   prefer 2
   apply(rule computation_via_compute_initial)
    apply(force)
   apply(force)
  apply(unfold Characteristic_Fixed_Point_Iterator_def)
  apply(rule_tac
      t="gfp (\<lambda>X. F (inf X S))"
      and s="Sup{u. u \<le> F (inf u S)}"
      in ssubst)
   apply(simp only: gfp_def)
  apply(rule_tac
      t="{X. Qterm X \<and> X \<le> S}"
      and s="{u. u \<le> F (inf u S)}"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply (metis inf_DES_ext_def inf_absorb1)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="inf x S"
      in allE)+
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply (metis le_iff_inf)
  done

theorem Compute_Fixed_Point_computes_Supremum: "
  Fixed_Point_Iterator F UNIV Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (F, S)
  \<Longrightarrow> Compute_Fixed_Point F S = Sup{X. X \<in> Qterm \<and> X \<le> S}"
  apply(rule_tac
      Qterm="\<lambda>x. x\<in> Qterm"
      and Qout="\<lambda>x. x\<in> Qout"
      in Supremum_to_gfp_initial)
   prefer 2
   apply(force)
  apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
  apply(force)
  done

lemma gfp_Decomposition: "
  Characteristic_Fixed_Point_Iterator G UNIVmap Qinter Qinter
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>X. QFout (F X))
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> gfp (F \<circ> G) = gfp (\<lambda>X. F (inf X (G top)))"
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator (F\<circ>G) UNIVmap (predicate_AND Qinter QFterm) QFout")
   prefer 2
   apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
     apply(force)
    apply(rule Characteristic_Fixed_Point_IteratorDec_to_Characteristic_Fixed_Point_Iterator)
    apply(force)
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(subgoal_tac "(\<And>X. X \<le> G top \<Longrightarrow> G (F X) = F X)")
   prefer 2
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "(\<forall>X. Qinter X = (G X = X))")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="F X"
      in allE)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "Qinter (F X)")
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="F X"
      and P="\<lambda>C. (QFout C \<Longrightarrow> Qinter C)"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(thin_tac "\<And>X. QFout (F X)")
  apply(subgoal_tac "(\<And>X. Qinter X \<Longrightarrow> X \<le> G top \<Longrightarrow> G (F X) = F X)")
   prefer 2
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "(\<forall>X. Qinter X = (G X = X))")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="F X"
      in allE)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "Qinter (F X)")
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(erule_tac
      x="F X"
      and P="\<lambda>Y. (QFout Y \<Longrightarrow> Qinter Y)"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac X)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac X)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(simp only: gfp_def)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(fold gfp_def)
   apply(rule_tac
      q="F(G x)"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "(G x) \<le> (inf (gfp (\<lambda>u. F (G u))) (G top))")
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "\<forall>X Y. X \<le> Y \<longrightarrow> F X \<le> F Y")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> (\<forall>Y. UNIVmap Y \<longrightarrow> X \<le> Y \<longrightarrow> G X \<le> G Y))")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="x"
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
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: gfp_def)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(subgoal_tac "x=F (G x)")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "F (G x)\<le>x")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      q="G x"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     apply(subgoal_tac "(\<forall>X. Qinter X \<longrightarrow> F X \<le> X)")
      apply(rename_tac x)(*strict*)
      prefer 2
      apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
     apply(rename_tac x)(*strict*)
     apply(erule_tac
      x="G x"
      in allE)
     apply(erule impE)
      apply(rename_tac x)(*strict*)
      apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> Qinter (G X))")
       apply(rename_tac x)(*strict*)
       prefer 2
       apply(simp add: Characteristic_Fixed_Point_Iterator_def)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> G X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x=G x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "G x\<le>x")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> G X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x \<le> G x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      q="F (G x)"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "(\<forall>X. Qinter X \<longrightarrow> F X \<le> X)")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="G x"
      in allE)
   apply(erule impE)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> Qinter (G X))")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(simp only: gfp_def)
  apply(rule Sup_upper)
  apply(clarsimp)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(fold gfp_def)
  apply(subgoal_tac "x=F (inf x (G top))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(subgoal_tac "F (inf x (G top)) \<le> x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      q="inf x (G top)"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "(\<forall>X. F X \<le> X)")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="inf x (G top)"
      in allE)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<le> gfp (\<lambda>u. F (inf u (G top)))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: gfp_def)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x\<le>G top")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      q="F(inf x (G top))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      q="(inf x (G top))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "(\<forall>X. F X \<le> X)")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="inf x (G top)"
      in allE)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "inf x (G top) = x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply (metis inf_absorb1)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "x \<le> G (gfp (\<lambda>u. F (inf u (G top))))")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "(\<forall>X Y. X \<le> Y \<longrightarrow> F X \<le> F Y)")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      q="F x"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(erule_tac
      x="G (gfp (\<lambda>u. F (inf u (G top))))"
      in allE)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      q="G(F(inf (gfp (\<lambda>u. F (inf u (G top)))) (G top)))"
      in GFP_SOUND_le_trans)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(subgoal_tac "(F (inf (gfp (\<lambda>u. F (inf u (G top)))) (G top))) \<le> (gfp (\<lambda>u. F (inf u (G top))))")
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> (\<forall>Y. UNIVmap Y \<longrightarrow> X \<le> Y \<longrightarrow> G X \<le> G Y))")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_Iterator_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="F (inf (gfp (\<lambda>u. F (inf u (G top)))) (G top))"
      in allE)
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="gfp (\<lambda>u. F (inf u (G top)))"
      in allE)
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      q="(inf (gfp (\<lambda>u. F (inf u (G top)))) (G top))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. F X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="(inf (gfp (\<lambda>u. F (inf u (G top)))) (G top))"
      in allE)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply (rule inf_le1)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="G (F (inf (gfp (\<lambda>u. F (inf u (G top)))) (G top)))"
      and s="(F (inf (gfp (\<lambda>u. F (inf u (G top)))) (G top)))"
      in ssubst)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      q="gfp (\<lambda>u. F (inf u (G top)))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: gfp_def)
   apply(rule Sup_least)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(fold gfp_def)
   apply(rule_tac
      q="F (inf xa (G top))"
      in GFP_SOUND_le_trans)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(subgoal_tac "(inf xa (G top)) \<le> (inf (gfp (\<lambda>u. F (inf u (G top)))) (G top))")
    apply(rename_tac x xa)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(simp add: gfp_def)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule_tac
      t="inf (inf xa (G top)) (G top)"
      and s="inf xa (G top)"
      in ssubst)
    apply(rename_tac x xa)(*strict*)
    apply (metis inf_absorb1 inf_le2)
   apply(rename_tac x xa)(*strict*)
   apply (metis le_infI1)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="inf (gfp (\<lambda>u. F (inf u (G top)))) (G top)"
      and P="\<lambda>X. (X \<le> G top \<Longrightarrow> G (F X) = F X)"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply (metis inf_le2)
  done

lemma Characteristic_Fixed_Point_Iterator_to_Characteristic_Fixed_Point_IteratorX: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorX F Qterm"
  apply(simp add: Characteristic_Fixed_Point_IteratorX_def Characteristic_Fixed_Point_Iterator_def)
  done

lemma Compute_Fixed_Point_Finite_reaches_Qinter: "
  Qinter S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> Qinter (Compute_Fixed_Point_Finite n F S)"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n C)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s="F (Compute_Fixed_Point_Finite n F S)"
      and t="Compute_Fixed_Point_Finite (Suc n) F S"
      in subst)
   apply(rename_tac n)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="F (Compute_Fixed_Point_Finite n F S)"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "(\<forall>X. Qinter X \<longrightarrow> QFout (F X))")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma computation_via_Compute_Fixed_Point_Finite_initialDec_hlp: "
  Qinter S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> Qinter (gfp (\<lambda>X. F (inf X S)))
  \<Longrightarrow> (F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X S)))
  \<and> (F (Compute_Fixed_Point_Finite n F S) \<noteq> Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S > gfp (\<lambda>X. F (inf X (S::'\<Sigma> DES))))"
  apply(induct n)
   apply(clarsimp)
   apply(case_tac "S=F S")
    apply(clarsimp)
    apply(simp add: gfp_def)
    apply(rule order_antisym)
     apply(rule Sup_upper)
     apply(clarsimp)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      q="F(inf x S)"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      q="F S"
      in GFP_SOUND_le_trans)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> F X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="inf x S"
      in allE)
    apply(erule impE)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "gfp (\<lambda>X. F (inf X S)) \<noteq> S")
    apply(subgoal_tac "gfp (\<lambda>X. F (inf X S)) \<le> S")
     apply(force)
    apply(simp add: gfp_def)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(fold gfp_def)
    apply(subgoal_tac "F (inf x S) \<le> inf x S")
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "(\<forall>X. F X \<le> X)")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac x)(*strict*)
    apply(erule_tac
      x="inf x S"
      in allE)
    apply(clarsimp)
   apply(rule gfp_not_fixed_point)
    apply(force)
   apply(simp add: mono_def)
   apply(clarsimp)
   apply(rename_tac x y)(*strict*)
   apply(subgoal_tac "\<forall>X Y. X \<le> Y \<longrightarrow> F X \<le> F Y")
    apply(rename_tac x y)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac x y)(*strict*)
   apply(erule_tac
      x="inf x S"
      in allE)
   apply(erule_tac
      x="inf y S"
      in allE)
   apply (metis inf_le2 le_infI1 le_inf_iff)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n C)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(case_tac "F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S")
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="gfp (\<lambda>X. F (inf X S))"
      and s="F (gfp (\<lambda>X. F (inf X S)))"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="gfp (\<lambda>X. F (inf X S))"
      and s="Compute_Fixed_Point_Finite n F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="F (Compute_Fixed_Point_Finite n F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac n)(*strict*)
    apply(rule gfp_fixed_point)
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "Compute_Fixed_Point_Finite (Suc n) F S \<le> S")
     apply(rename_tac n)(*strict*)
     prefer 2
     apply(rule Compute_Fixed_Point_Finite_smaller_than_input)
     apply(rename_tac n C)(*strict*)
     apply(subgoal_tac "\<forall>X. F X \<le> X")
      apply(rename_tac n C)(*strict*)
      prefer 2
      apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
     apply(rename_tac n C)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="inf (Compute_Fixed_Point_Finite (Suc n) F S) S"
      and s="(Compute_Fixed_Point_Finite (Suc n) F S)"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply (metis inf_DES_ext_def inf_absorb1)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule Characteristic_Fixed_Point_IteratorDec_does_not_skip_Fixed_Points)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      in allE)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(rule Compute_Fixed_Point_Finite_reaches_Qinter)
      apply(rename_tac n)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n C)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "(\<forall>X. F X \<le> X)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac n)(*strict*)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      in allE)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule_tac
      x="gfp (\<lambda>X. F (inf X S))"
      and P="\<lambda>Y. Qinter Y \<longrightarrow> Y < Compute_Fixed_Point_Finite n F S \<longrightarrow> F Y = Y \<longrightarrow> Y \<le> F (Compute_Fixed_Point_Finite n F S)"
      in allE)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(erule impE)
     apply(rename_tac n)(*strict*)
     apply(rule gfp_mixed_fixed_point)
      apply(rename_tac n X)(*strict*)
      apply(force)
     apply(rename_tac n X Y)(*strict*)
     apply(subgoal_tac "(\<forall>X Y. X \<le> Y \<longrightarrow> F X \<le> F Y)")
      apply(rename_tac n X Y)(*strict*)
      prefer 2
      apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
     apply(rename_tac n X Y)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
     apply(rename_tac n)(*strict*)
     apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) \<le> Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(subgoal_tac "(\<forall>X. F X \<le> X)")
     apply(rename_tac n)(*strict*)
     prefer 2
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) = Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) = Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F S"
      and s="gfp (\<lambda>X. F (inf X S))"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>X. F X \<le> X")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F S) \<le> Compute_Fixed_Point_Finite n F S")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) \<le> Compute_Fixed_Point_Finite n F (F S)")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<forall>X. F X \<le> X")
  apply(subgoal_tac "X" for X)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule Characteristic_Fixed_Point_IteratorDec_does_not_skip_Fixed_Points)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="Compute_Fixed_Point_Finite n F S"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_reaches_Qinter)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n C)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply (metis xt1(11))
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="gfp (\<lambda>X. F (inf X S))"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
  apply(rename_tac n)(*strict*)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(case_tac "gfp (\<lambda>X. F (inf X S)) = F (Compute_Fixed_Point_Finite n F S)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F (gfp (\<lambda>X. F (inf X S))) = gfp (\<lambda>X. F (inf X S))")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule gfp_mixed_fixed_point)
     apply(rename_tac n X)(*strict*)
     apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
    apply(rename_tac n X Y)(*strict*)
    apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F (Compute_Fixed_Point_Finite n F (F S)) = Compute_Fixed_Point_Finite n F (F S)")
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_pre_apply)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F S"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply_hlp)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule gfp_mixed_fixed_point)
   apply(rename_tac n X)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
  apply(rename_tac n X Y)(*strict*)
  apply(simp add: Characteristic_Fixed_Point_IteratorDec_def)
  done

lemma computation_via_Compute_Fixed_Point_Finite_initialDec: "
  Qinter S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> Qinter (gfp (\<lambda>X. F (inf X S)))
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X (S::'\<Sigma> DES)))"
  apply(subgoal_tac "(F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S = gfp (\<lambda>X. F (inf X S))) \<and> (F (Compute_Fixed_Point_Finite n F S) \<noteq> Compute_Fixed_Point_Finite n F S \<longrightarrow> Compute_Fixed_Point_Finite n F S > gfp (\<lambda>X. F (inf X S)))")
   apply(force)
  apply(rule_tac
      QFout="QFout"
      in computation_via_Compute_Fixed_Point_Finite_initialDec_hlp)
     prefer 2
     apply(force)+
  done

lemma computation_via_compute_initialDec: "
  Qinter S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> Qinter (gfp (\<lambda>X. F (inf X S)))
  \<Longrightarrow> Compute_Fixed_Point_dom (F,S)
  \<Longrightarrow> Compute_Fixed_Point F S = (gfp (\<lambda>X. F (inf X S)))"
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point F A = Compute_Fixed_Point_Finite n F A \<and> F (Compute_Fixed_Point_Finite n F A) = Compute_Fixed_Point_Finite n F A" for A)
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "Compute_Fixed_Point_dom (F, S)")
  apply(thin_tac "Compute_Fixed_Point F S = Compute_Fixed_Point_Finite n F S")
  apply(rule computation_via_Compute_Fixed_Point_Finite_initialDec)
      apply(rename_tac n)(*strict*)
      prefer 2
      apply(force)+
  done

lemma Supremum_to_gfp_initialDec: "
  Characteristic_Fixed_Point_Iterator G UNIVmap Qinter Qinter
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorDec F Qinter QFterm QFout
  \<Longrightarrow> (\<And>C. QFterm C \<Longrightarrow> Qinter C)
  \<Longrightarrow> (\<And>X. QFout (F X))
  \<Longrightarrow> (\<And>C. QFout C \<Longrightarrow> Qinter C)
  \<Longrightarrow> Qinter (gfp (\<lambda>X. F (inf X (G top))))
  \<Longrightarrow> Compute_Fixed_Point_dom (F,G top)
  \<Longrightarrow> Compute_Fixed_Point F (G top) = Sup{X. QFterm X \<and> X \<le> G top}"
  apply(rule_tac
      t="Sup{X. QFterm X \<and> X \<le> G top}"
      and s="(gfp (\<lambda>X. F (inf X (G top))))"
      in ssubst)
   prefer 2
   apply(rule computation_via_compute_initialDec)
       prefer 2
       apply(force)
      apply(simp add: Characteristic_Fixed_Point_Iterator_def)
      apply(clarsimp)
     apply(rename_tac C)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="gfp (\<lambda>X. F (inf X (G top)))"
      and s="gfp (F \<circ> G)"
      in subst)
   apply(rule gfp_Decomposition)
      apply(force)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(force)
  apply(subgoal_tac "Characteristic_Fixed_Point_Iterator (F\<circ>G) UNIVmap (predicate_AND Qinter QFterm) QFout")
   prefer 2
   apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
     apply(force)
    apply(rule Characteristic_Fixed_Point_IteratorDec_to_Characteristic_Fixed_Point_Iterator)
    apply(force)
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      t="gfp (F\<circ>G)"
      and s="Sup{X. (\<lambda>X. Qinter X \<and> QFterm X) X}"
      in subst)
   apply(rule Supremum_to_gfp)
   apply(rule Characteristic_Fixed_Point_Iterator_to_Characteristic_Fixed_Point_IteratorX)
   apply(force)
  apply(rule_tac
      t="{X. QFterm X \<and> X \<le> G top}"
      and s="{u. Qinter u \<and> QFterm u}"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "Qinter x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      q="G x"
      in GFP_SOUND_le_trans)
   apply(rename_tac x)(*strict*)
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "(\<forall>X. UNIVmap X \<longrightarrow> (\<forall>Y. UNIVmap Y \<longrightarrow> X \<le> Y \<longrightarrow> G X \<le> G Y))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma Compute_Fixed_Point_Finite_invariant_after_fixed_point: "
  Compute_Fixed_Point_Finite n F A = F (Compute_Fixed_Point_Finite n F A)
  \<Longrightarrow> n\<le>na
  \<Longrightarrow> Compute_Fixed_Point_Finite n F A = Compute_Fixed_Point_Finite na F A"
  apply(induct "na-n" arbitrary: na)
   apply(rename_tac na)(*strict*)
   apply(clarsimp)
  apply(rename_tac x na)(*strict*)
  apply(clarsimp)
  apply(case_tac na)
   apply(rename_tac x na)(*strict*)
   apply(force)
  apply(rename_tac x na nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x nat)(*strict*)
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x nat)(*strict*)
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite nat F (F A)"
      and s="Compute_Fixed_Point_Finite (Suc nat) F A"
      in ssubst)
   apply(rename_tac x nat)(*strict*)
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc nat) F A"
      and s="F (Compute_Fixed_Point_Finite nat F A)"
      in ssubst)
   apply(rename_tac x nat)(*strict*)
   defer
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(rule sym)
  apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  done

lemma EqualCompute_initial: "
  (\<And>C. Q C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. Q (Compute_Fixed_Point_Finite n F S))
  \<Longrightarrow> Qinp S
  \<Longrightarrow> (\<And>C. Qout C \<Longrightarrow> Qinp C)
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S \<and> Q (Compute_Fixed_Point_Finite n F S)"
  apply(induct n)
   apply(clarsimp)
   apply(erule_tac
      x="0"
      in meta_allE)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F (F S)"
      and s="F (Compute_Fixed_Point_Finite n F S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="F (Compute_Fixed_Point_Finite n F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n G (G S)"
      and s="G (Compute_Fixed_Point_Finite n G S)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      t="G (Compute_Fixed_Point_Finite n G S)"
      and s="Compute_Fixed_Point_Finite (Suc n) G S"
      in ssubst)
    apply(rename_tac n)(*strict*)
    apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n G S"
      and s="Compute_Fixed_Point_Finite n F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(erule_tac
      x="n"
      in meta_allE)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="n+1"
      in meta_allE)
  apply(rule_tac
      t="F (Compute_Fixed_Point_Finite n F S)"
      and s="Compute_Fixed_Point_Finite (Suc n) F S"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma equal_computation_via_compute: "
  (\<And>C. QFdom C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. QFdom (Compute_Fixed_Point_Finite n F S))
  \<Longrightarrow> Compute_Fixed_Point_dom (F,S)
  \<Longrightarrow> Compute_Fixed_Point_dom (G,S)
  \<Longrightarrow> Compute_Fixed_Point F S = Compute_Fixed_Point G S"
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point F S = Compute_Fixed_Point_Finite n F S \<and> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S")
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(blast)
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point G S = Compute_Fixed_Point_Finite n G S \<and> G (Compute_Fixed_Point_Finite n G S) = Compute_Fixed_Point_Finite n G S")
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac n na)(*strict*)
  apply(subgoal_tac "\<forall>n. Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S \<and> QFdom (Compute_Fixed_Point_Finite n F S)")
   apply(rename_tac n na)(*strict*)
   prefer 2
   apply(rule allI)
   apply(rename_tac n na nb)(*strict*)
   apply(rule EqualCompute_initial)
      apply(rename_tac n na nb C)(*strict*)
      apply(force)
     apply(rename_tac n na nb nc)(*strict*)
     apply(force)
    apply(rename_tac n na nb)(*strict*)
    apply(force)
   apply(rename_tac n na nb C)(*strict*)
   apply(force)
  apply(rename_tac n na)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Compute_Fixed_Point_Finite n G S = Compute_Fixed_Point_Finite na G S")
   apply(rename_tac n na)(*strict*)
   apply(subgoal_tac "Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite na F S")
    apply(rename_tac n na)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na)(*strict*)
   apply(clarsimp)
  apply(rename_tac n na)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(case_tac "n<na")
   apply(rename_tac n na)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_invariant_after_fixed_point)
    apply(rename_tac n na)(*strict*)
    apply(force)
   apply(rename_tac n na)(*strict*)
   apply(force)
  apply(rename_tac n na)(*strict*)
  apply(rule sym)
  apply(rule Compute_Fixed_Point_Finite_invariant_after_fixed_point)
   apply(rename_tac n na)(*strict*)
   apply(force)
  apply(rename_tac n na)(*strict*)
  apply(force)
  done

lemma computeterm_by_Compute_Fixed_Point_Finite_hlp: "
  F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S
  \<Longrightarrow> Qinp (Compute_Fixed_Point_Finite n F S)
  \<Longrightarrow> (\<And>C. Qinp C \<Longrightarrow> F C = G C)
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> Compute_Fixed_Point_dom (G,Compute_Fixed_Point_Finite (n-m) G S)"
  apply(induct m)
   apply(clarsimp)
   apply(rule Compute_Fixed_Point.domintros)
   apply(subgoal_tac "Compute_Fixed_Point_Finite n G S = G (Compute_Fixed_Point_Finite n G S)")
    apply(force)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite n G S"
      in meta_allE)
   apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(rule Compute_Fixed_Point.domintros)
  apply(rule_tac
      t="G (Compute_Fixed_Point_Finite (n - Suc m) G S)"
      and s="(Compute_Fixed_Point_Finite (Suc (n - Suc m)) G S)"
      in ssubst)
   apply(rename_tac m)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac m)(*strict*)
  apply(rule_tac
      t="(Suc (n - Suc m))"
      and s="n-m"
      in ssubst)
   apply(rename_tac m)(*strict*)
   apply(force)
  apply(rename_tac m)(*strict*)
  apply(force)
  done

lemma computeterm_by_Compute_Fixed_Point_Finite: "
  (\<And>C. Q C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. Q (Compute_Fixed_Point_Finite n F S))
  \<Longrightarrow> Compute_Fixed_Point F S = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_dom (G,S)"
  apply(subgoal_tac "\<forall>n. Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S \<and> Q (Compute_Fixed_Point_Finite n F S)")
   prefer 2
   apply(rule allI)
   apply(rename_tac na)(*strict*)
   apply(rule EqualCompute_initial)
      apply(rename_tac na C)(*strict*)
      apply(force)
     apply(rename_tac na naa)(*strict*)
     apply(force)
    apply(rename_tac na)(*strict*)
    apply(force)
   apply(rename_tac na C)(*strict*)
   apply(force)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      t="S"
      and s="Compute_Fixed_Point_Finite (n-n) G S"
      in ssubst)
   apply(force)
  apply(rule_tac
      F="F"
      and Qinp="Q"
      in computeterm_by_Compute_Fixed_Point_Finite_hlp)
      apply(force)
     apply(force)
    prefer 2
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(erule_tac
      x="n"
      in meta_allE)
   apply(force)
  apply(force)
  done

lemma computation_via_compute2: "
  Characteristic_Fixed_Point_IteratorX G Q
  \<Longrightarrow> (\<And>C. QFdom C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. QFdom (Compute_Fixed_Point_Finite n F top))
  \<Longrightarrow> Compute_Fixed_Point_dom (F,top)
  \<Longrightarrow> Compute_Fixed_Point F top = Sup {X. Q X}"
  apply(rule_tac
      t="Sup {X. Q X}"
      and s="gfp G"
      in ssubst)
   apply(rule Supremum_to_gfp)
   apply(force)
  apply(subgoal_tac "Compute_Fixed_Point_dom (F,top) \<and> Compute_Fixed_Point_dom (G,top)")
   apply(rule_tac
      t="Compute_Fixed_Point F top"
      and s="Compute_Fixed_Point G top"
      in ssubst)
    apply(rule_tac equal_computation_via_compute)
       apply(rename_tac C)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac C)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(force)
   apply(rule computation_via_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n. Compute_Fixed_Point F top = Compute_Fixed_Point_Finite n F top \<and> F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top")
   prefer 2
   apply(rule compute_by_Compute_Fixed_Point_Finite)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule computeterm_by_Compute_Fixed_Point_Finite)
     apply(rename_tac n C)(*strict*)
     prefer 3
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n C)(*strict*)
    apply(force)
   apply(rename_tac n na)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma computeterm_by_Compute_Fixed_Point_Finite_initial_hlp: "
  Compute_Fixed_Point F S = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S
  \<Longrightarrow> Qinp (Compute_Fixed_Point_Finite n F S)
  \<Longrightarrow> (\<And>C. Qinp C \<Longrightarrow> F C = G C)
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> Compute_Fixed_Point_dom (G,Compute_Fixed_Point_Finite (n-m) G S)"
  apply(induct m)
   apply(clarsimp)
   apply(rule Compute_Fixed_Point.domintros)
   apply(subgoal_tac "Compute_Fixed_Point_Finite n G S = G (Compute_Fixed_Point_Finite n G S)")
    apply(force)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite n G S"
      in meta_allE)
   apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(rule Compute_Fixed_Point.domintros)
  apply(rule_tac
      t="G (Compute_Fixed_Point_Finite (n - Suc m) G S)"
      and s="(Compute_Fixed_Point_Finite (Suc (n - Suc m)) G S)"
      in ssubst)
   apply(rename_tac m)(*strict*)
   apply(rule Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac m)(*strict*)
  apply(rule_tac
      t="(Suc (n - Suc m))"
      and s="n-m"
      in ssubst)
   apply(rename_tac m)(*strict*)
   apply(force)
  apply(rename_tac m)(*strict*)
  apply(force)
  done

lemma computeterm_by_compute_initialN: "
  (\<And>C. QFdom C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. QFdom (Compute_Fixed_Point_Finite n F S))
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F S) = Compute_Fixed_Point_Finite n F S
  \<Longrightarrow> Compute_Fixed_Point_dom (G,S)"
  apply(subgoal_tac "\<forall>n. Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S \<and> QFdom (Compute_Fixed_Point_Finite n F S)")
   prefer 2
   apply(rule allI)
   apply(rename_tac na)(*strict*)
   apply(rule EqualCompute_initial)
      apply(rename_tac na C)(*strict*)
      apply(erule_tac
      x="n"
      in meta_allE)
      apply(force)
     apply(rename_tac na naa)(*strict*)
     apply(force)
    apply(rename_tac na)(*strict*)
    apply(force)
   apply(rename_tac na C)(*strict*)
   apply(force)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      t="S"
      and s="Compute_Fixed_Point_Finite (n-n) G S"
      in ssubst)
   apply(force)
  apply(rule_tac
      F="F"
      and Qinp="QFdom"
      in computeterm_by_Compute_Fixed_Point_Finite_hlp)
      apply(force)
     apply(force)
    apply(erule_tac
      x="n"
      in meta_allE)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(force)
  apply(force)
  done

lemma Supremum_to_gfp_initialTranslate: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (G,S)
  \<Longrightarrow> (\<And>n. Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S)
  \<Longrightarrow> (\<And>C. QFdom C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>n. QFdom (Compute_Fixed_Point_Finite n F S))
  \<Longrightarrow> Compute_Fixed_Point G S = Sup{X. Qterm X \<and> X \<le> S}"
  apply(subgoal_tac "Compute_Fixed_Point_dom (F,S)")
   prefer 2
   apply(subgoal_tac "\<exists>n. Compute_Fixed_Point G S = Compute_Fixed_Point_Finite n G S \<and> G (Compute_Fixed_Point_Finite n G S) = Compute_Fixed_Point_Finite n G S")
    prefer 2
    apply(rule compute_by_Compute_Fixed_Point_Finite)
    apply(blast)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(rule_tac
      Q="QFdom"
      and F="G"
      in computeterm_by_Compute_Fixed_Point_Finite)
      apply(rename_tac n C)(*strict*)
      apply(force)
     apply(rename_tac n na)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rule_tac
      t="Sup{X. Qterm X \<and> X \<le> S}"
      and s="Compute_Fixed_Point F S"
      in subst)
   apply(rule Supremum_to_gfp_initial)
    apply(force)
   apply(force)
  apply(rule_tac
      QFdom="QFdom"
      in equal_computation_via_compute)
     apply(rename_tac C)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(force)
  done

lemma Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1: "
  Characteristic_Fixed_Point_Iterator F UNIVmap Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (G, S)
  \<Longrightarrow> (\<And>C. Qinp C \<Longrightarrow> F C = G C)
  \<Longrightarrow> (\<And>C. Qinp C \<Longrightarrow> Qinp (F C))
  \<Longrightarrow> Qinp S
  \<Longrightarrow> Compute_Fixed_Point G S = Sup{X. Qterm X \<and> X \<le> S}"
  apply(subgoal_tac "(\<And>n. Qinp (Compute_Fixed_Point_Finite n F S))")
   prefer 2
   apply(rename_tac n)(*strict*)
   apply(induct_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na)(*strict*)
   apply(erule_tac
      x="Compute_Fixed_Point_Finite na F S"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac na)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_preserve_prop)
  apply(subgoal_tac "(\<And>n. Compute_Fixed_Point_Finite n F S = Compute_Fixed_Point_Finite n G S)")
   prefer 2
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule_tac
      F="F"
      and G="G"
      and Q="Qinp"
      in EqualCompute_initial)
       apply(rename_tac n C)(*strict*)
       apply(force)
      apply(rename_tac n na)(*strict*)
      apply(force)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n C)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rule Supremum_to_gfp_initialTranslate)
      apply(force)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

theorem Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator: "
  Fixed_Point_Iterator G UNIV Qterm Qout
  \<Longrightarrow> S \<in> Qinp
  \<Longrightarrow> (\<And>C. C \<in> Qinp \<Longrightarrow> G C \<in> Qinp)
  \<Longrightarrow> (\<And>C. C \<in> Qinp \<Longrightarrow> G C = F C)
  \<Longrightarrow> Compute_Fixed_Point_dom (F, S)
  \<Longrightarrow> Compute_Fixed_Point F S = Sup{X. X \<in> Qterm \<and> X \<le> S}"
  apply(subgoal_tac "Compute_Fixed_Point F S = Sup{X. (\<lambda>x. x \<in> Qterm) X \<and> X \<le> S}")
   apply(force)
  apply(rule_tac
      F="G"
      and G="F"
      and Qout="\<lambda>x. x\<in> Qout"
      and Qinp="\<lambda>x. x\<in> Qinp"
      in Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator1)
      apply (metis (mono_tags) Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1 Collect_mem_eq UNIV_eq_I UNIVmap_def mem_Collect_eq)
     apply(force)
    apply(rename_tac C)(*strict*)
    apply(force)
   apply(rename_tac C)(*strict*)
   apply(force)
  apply(force)
  done

theorem Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator2: "
  Fixed_Point_Iterator G UNIV Qterm Qout
  \<Longrightarrow> S \<in> Qinp
  \<Longrightarrow> Qout \<subseteq> Qinp
  \<Longrightarrow> (\<And>C. C \<in> Qinp \<Longrightarrow> G C = F C)
  \<Longrightarrow> Compute_Fixed_Point_dom (F, S)
  \<Longrightarrow> Compute_Fixed_Point F S = Sup{X. X \<in> Qterm \<and> X \<le> S}"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Compute_Fixed_Point_computes_Supremum_using_Equivalent_Iterator)
       apply(force) 
      apply(force)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(simp add: Fixed_Point_Iterator_def)
   apply(erule_tac x="C" in allE) 
   apply(force)
  apply(force)
  done



corollary gfp_properties_using_monotonicity: "
  mono F
  \<Longrightarrow> gfp F = Sup{A. A = F A} \<and> gfp F = F (gfp F)"
  apply(rule conjI)
   prefer 2
   apply (metis gfp_unfold)
  apply(simp add: gfp_def)
  apply(rule antisym)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply(rule antisym)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply (metis gfp_def gfp_unfold gfp_upperbound)
   apply(rule Sup_upper)
   apply(clarsimp)
   apply (metis gfp_def gfp_unfold order_refl)
  apply(rule Sup_least)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule Sup_upper)
  apply(clarsimp)
  done

definition des_langM_update :: "'a DES \<Rightarrow> 'a list set \<Rightarrow> 'a DES" where
  "des_langM_update D L = (DES (des_langUM D) L)"

definition des_langUM_update :: "'a DES \<Rightarrow> 'a list set \<Rightarrow> 'a DES" where
  "des_langUM_update D L = (DES L (des_langM D))"

lemma helpXX: "
x \<in> A
 \<longrightarrow> finite {n. (\<exists>w\<in> A. length w = n) \<and> n \<le> length x}
 \<longrightarrow> {n. \<exists>w\<in> A. length w = n \<and> n \<le> length x} \<noteq> {}
 \<longrightarrow> {n. \<exists>w\<in> A. length w = n \<and> n \<le> length x} \<subseteq> length ` A
 \<longrightarrow> (\<exists>w\<in> A. length w = Min {n. \<exists>w\<in> A. length w = n \<and> n \<le> length x})"
  apply(rule_tac
      x="{n. \<exists>w\<in> A. length w = n \<and> n \<le> length x}"
      in Finite_Set.finite.induct)
    apply(clarsimp)
   apply(clarsimp)
  apply(rename_tac Aa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac Aa xa)(*strict*)
  apply(case_tac "Aa={}")
   apply(rename_tac Aa xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac Aa xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Aa xa w)(*strict*)
  apply(case_tac "(length xa) \<le> (Min Aa)")
   apply(rename_tac Aa xa w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="xa"
      in bexI)
    apply(rename_tac Aa xa w)(*strict*)
    apply (metis Min_in min.absorb2 min.commute)
   apply(rename_tac Aa xa w)(*strict*)
   apply(force)
  apply(rename_tac Aa xa w)(*strict*)
  apply (metis min_def)
  done

lemma nonempty_language_has_some_shortest_word: "
  x\<in> A
  \<Longrightarrow> \<exists>w\<in> A. \<forall>w'\<in> A. length w\<le>length w'"
  apply(subgoal_tac "finite {n. (\<exists>w\<in> A. length w = n) \<and> n \<le> length x}")
   prefer 2
   apply(force)
  apply(subgoal_tac "\<exists>w\<in> A. length w = Min {n. \<exists>w\<in> A. length w=n \<and> n\<le>length x}")
   apply(erule bexE)+
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="w"
      in bexI)
    apply(rename_tac w)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule ballI)
   apply(rename_tac w w')(*strict*)
   apply(clarsimp)
   apply(case_tac "length x \<le> length w'")
    apply(rename_tac w w')(*strict*)
    apply(rule_tac
      j="length x"
      in le_trans)
     apply(rename_tac w w')(*strict*)
     apply(rule Min_le)
      apply(rename_tac w w')(*strict*)
      apply(force)
     apply(rename_tac w w')(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac w w')(*strict*)
    apply(force)
   apply(rename_tac w w')(*strict*)
   apply(rule Min_le)
    apply(rename_tac w w')(*strict*)
    apply(force)
   apply(rename_tac w w')(*strict*)
   apply(clarsimp)
   apply(force)
  apply(subgoal_tac "{n. \<exists>w\<in> A. length w = n \<and> n \<le> length x}\<noteq>{}")
   prefer 2
   apply(force)
  apply(subgoal_tac "{n. \<exists>w\<in> A. length w = n \<and> n \<le> length x}\<subseteq> length`A")
   prefer 2
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      A="A"
      in helpXX)
  apply(force)
  done

corollary infinite_computation_of_fixed_point: "
  F = (\<lambda>X.
  (DES (des_langUM X) (
  (des_langM X-{w. w\<in> des_langM X \<and> (\<forall>w'. length w'<length w \<longrightarrow> w'\<notin> des_langM X)}
  ))))
  \<Longrightarrow> mono F
  \<and> (\<forall>C. F C \<le> C)
  \<and> gfp F = DES top bot
  \<and> Compute_Fixed_Point_Finite n F top = DES top {w. length w \<ge> n}
  \<and> F (Compute_Fixed_Point_Finite n F top) < Compute_Fixed_Point_Finite n F top"
  apply(rule conjI)
   apply(simp add: mono_def)
   apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
   apply(clarsimp)
   apply(rename_tac x y xa w')(*strict*)
   apply(case_tac x)
   apply(rename_tac x y xa w' set1 set2)(*strict*)
   apply(case_tac y)
   apply(rename_tac x y xa w' set1 set2 set1a set2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa w' set1 set2 set1a set2a)(*strict*)
   apply(force)
  apply(rule context_conjI)
   apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(unfold gfp_def)
   apply(rule antisym)
    apply(rule Sup_least)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
    apply(case_tac x)
    apply(rename_tac x set1 set2)(*strict*)
    apply(clarsimp)
    apply(rename_tac set2)(*strict*)
    apply(rule antisym)
     apply(rename_tac set2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac set2)(*strict*)
    apply(rule subsetI)
    apply(rename_tac set2 x)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac set2 x)(*strict*)
     prefer 2
     apply(rule_tac
      A="set2"
      in nonempty_language_has_some_shortest_word)
     apply(force)
    apply(rename_tac set2 x)(*strict*)
    apply(clarsimp)
    apply(rename_tac set2 x w)(*strict*)
    apply(force)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(induct n)
   apply(clarsimp)
   apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
   apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F top"
      and s="F (Compute_Fixed_Point_Finite n F top)"
      in ssubst)
    apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
   apply(clarsimp)
   apply(case_tac "{w. \<forall>w'. \<not> length w' < length w} = {}")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite (Suc n) F top"
      and s="F (Compute_Fixed_Point_Finite n F top)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply (metis Compute_Fixed_Point_Finite_FB_iterate_vs_post_apply)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      t="Compute_Fixed_Point_Finite n F top"
      and s="DES UNIV {w. n \<le> length w}"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(thin_tac " (F = (\<lambda>X. DES (des_langUM X) (des_langM X - {w \<in> des_langM X. \<forall>w'. length w' < length w \<longrightarrow> w' \<notin> des_langM X})) \<Longrightarrow> \<forall>C. F C \<le> C \<Longrightarrow> Compute_Fixed_Point_Finite n F top = DES UNIV {w. n \<le> length w} \<and> F (Compute_Fixed_Point_Finite n F top) < Compute_Fixed_Point_Finite n F top)")
  apply(rule context_conjI)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def des_langM_update_def)
   apply(rule antisym)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n x)(*strict*)
   apply(case_tac x)
    apply(rename_tac n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n x a list)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(case_tac "F (F (DES UNIV {w. n \<le> length w})) = F (DES UNIV {w. n \<le> length w})")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply (metis less_le)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<forall>C. F C \<le> C")
  apply(clarsimp)
  apply(thin_tac "{w. n \<le> length w} - {w. n \<le> length w \<and> (\<forall>w'. length w' < length w \<longrightarrow> \<not> n \<le> length w')} = {w. Suc n \<le> length w}")
  apply(case_tac "{w. Suc n \<le> length w \<and> (\<forall>w'. length w' < length w \<longrightarrow> \<not> Suc n \<le> length w')}={}")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac n x)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply (metis Ex_list_of_length lessI less_eq_Suc_le_raw not_less_eq)
  done

lemma orthogonality1: "
  subtop = DES UNIV (UNIV - {[]})
  \<Longrightarrow> F = (\<lambda>X. if X = subtop then top else X)
  \<Longrightarrow> mono F \<and> subtop < F subtop"
  apply(clarsimp)
  apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac y x)(*strict*)
   apply(case_tac y)
   apply(rename_tac y x set1 set2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x set1 set2)(*strict*)
   apply(erule impE)
    apply(rename_tac x set1 set2)(*strict*)
    apply(force)
   apply(rename_tac x set1 set2)(*strict*)
   apply(case_tac "x=[]")
    apply(rename_tac x set1 set2)(*strict*)
    apply(clarsimp)
   apply(rename_tac x set1 set2)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(force)
  done

lemma orthogonality2: "
  F = (\<lambda>X::'\<Sigma> DES. if X = top then bot else X)
  \<Longrightarrow> \<not> mono F \<and> (\<forall>C. F C \<le> C)"
  apply(rule conjI)
   apply(simp add: mono_def)
   apply(clarsimp)
   apply(rule_tac
      x="DES UNIV (UNIV - {[]})"
      in exI)
   apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def)
   apply(force)
  apply(force)
  done

corollary orthogonality_of_monotonicity_and_decreasing_arguments: "
  subtop = DES top (top - {[]})
  \<Longrightarrow> F1 = (\<lambda>X::'\<Sigma> DES. if X = subtop then top else X)
  \<Longrightarrow> F2 = (\<lambda>X::'\<Sigma> DES. if X = top then bot else X)
  \<Longrightarrow> F3 = (\<lambda>X::'\<Sigma> DES. X)
  \<Longrightarrow> F4 = (\<lambda>X::'\<Sigma> DES. if X = top then bot else top::'\<Sigma> DES)
  \<Longrightarrow> (mono F1 \<and> subtop < F1 subtop)
  \<and> (\<not> mono F2 \<and> (\<forall>C. F2 C \<le> C))
  \<and> (mono F3 \<and> (\<forall>C. F3 C \<le> C))
  \<and> (\<not> mono F4 \<and> (bot < F4 bot))"
  apply(rule conjI)
   apply(rule orthogonality1)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule orthogonality2)
   apply(force)
  apply(rule conjI)
   apply(simp add: mono_def)
  apply(simp add: mono_def)
  apply(clarsimp)
  apply(simp add: DES_specification_satisfied_def less_DES_ext_def lessDES_def less_eq_DES_ext_def lesseqDES_def des_langUM_def des_langM_def DES_nonblockingness_def nonblockingness_language_def IsDES_def prefix_closure_def prefix_def bot_DES_ext_def botDES_def top_DES_ext_def topDES_def mono_def)
  apply(force)
  done

lemma set_orthogonality1: "
  subtop = (UNIV - {a})
  \<Longrightarrow> F = (\<lambda>X. if X = subtop then top else X)
  \<Longrightarrow> mono F \<and> subtop < F subtop"
  apply(clarsimp)
  apply(simp add: mono_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac y x)(*strict*)
   apply(case_tac "x=a")
    apply(rename_tac y x)(*strict*)
    apply(clarsimp)
   apply(rename_tac y x)(*strict*)
   apply(force)
  apply(force)
  done

lemma non_set_orthogonality2: "
  (UNIV::'a set) = {x}
  \<Longrightarrow> F = (\<lambda>X::'a set. if X = top then bot else X)
  \<Longrightarrow> mono F"
  apply(clarsimp)
  apply(simp only: mono_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(case_tac "x \<in> xa")
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(force)
  done

lemma set_orthogonality2: "
  (x::'a) \<noteq> y
  \<Longrightarrow> F = (\<lambda>X::'a set. if X = top then bot else X)
  \<Longrightarrow> \<not> mono F \<and> (\<forall>C. F C \<le> C)"
  apply(rule conjI)
   apply(simp only: mono_def)
   apply(simp (no_asm))
   apply(clarsimp)
   apply(rule_tac
      x="(UNIV - {x})"
      in exI)
   apply(simp add: mono_def)
   apply(force)
  apply(clarsimp)
  done

corollary set_orthogonality_of_monotonicity_and_decreasing_arguments: "
  subtop = (top - {a})
  \<Longrightarrow> (x::'a) \<noteq> y
  \<Longrightarrow> F1 = (\<lambda>X::'a set. if X = subtop then top else X)
  \<Longrightarrow> F2 = (\<lambda>X::'a set. if X = top then bot else X)
  \<Longrightarrow> F3 = (\<lambda>X::'a set. X)
  \<Longrightarrow> F4 = (\<lambda>X::'a set. if X = top then bot else top::'a set)
  \<Longrightarrow> (mono F1 \<and> subtop < F1 subtop)
  \<and> (\<not> mono F2 \<and> (\<forall>C. F2 C \<le> C))
  \<and> (mono F3 \<and> (\<forall>C. F3 C \<le> C))
  \<and> (\<not> mono F4 \<and> (bot < F4 bot))"
  apply(rule conjI)
   apply(rule set_orthogonality1)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule set_orthogonality2)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: mono_def)
  apply(simp add: mono_def)
  apply(force)
  done

end

