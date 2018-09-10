section {*compute\_greatest\_fixed\_points\_for\_alternative\_fixed\_point\_iterator\_type*}
theory
  compute_greatest_fixed_points_for_alternative_fixed_point_iterator_type

imports
  compute_greatest_fixed_points

begin

lemma Xcomputation_via_Compute_Fixed_Point_Finite_hlp1: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
  \<Longrightarrow> F A \<noteq> A
  \<Longrightarrow> F (F A) \<noteq> F A
  \<Longrightarrow> gfp F < A
  \<Longrightarrow> gfp F < F A"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points)
   apply(force)
  apply(clarsimp)
  apply(erule_tac
      x="A"
      in allE)
  apply(subgoal_tac "F A \<le> A")
   apply(erule impE)
    apply(force)
   apply(erule_tac
      x="gfp F"
      in allE)
   apply(erule impE)
    apply(force)
   apply(subgoal_tac "mono F")
    prefer 2
    apply(simp add: Characteristic_Fixed_Point_Iterator_def mono_def)
   apply(erule impE)
    apply (metis gfp_unfold)
   apply(case_tac "gfp F = F A")
    apply (metis gfp_unfold)
   apply(force)
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

lemma Xcomputation_via_Compute_Fixed_Point_Finite_hlp2: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
  \<Longrightarrow> F A \<noteq> A
  \<Longrightarrow> F (F A) = F A
  \<Longrightarrow> gfp F < A
  \<Longrightarrow> F A = gfp F"
  apply(subgoal_tac "mono F")
   prefer 2
   apply(simp add: Characteristic_Fixed_Point_Iterator_def mono_def)
  apply(rule order_antisym)
   apply (metis gfp_upperbound order_eq_refl)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule Characteristic_Fixed_Point_Iterator_does_not_skip_Fixed_Points)
   apply(force)
  apply(clarsimp)
  apply(erule_tac
      x="A"
      in allE)
  apply(subgoal_tac "F A \<le> A")
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
  apply(simp add: Characteristic_Fixed_Point_Iterator_def)
  done

lemma Xcomputation_via_Compute_Fixed_Point_Finite_hlp: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
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
    apply(simp add: Characteristic_Fixed_Point_Iterator_def mono_def)
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
   apply(rule Xcomputation_via_Compute_Fixed_Point_Finite_hlp1)
      apply(rename_tac n A)(*strict*)
      apply(force)+
  apply(rename_tac n A)(*strict*)
  apply(rule Xcomputation_via_Compute_Fixed_Point_Finite_hlp2)
     apply(rename_tac n A)(*strict*)
     apply(force)+
  done

lemma Xcomputation_via_Compute_Fixed_Point_Finite: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
  \<Longrightarrow> F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top
  \<Longrightarrow> Compute_Fixed_Point_Finite n F top = gfp F"
  apply(subgoal_tac "(F (Compute_Fixed_Point_Finite n F top) = Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top = gfp F) \<and> (F (Compute_Fixed_Point_Finite n F top) \<noteq> Compute_Fixed_Point_Finite n F top \<longrightarrow> Compute_Fixed_Point_Finite n F top > gfp F)")
   apply(force)
  apply(rule Xcomputation_via_Compute_Fixed_Point_Finite_hlp)
  apply(force)
  done

lemma Xcomputation_via_compute: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
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
  apply(rule Xcomputation_via_Compute_Fixed_Point_Finite)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma XCharacteristic_Compute_Fixed_Point_computes_gfp: "
  Characteristic_Fixed_Point_Iterator F (\<lambda>x. True) Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (F, top)
  \<Longrightarrow> Compute_Fixed_Point F top = gfp F"
  apply(rule Xcomputation_via_compute)
   prefer 2
   apply(force)
  apply(simp add: Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator)
  done

theorem XCompute_Fixed_Point_computes_gfp: "
  Fixed_Point_Iterator F UNIV Qterm Qout
  \<Longrightarrow> Compute_Fixed_Point_dom (F, top)
  \<Longrightarrow> Compute_Fixed_Point F top = gfp F"
  apply(rule_tac
      Qterm="\<lambda>x. x\<in> Qterm"
      and Qout="\<lambda>x. x\<in> Qout"
      in XCharacteristic_Compute_Fixed_Point_computes_gfp)
   prefer 2
   apply(force)
  apply(rule_tac
      P="\<lambda>X. X"
      in Characteristic_Fixed_Point_Iterator_equals_Fixed_Point_Iterator1_proof)
  apply(force)
  done

corollary Compute_Fixed_Point_computes_gfp_can_not_have_Qinp: "
  (\<forall>x. S = F S \<longrightarrow> x \<le> F (inf x S) \<longrightarrow> x \<le> S)
  \<longleftrightarrow> (S = F S \<longrightarrow> gfp (\<lambda>X. F (inf X S)) \<le> S)"
  apply(rule antisym)
   apply(simp add: gfp_def)
   apply(clarsimp)
   apply(rule Sup_least)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      b="gfp (\<lambda>X. F (inf X S))"
      in order.trans)
   apply(rename_tac x)(*strict*)
   apply(simp add: gfp_def)
   apply(rule Sup_upper)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

end
