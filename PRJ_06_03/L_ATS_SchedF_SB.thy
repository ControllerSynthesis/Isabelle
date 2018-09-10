section {*L\_ATS\_SchedF\_SB*}
theory
  L_ATS_SchedF_SB

imports
  L_ATS_SchedF_Basic

begin

locale ATS_SchedF_SB =
  ATS_SchedF_Basic
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event set"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable
    +
  fixes get_fixed_scheduler :: "'conf \<Rightarrow> 'fixed_scheduler"

assumes AX_fixed_scheduler_extendable_translates_backwards: "
  TSstructure G
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c2)
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c1)"

context ATS_SchedF_SB begin

lemma fixed_scheduler_extendable_translates_backwards_lift: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> d i = Some (pair e1 c1)
  \<Longrightarrow> d j = Some (pair e2 c2)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c2)
  \<Longrightarrow> fixed_scheduler_extendable G (get_fixed_scheduler c1)"
  apply(induct "j-i" arbitrary: i e1 c1)
   apply(rename_tac i e1 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e1 c1)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac x i e1 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="j"
      in step_detail_before_some_position)
     apply(rename_tac x i e1 c1)(*strict*)
     apply(force)
    apply(rename_tac x i e1 c1)(*strict*)
    apply(force)
   apply(rename_tac x i e1 c1)(*strict*)
   apply(force)
  apply(rename_tac x i e1 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
  apply(erule_tac
      x="Some e2a"
      in meta_allE)
  apply(erule_tac
      x="c2a"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
   apply(force)
  apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
   apply (metis AX_step_relation_preserves_belongs)
  apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
   apply(force)
  apply(rename_tac x i e1 c1 e2a c2a)(*strict*)
  apply (metis AX_fixed_scheduler_extendable_translates_backwards)
  done

definition Nonblockingness_branching_restricted :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_branching_restricted G \<equiv>
  \<forall>dh n.
  derivation_initial G dh
  \<and> maximum_of_domain dh n
  \<and> fixed_scheduler_extendable G (get_fixed_scheduler (the (get_configuration (dh n))))
  \<longrightarrow> (\<exists>dc n'.
  derivation G dc
  \<and> belongs G dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh dc n
  \<and> marking_condition G (derivation_append dh dc n))"

lemma schedF_nonextendable_translates_backwards_lift: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> \<not> fixed_scheduler_extendable G (get_fixed_scheduler cx)
  \<Longrightarrow> d x = Some (pair ex cx)
  \<Longrightarrow> d y = Some (pair ey cy)
  \<Longrightarrow> x\<le>y
  \<Longrightarrow> \<not> fixed_scheduler_extendable G (get_fixed_scheduler cy)"
  apply(induct "y-x" arbitrary: x ex cx)
   apply(rename_tac x ex cx)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa x ex cx)(*strict*)
  apply(erule_tac
      x="Suc x"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac xa x ex cx)(*strict*)
   prefer 2
   apply(rule_tac
      m="y"
      in step_detail_before_some_position)
     apply(rename_tac xa x ex cx)(*strict*)
     apply(force)
    apply(rename_tac xa x ex cx)(*strict*)
    apply(force)
   apply(rename_tac xa x ex cx)(*strict*)
   apply(force)
  apply(rename_tac xa x ex cx)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x ex cx e2 c2)(*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x ex cx e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x ex cx e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x ex cx e2 c2)(*strict*)
   prefer 2
   apply(erule meta_impE)
    apply(rename_tac xa x ex cx e2 c2)(*strict*)
    apply(force)
   apply(rename_tac xa x ex cx e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x ex cx e2 c2)(*strict*)
  apply (metis belongs_configurations AX_fixed_scheduler_extendable_translates_backwards)
  done

theorem Nonblockingness_branching_implies_Nonblockingness_branching_restricted: "
  TSstructure G
  \<Longrightarrow> Nonblockingness_branching G
  \<Longrightarrow> Nonblockingness_branching_restricted G"
  apply(simp add: Nonblockingness_branching_def Nonblockingness_branching_restricted_def)
  done

end

end
