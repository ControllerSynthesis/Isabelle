section {*L\_ATS\_Simulation\_Configuration\_WeakLRB*}
theory
  L_ATS_Simulation_Configuration_WeakLRB

imports
  L_ATS_Simulation_Configuration_Weak

begin

locale ATS_Simulation_Configuration_WeakLRB =
  ATS_Simulation_Configuration_Weak
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "relation_configuration :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_initial_configuration :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_effect :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"
  "relation_TSstructure :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 relation_configuration relation_initial_configuration relation_effect relation_TSstructure
    +

fixes AX_relation_initial_simulationB :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"

fixes AX_relation_step_simulationB :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"

assumes AX_relation_initial_simulationB: "
  relation_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> \<exists>d2 n.
  GR.derivation_initial G2 d2
  \<and> relation_initial_configuration G1 G2 c1 (the(get_configuration(d2 0)))
  \<and> AX_relation_initial_simulationB G1 G2 c1 c2 d2
  \<and> maximum_of_domain d2 n
  \<and> get_configuration (d2 n) = Some c2"

assumes AX_relation_step_simulationB: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> c1' \<in> configurations1 G1
  \<Longrightarrow> step_relation1 G1 c1' e1 c1
  \<Longrightarrow> \<exists>d2 n.
  GR.derivation G2 d2
  \<and> GR.belongs G2 d2
  \<and> the(get_configuration(d2 n)) = c2
  \<and> AX_relation_step_simulationB G1 G2 c1' e1 c1 c2 d2
  \<and> maximum_of_domain d2 n
  \<and> relation_configuration G1 G2 c1' (the(get_configuration(d2 0)))"

assumes AX_initial_contained: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_initial_configuration G1 G2 c1 c2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2"

context ATS_Simulation_Configuration_WeakLRB begin

lemma ATS_Simulation_Configuration_WeakLRB_simulation_derivation_exists: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation G1 d1
  \<Longrightarrow> GL.belongs G1 d1
  \<Longrightarrow> d1 x = Some (pair e1x c1x)
  \<Longrightarrow> d1 y = Some (pair e1y c1y)
  \<Longrightarrow> x\<le>y
  \<Longrightarrow> relation_configuration G1 G2 c1y c2y
  \<Longrightarrow> \<exists>d2 n2.
  GR.derivation G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_configuration G1 G2 c1x (the (get_configuration (d2 0)))
  \<and> c2y = (the (get_configuration (d2 n2)))
  \<and> (c1x \<in> initial_configurations1 G1 \<longrightarrow> (the (get_configuration (d2 0))) \<in> initial_configurations2 G2)"
  apply(induct "y-x" arbitrary: x e1x c1x)
   apply(rename_tac x e1x c1x)(*strict*)
   apply(clarsimp)
   apply(case_tac "c1y \<in> initial_configurations1 G1")
    apply(subgoal_tac "\<exists>d2 n. GR.derivation_initial G2 d2 \<and> relation_initial_configuration G1 G2 c1y (the(get_configuration(d2 0))) \<and> AX_relation_initial_simulationB G1 G2 c1y c2y d2 \<and> maximum_of_domain d2 n \<and> get_configuration (d2 n) = Some c2y")
     prefer 2
     apply(rule AX_relation_initial_simulationB)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rename_tac d2 n)(*strict*)
    apply(rule_tac
      x="d2"
      in exI)
    apply(rule conjI)
     apply(rename_tac d2 n)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d2 n)(*strict*)
    apply(rule_tac
      x="n"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
     apply(rename_tac d2 n)(*strict*)
     apply(clarsimp)
     apply(rename_tac d2 n c)(*strict*)
     apply(subgoal_tac "\<exists>e c. d2 n = Some (pair e c)")
      apply(rename_tac d2 n c)(*strict*)
      apply(clarsimp)
      apply(rename_tac d2 n c e ca)(*strict*)
      apply(simp add: get_configuration_def GR.derivation_initial_def)
      apply (metis AX_initial_contained)
     apply(rename_tac d2 n c)(*strict*)
     apply(simp add: get_configuration_def)
     apply(case_tac "d2 n")
      apply(rename_tac d2 n c)(*strict*)
      apply(clarsimp)
     apply(rename_tac d2 n c a)(*strict*)
     apply(case_tac a)
     apply(rename_tac d2 n c a option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac d2 n)(*strict*)
    apply (metis GR.derivation_initial_is_derivation GR.some_position_has_details_at_0)
   apply(rule_tac
      x="der1 c2y"
      in exI)
   apply(rule conjI)
    apply(rule GR.der1_is_derivation)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rule der1_maximum_of_domain)
   apply(simp add: der1_def get_configuration_def)
  apply(rename_tac xa x e1x c1x)(*strict*)
  apply(clarsimp)
  apply(case_tac y)
   apply(rename_tac xa x e1x c1x)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y)
  apply(rename_tac xa x e1x c1x y)(*strict*)
  apply(erule_tac
      x="Suc x"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 x = Some (pair e1 c1) \<and> d1 (Suc x) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac xa x e1x c1x y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc y"
      in GL.step_detail_before_some_position)
     apply(rename_tac xa x e1x c1x y)(*strict*)
     apply(force)
    apply(rename_tac xa x e1x c1x y)(*strict*)
    apply(force)
   apply(rename_tac xa x e1x c1x y)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2)(*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x e1x c1x y e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x e1x c1x y e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>d2' n. GR.derivation G2 d2' \<and> GR.belongs G2 d2' \<and> the(get_configuration(d2' n)) = the(get_configuration(d2 0)) \<and> AX_relation_step_simulationB G1 G2 c1x e2 c2 (the(get_configuration(d2 0))) d2' \<and> maximum_of_domain d2' n \<and> relation_configuration G1 G2 c1x (the(get_configuration(d2' 0)))")
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
   prefer 2
   apply(rule AX_relation_step_simulationB)
       apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
       apply(force)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
      apply(force)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
     apply(rule GL.AX_step_relation_preserves_belongsE)
       apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
       apply (metis AX_TSstructure_relation_TSstructure1_belongs)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
      apply(force)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
     apply (metis GL.belongs_configurations)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
    apply (metis GL.belongs_configurations)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
  apply(case_tac "c1x \<in> initial_configurations1 G1")
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_append d2' d2 n"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
      apply(force)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply(simp add: maximum_of_domain_def)
    apply(clarsimp)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya yb)(*strict*)
    apply(case_tac yb)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya yb option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya option b)(*strict*)
    apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya option b c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n ya option b)(*strict*)
    apply (metis GR.some_position_has_details_at_0)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   apply(rule_tac
      x="n+n2"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply (metis concat_has_max_dom)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply (simp add: get_configuration_def derivation_append_def)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply (simp add: get_configuration_def derivation_append_def)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
  apply(subgoal_tac "\<exists>d2 n. GR.derivation_initial G2 d2 \<and> relation_initial_configuration G1 G2 c1x (the(get_configuration(d2 0))) \<and> AX_relation_initial_simulationB G1 G2 c1x (the (get_configuration (d2' 0))) d2 \<and> maximum_of_domain d2 n \<and> get_configuration (d2 n) = Some (the (get_configuration (d2' 0)))")
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   prefer 2
   apply(rule AX_relation_initial_simulationB)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
    apply(force)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply(rule_tac
      x="derivation_append d2a (derivation_append d2' d2 n) na"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
      apply(force)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(subgoal_tac "\<exists>e c. d2' n = Some (pair e c)")
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
     apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c ca)(*strict*)
      apply(simp add: get_configuration_def GR.derivation_initial_def)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
     apply (metis GR.some_position_has_details_at_0)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(rule GR.some_position_has_details_before_max_dom)
      apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
      apply(force)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(force)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2a na = Some (pair e c)")
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
    apply(simp add: derivation_append_def)
    apply(subgoal_tac "\<exists>c. d2' 0 = Some (pair None c)")
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c ca)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na e c)(*strict*)
    apply (metis GR.some_position_has_details_at_0)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply(rule GR.some_position_has_details_before_max_dom)
     apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
    apply(force)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply(force)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply(rule_tac
      x="na+(n+n2)"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply (metis concat_has_max_dom)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply (simp add: get_configuration_def derivation_append_def)
   apply (metis get_configuration_def AX_initial_contained)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply (simp add: get_configuration_def derivation_append_def)
   apply(clarsimp)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply(subgoal_tac "\<exists>c. d2a 0 = Some (pair None c)")
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na c)(*strict*)
   apply (simp add: get_configuration_def derivation_append_def GR.derivation_initial_def)
  apply(rename_tac xa x e1x c1x y e2 c2 d2 n2 d2' n d2a na)(*strict*)
  apply (metis GR.derivation_initial_is_derivation GR.some_position_has_details_at_0)
  done

lemma ATS_Simulation_Configuration_WeakLRB_simulation_initial_derivation_exists: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 x = Some (pair e1 c1)
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> \<exists>d2 n2.
  GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> c2 = (the (get_configuration (d2 n2)))"
  apply(subgoal_tac "\<exists>c. d1 0 = Some (pair None c)")
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "\<exists>d2 n2. GR.derivation G2 d2 \<and> maximum_of_domain d2 n2 \<and> relation_configuration G1 G2 c (the (get_configuration (d2 0))) \<and> c2 = (the (get_configuration (d2 n2))) \<and> (c \<in> initial_configurations1 G1 \<longrightarrow> (the (get_configuration (d2 0))) \<in> initial_configurations2 G2)")
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      in ATS_Simulation_Configuration_WeakLRB_simulation_derivation_exists)
          apply(rename_tac c)(*strict*)
          apply(force)
         apply(rename_tac c)(*strict*)
         apply(rule GL.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac c)(*strict*)
        apply(rule GL.derivation_initial_belongs)
         apply(rename_tac c)(*strict*)
         apply (metis AX_TSstructure_relation_TSstructure1_belongs)
        apply(rename_tac c)(*strict*)
        apply(force)
       apply(rename_tac c)(*strict*)
       apply(force)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d2 n2)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac c d2 n2)(*strict*)
    apply(rule_tac
      x="d2"
      in exI)
    apply(rule conjI)
     apply(rename_tac c d2 n2)(*strict*)
     apply(simp add: GR.derivation_initial_def)
     apply(clarsimp)
     apply(rename_tac c d2 n2 ca)(*strict*)
     apply (simp add: get_configuration_def)
     apply(erule impE)
      apply(rename_tac c d2 n2 ca)(*strict*)
      apply(simp add: GL.derivation_initial_def)
     apply(rename_tac c d2 n2 ca)(*strict*)
     apply(force)
    apply(rename_tac c d2 n2)(*strict*)
    apply(rule_tac
      x="n2"
      in exI)
    apply(clarsimp)
   apply(rename_tac c d2 n2)(*strict*)
   apply (metis GR.some_position_has_details_at_0)
  apply (metis GL.derivation_initial_is_derivation GL.some_position_has_details_at_0)
  done

theorem ATS_Simulation_Configuration_WeakLRB_get_accessible_configurations_transfer: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c1 \<in> GL.get_accessible_configurations G1
  \<Longrightarrow> c2 \<in> GR.get_accessible_configurations G2"
  apply(simp add: GL.get_accessible_configurations_def GR.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>d2 n2. GR.derivation_initial G2 d2 \<and> maximum_of_domain d2 n2 \<and> c2 = (the (get_configuration (d2 n2)))")
   apply(rename_tac d i option b)(*strict*)
   prefer 2
   apply(rule ATS_Simulation_Configuration_WeakLRB_simulation_initial_derivation_exists)
      apply(rename_tac d i option b)(*strict*)
      apply(force)
     apply(rename_tac d i option b)(*strict*)
     apply(force)
    apply(rename_tac d i option b)(*strict*)
    apply(force)
   apply(rename_tac d i option b)(*strict*)
   apply(force)
  apply(rename_tac d i option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option d2 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n2"
      in exI)
  apply(simp add: get_configuration_def)
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac d i option d2 n2 y)(*strict*)
  apply(case_tac y)
  apply(rename_tac d i option d2 n2 y optiona conf)(*strict*)
  apply(clarsimp)
  done

end

end
