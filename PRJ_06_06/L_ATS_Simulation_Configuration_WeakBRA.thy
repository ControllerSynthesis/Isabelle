section {*L\_ATS\_Simulation\_Configuration\_WeakBRA*}
theory
  L_ATS_Simulation_Configuration_WeakBRA

imports
  L_ATS_Simulation_Configuration_WeakDET

begin

locale ATS_Simulation_Configuration_WeakBRA =
  ATS_Simulation_Configuration_WeakDET
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
  "relation_configurationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_initial_configurationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_effectLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"
  "relation_TSstructureLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"
  "relation_initial_simulationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_configurationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "relation_initial_configurationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "relation_effectRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'event2 \<Rightarrow> 'event1 \<Rightarrow> bool"
  "relation_TSstructureRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> bool"
  "relation_initial_simulationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> bool"
  "label_relation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 relation_configurationLR relation_initial_configurationLR relation_effectLR relation_TSstructureLR relation_initial_simulationLR relation_step_simulationLR relation_configurationRL relation_initial_configurationRL relation_effectRL relation_TSstructureRL relation_initial_simulationRL relation_step_simulationRL label_relation
    +

assumes AX_relation_configuration_inverse: "
  relation_TSstructureLR G1 G2
  \<Longrightarrow> relation_configurationRL G2 G1 c2 c1
  \<Longrightarrow> relation_configurationLR G1 G2 c1 c2"

assumes AX_marking_condition_translation: "
  relation_TSstructureRL G2 G1
  \<Longrightarrow> relation_TSstructureLR G1 G2
  \<Longrightarrow> LR.GR.derivation_initial G2 dR
  \<Longrightarrow> maximum_of_domain dR nR
  \<Longrightarrow> dR nR = Some (pair enR cnR)
  \<Longrightarrow> LR.GL.derivation_initial G1 dL
  \<Longrightarrow> maximum_of_domain dL nL
  \<Longrightarrow> relation_initial_configurationRL G2 G1 c0R c0L
  \<Longrightarrow> relation_configurationRL G2 G1 cnR cnL
  \<Longrightarrow> dR 0 = Some (pair None c0R)
  \<Longrightarrow> dL 0 = Some (pair None c0L)
  \<Longrightarrow> dL nL = Some (pair enL cnL)
  \<Longrightarrow> LR.GL.derivation G1 dL2
  \<Longrightarrow> LR.GL.belongs G1 dL2
  \<Longrightarrow> maximum_of_domain dL2 nL2
  \<Longrightarrow> marking_condition1 G1 (derivation_append dL dL2 nL)
  \<Longrightarrow> dL2 0 = Some (pair None cnL)
  \<Longrightarrow> relation_configurationLR G1 G2 cnL cnR
  \<Longrightarrow> dL2 nL2 = Some (pair e2nL c2nL)
  \<Longrightarrow> LR.GR.derivation G2 d2R
  \<Longrightarrow> LR.GR.belongs G2 d2R
  \<Longrightarrow> maximum_of_domain d2R n2R
  \<Longrightarrow> relation_configurationLR G1 G2 c2nL cn2R
  \<Longrightarrow> d2R 0 = Some (pair None cnR)
  \<Longrightarrow> d2R n2R = Some (pair en2R cn2R)
  \<Longrightarrow> marking_condition2 G2 (derivation_append dR d2R nR)"

context ATS_Simulation_Configuration_WeakBRA begin

theorem Nonblockingness_branching_is_preserved: "
  relation_TSstructureRL G2 G1
  \<Longrightarrow> relation_TSstructureLR G1 G2
  \<Longrightarrow> LR.GL.Nonblockingness_branching G1
  \<Longrightarrow> LR.GR.Nonblockingness_branching G2"
  apply(simp add: LR.GR.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(rename_tac dR nR)
  apply(rename_tac dR nR)(*strict*)
  apply(subgoal_tac "\<exists>enR cnR. dR nR = Some (pair enR cnR)")
  apply(rename_tac dR nR)(*strict*)
  prefer 2
  apply(rule LR.GR.some_position_has_details_before_max_dom)
  apply(rename_tac dR nR)(*strict*)
  apply(rule LR.GR.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac dR nR)(*strict*)
  apply(force)
  apply(rename_tac dR nR)(*strict*)
  apply(force)
  apply(rename_tac dR nR)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2. LR.GL.derivation_initial G1 d2 \<and> maximum_of_domain d2 n2 \<and> relation_initial_configurationRL G2 G1 (the (get_configuration (dR 0))) (the (get_configuration (d2 0))) \<and> relation_configurationRL G2 G1 cnR (the (get_configuration (d2 n2)))")
  apply(rename_tac dR nR enR cnR)(*strict*)
  prefer 2
  apply(rule RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
  apply(rename_tac dR nR enR cnR)(*strict*)
  apply(force)
  apply(rename_tac dR nR enR cnR)(*strict*)
  apply(force)
  apply(rename_tac dR nR enR cnR)(*strict*)
  apply(force)
  apply(rename_tac dR nR enR cnR)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR d2 n2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>c. dR 0 = Some (pair None c)")
  apply(rename_tac dR nR enR cnR d2 n2)(*strict*)
   prefer 2
   apply (metis LR.GR.derivation_initial_is_derivation LR.GR.some_position_has_details_at_0)
  apply(rename_tac dR nR enR cnR d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac dR nR enR cnR d2 n2)(*strict*)
   prefer 2
   apply (metis LR.GL.derivation_initial_is_derivation LR.GL.some_position_has_details_at_0)
  apply(rename_tac dR nR enR cnR d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
   prefer 2
   apply(rule LR.GL.some_position_has_details_before_max_dom)
     apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
     apply(rule LR.GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
    apply(force)
   apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
   apply(force)
  apply(rename_tac dR nR enR cnR d2 n2 c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR d2 n2 c ca e cb)(*strict*)
  apply(rename_tac dL nL c0R c0L enL cnL)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL)(*strict*)
  apply(simp add: LR.GL.Nonblockingness_branching_def)
  apply(erule_tac
      x="dL"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="nL"
      in allE)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dc x)(*strict*)
  apply(rename_tac dL2 nL2)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2)(*strict*)
  apply(subgoal_tac "\<exists>c. dL2 0 =Some (pair None c)")
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2)(*strict*)
   prefer 2
   apply (metis LR.GL.some_position_has_details_at_0)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
  apply(subgoal_tac "relation_configurationLR G1 G2 cnL cnR")
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
   prefer 2
   apply(rule AX_relation_configuration_inverse)
    apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
    apply(force)
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
   apply(force)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
  apply(subgoal_tac "\<exists>e c. dL2 nL2= Some (pair e c)")
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
   prefer 2
   apply(rule LR.GL.some_position_has_details_before_max_dom)
     apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
     apply(force)
    apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
    apply(force)
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
   apply(force)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2. LR.GR.derivation G2 d2 \<and> LR.GR.belongs G2 d2 \<and> maximum_of_domain d2 n2 \<and> the (get_configuration (d2 0)) = cnR \<and> relation_configurationLR G1 G2 (the (get_configuration (dL2 0))) (the (get_configuration (d2 0))) \<and> relation_configurationLR G1 G2 ca (the (get_configuration (d2 n2)))")
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
   prefer 2
   apply(rule LR.ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness2)
         apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
         apply(force)
        apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
        apply(force)
       apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
       apply(force)
      apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
      apply(simp add: derivation_append_fit_def)
     apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
     apply(simp add: derivation_append_fit_def)
    apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply (metis LR.GR.belongs_configurations LR.GR.derivation_initial_belongs LR.AX_TSstructure_relation_TSstructure2_belongs)
   apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac dR nR enR cnR dL nL c0R c0L enL cnL dL2 nL2 c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
   apply(force)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
   prefer 2
   apply (metis LR.GR.some_position_has_details_at_0)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
   prefer 2
   apply(rule LR.GR.some_position_has_details_before_max_dom)
     apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
     apply(force)
    apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
    apply(force)
   apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
   apply(force)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2 cb ea cc)(*strict*)
  apply(rule conjI)
   apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2 cb ea cc)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac dR nR enR dL nL c0R c0L enL cnL dL2 nL2 c e ca d2 n2 cb ea cc)(*strict*)
  apply(simp add: derivation_append_fit_def)
  apply(clarsimp)
  apply(rename_tac dR nR enR dL nL c0R c0L enL dL2 nL2 c e ca d2 n2 cb ea cc)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac cnL e2nL c2nL d2R n2R cnR en2R cn2R)
  apply(rename_tac dR nR enR dL nL c0R c0L enL dL2 nL2 cnL e2nL c2nL d2R n2R cnR en2R cn2R)(*strict*)
  apply(rule AX_marking_condition_translation)
                      apply(rename_tac dR nR enR dL nL c0R c0L enL dL2 nL2 cnL e2nL c2nL d2R n2R cnR en2R cn2R)(*strict*)
                      apply(force)+
  done

end

end
