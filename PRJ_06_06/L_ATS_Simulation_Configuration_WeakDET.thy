section {*L\_ATS\_Simulation\_Configuration\_WeakDET*}
theory
  L_ATS_Simulation_Configuration_WeakDET

imports
  L_ATS_Simulation_Configuration_Weak

begin

locale ATS_Simulation_Configuration_WeakDET =
  LR :
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
  "relation_configurationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_initial_configurationLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_effectLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"
  "relation_TSstructureLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"
  "relation_initial_simulationLRLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulationLRLR :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  +
  RL :
  ATS_Simulation_Configuration_Weak
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "relation_configurationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "relation_initial_configurationRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "relation_effectRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'event2 \<Rightarrow> 'event1 \<Rightarrow> bool"
  "relation_TSstructureRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> bool"
  "relation_initial_simulationLRRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulationLRRL :: 'TSstructure2 \<Rightarrow> 'TSstructure1 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 relation_configurationLR relation_initial_configurationLR relation_effectLR relation_TSstructureLR relation_initial_simulationLRLR relation_step_simulationLRLR relation_configurationRL relation_initial_configurationRL relation_effectRL relation_TSstructureRL relation_initial_simulationLRRL relation_step_simulationLRRL
    +

fixes label_relation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"

assumes AX_backwards_determinism: "
  relation_TSstructureRL G2 G1
  \<Longrightarrow> LR.GL.is_forward_edge_deterministic_accessible G1
  \<Longrightarrow> step_relation2 G2 cnR en1 cnR1
  \<Longrightarrow> step_relation2 G2 cnR en2 cnR2
  \<Longrightarrow> maximum_of_domain dR nR
  \<Longrightarrow> LR.GR.derivation_initial G2 dR
  \<Longrightarrow> dR nR = Some (pair enR cnR)
  \<Longrightarrow> LR.GL.derivation_initial G1 dL
  \<Longrightarrow> maximum_of_domain dL nL
  \<Longrightarrow> relation_initial_configurationRL G2 G1 c0R c0L
  \<Longrightarrow> relation_configurationRL G2 G1 cnR cnL
  \<Longrightarrow> dR 0 = Some (pair None c0R)
  \<Longrightarrow> dL 0 = Some (pair None c0L)
  \<Longrightarrow> dL nL = Some (pair enL cnL)
  \<Longrightarrow> LR.GL.derivation G1 dL1
  \<Longrightarrow> LR.GL.derivation G1 dL2
  \<Longrightarrow> LR.GL.belongs G1 dL1
  \<Longrightarrow> LR.GL.belongs G1 dL2
  \<Longrightarrow> relation_step_simulationLRRL G2 G1 cnR en1 cnR1 cnL dL1
  \<Longrightarrow> relation_step_simulationLRRL G2 G1 cnR en2 cnR2 cnL dL2
  \<Longrightarrow> maximum_of_domain dL1 nL1
  \<Longrightarrow> relation_configurationRL G2 G1 cnR1 cnL1
  \<Longrightarrow> maximum_of_domain dL2 nL2
  \<Longrightarrow> relation_configurationRL G2 G1 cnR2 cnL2
  \<Longrightarrow> dL1 0 = Some (pair None cnL)
  \<Longrightarrow> dL2 0 = Some (pair None cnL)
  \<Longrightarrow> dL1 nL1 = Some (pair enL1 cnL1)
  \<Longrightarrow> dL2 nL2 = Some (pair enL2 cnL2)
  \<Longrightarrow> en1 = en2"

context ATS_Simulation_Configuration_WeakDET begin

theorem is_forward_edge_deterministic_accessible_is_preserved: "
  relation_TSstructureRL G2 G1
  \<Longrightarrow> LR.GL.is_forward_edge_deterministic_accessible G1
  \<Longrightarrow> LR.GR.is_forward_edge_deterministic_accessible G2"
  apply(simp add: LR.GR.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: LR.GR.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
  apply(subgoal_tac "\<exists>dR nR. maximum_of_domain dR nR \<and> ATS.derivation_initial initial_configurations2 step_relation2 G2 dR \<and> dR nR = Some (pair enR cnR)")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d i"
      in exI)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule conjI)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
   apply(rule conjI)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
    apply(rule LR.GR.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 d i enR dR nR)(*strict*)
  apply(thin_tac "ATS.derivation_initial initial_configurations2 step_relation2 G2 d")
  apply(thin_tac "d i = Some (pair enR cnR)")
  apply(clarsimp)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
  apply(subgoal_tac "\<exists>d2 n2. LR.GL.derivation_initial G1 d2 \<and> maximum_of_domain d2 n2 \<and> relation_initial_configurationRL G2 G1 (the (get_configuration (dR 0))) (the (get_configuration (d2 0))) \<and> relation_configurationRL G2 G1 cnR (the (get_configuration (d2 n2)))")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
   prefer 2
   apply(rule RL.ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
     apply(force)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
    apply(force)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
   apply(force)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>c. dR 0 = Some (pair None c)")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2)(*strict*)
   prefer 2
   apply (metis LR.GR.derivation_initial_is_derivation LR.GR.some_position_has_details_at_0)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2)(*strict*)
   prefer 2
   apply (metis LR.GL.derivation_initial_is_derivation LR.GL.some_position_has_details_at_0)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
   prefer 2
   apply(rule LR.GL.some_position_has_details_before_max_dom)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
     apply(rule LR.GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
    apply(force)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
   apply(force)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR d2 n2 c ca e cb)(*strict*)
  apply(rename_tac dL nL c0R c0L enL cnL)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
  apply(subgoal_tac "\<exists>d2 n. LR.GL.derivation G1 d2 \<and> LR.GL.belongs G1 d2 \<and> the(get_configuration(d2 0)) = cnL \<and> relation_step_simulationLRRL G2 G1 cnR en1 cnR1 cnL d2 \<and> maximum_of_domain d2 n \<and> relation_configurationRL G2 G1 cnR1 (the(get_configuration(d2 n)))")
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
   apply(subgoal_tac "\<exists>d2 n. LR.GL.derivation G1 d2 \<and> LR.GL.belongs G1 d2 \<and> the(get_configuration(d2 0)) = cnL \<and> relation_step_simulationLRRL G2 G1 cnR en2 cnR2 cnL d2 \<and> maximum_of_domain d2 n \<and> relation_configurationRL G2 G1 cnR2 (the(get_configuration(d2 n)))")
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na)(*strict*)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na)(*strict*)
     prefer 2
     apply (metis LR.GL.some_position_has_details_at_0)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>c. d2a 0 = Some (pair None c)")
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na)(*strict*)
     prefer 2
     apply (metis LR.GL.some_position_has_details_at_0)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
    apply(subgoal_tac "\<exists>e c. d2 n = Some (pair e c)")
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
     prefer 2
     apply(rule LR.GL.some_position_has_details_before_max_dom)
       apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
       apply(force)
      apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
      apply(force)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
     apply(force)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
    apply(subgoal_tac "\<exists>e c. d2a na = Some (pair e c)")
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
     prefer 2
     apply(rule LR.GL.some_position_has_details_before_max_dom)
       apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
       apply(force)
      apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
      apply(force)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
     apply(force)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL d2 d2a n na c e ea ca cb)(*strict*)
    apply(rename_tac dL1 dL2 nL1 nL2 cnL enL1 enL2 cnL1 cnL2)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL dL1 dL2 nL1 nL2 cnL enL1 enL2 cnL1 cnL2)(*strict*)
    prefer 2
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
    apply(rule RL.AX_relation_step_simulation)
       apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
       apply(force)
      apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
      apply(force)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
     apply (metis LR.GR.belongs_configurations LR.GR.derivation_initial_belongs LR.GR.AX_step_relation_preserves_belongsE RL.AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
    apply(force)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL dL1 dL2 nL1 nL2 cnL enL1 enL2 cnL1 cnL2)(*strict*)
   prefer 2
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
   apply(rule RL.AX_relation_step_simulation)
      apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
      apply(force)
     apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
     apply(force)
    apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
    apply (metis LR.GR.belongs_configurations LR.GR.derivation_initial_belongs LR.GR.AX_step_relation_preserves_belongsE RL.AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL cnL)(*strict*)
   apply(force)
  apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL dL1 dL2 nL1 nL2 cnL enL1 enL2 cnL1 cnL2)(*strict*)
  apply(rule_tac
      ?G1.0="G1"
      and dR="dR"
      and ?dL1.0="dL1"
      and ?dL2.0="dL2"
      in AX_backwards_determinism)
                      apply(rename_tac cnR cnR1 cnR2 en1 en2 enR dR nR dL nL c0R c0L enL dL1 dL2 nL1 nL2 cnL enL1 enL2 cnL1 cnL2)(*strict*)
                      apply(force)+
  done

end

end
