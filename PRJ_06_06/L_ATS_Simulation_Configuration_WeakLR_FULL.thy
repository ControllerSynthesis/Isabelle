section {*L\_ATS\_Simulation\_Configuration\_WeakLR\_FULL*}
theory
  L_ATS_Simulation_Configuration_WeakLR_FULL

imports
  L_ATS_Simulation_Configuration_WeakLR_Unmarked_Effect
  L_ATS_Simulation_Configuration_WeakLR_Marked_Effect

begin

locale ATS_Simulation_Configuration_WeakLR_FULL =
  ATS_Simulation_Configuration_Weak_Unmarked_Effect
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
  "relation_initial_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  +
  ATS_Simulation_Configuration_Weak_Marked_Effect
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
  "relation_initial_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 relation_configuration relation_initial_configuration relation_effect relation_TSstructure relation_initial_simulation relation_step_simulation

end
