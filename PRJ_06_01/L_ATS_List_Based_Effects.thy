section {*L\_ATS\_List\_Based\_Effects*}
theory
  L_ATS_List_Based_Effects

imports
  L_ATS_Language

begin

locale ATS_List_Based_Effects =
  ATS_Language
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event list set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect

context ATS_List_Based_Effects
begin

definition observation_neutral :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "observation_neutral G d \<equiv>
  unmarked_effect G d = unmarked_effect G (derivation_take d 0)"

end

end
