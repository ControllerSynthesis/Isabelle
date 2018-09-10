section {*L\_BF\_Bra\_LaOp*}
theory
  L_BF_Bra_LaOp

imports
  PRJ_06_05__PRE

begin

locale BF_Bra_LaOp =
  ATS_List_Based_Effects
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect
    +

assumes AX_BF_Bra_LaOp: "
  TSstructure M
  \<Longrightarrow> nonblockingness_language (unmarked_language M) (marked_language M)
  \<Longrightarrow> Nonblockingness_branching M"

end
