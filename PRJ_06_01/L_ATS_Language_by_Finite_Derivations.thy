section {*L\_ATS\_Language\_by\_Finite\_Derivations*}
theory
  L_ATS_Language_by_Finite_Derivations

imports
  L_ATS_Language

begin

locale ATS_Language_by_Finite_Derivations =
  ATS_Language
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect
    +

assumes AX_marked_language_finite: "
  TSstructure G
  \<Longrightarrow> finite_marked_language G=marked_language G"

assumes AX_unmarked_language_finite: "
  TSstructure G
  \<Longrightarrow> finite_unmarked_language G=unmarked_language G"

end
