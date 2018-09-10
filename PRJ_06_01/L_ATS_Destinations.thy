section {*L\_ATS\_Destinations*}
theory
  L_ATS_Destinations

imports
  L_ATS

begin

locale ATS_Destinations =
  ATS
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  for
    TSstructure configurations initial_configurations step_labels step_relation
    +

fixes destinations :: "'TSstructure \<Rightarrow> 'destination set"
fixes get_destinations :: "'TSstructure \<Rightarrow> ('label,'conf)derivation_configuration \<Rightarrow> 'destination set"

context ATS_Destinations
begin

definition get_accessible_destinations :: "
  'TSstructure
  \<Rightarrow> 'destination set"
  where
    "get_accessible_destinations G \<equiv>
  {x\<in> destinations G.
  \<exists>d i e c.
    derivation_initial G d
    \<and> d i = Some (pair e c)
    \<and> x\<in> get_destinations G (pair e c)}"

definition accessible :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "accessible G \<equiv>
  destinations G \<subseteq> get_accessible_destinations G"

end

end
