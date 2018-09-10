section {*LR1\_Property\_Satisfaction\_\_output\_not\_produced\_by*}
theory
  LR1_Property_Satisfaction__output_not_produced_by

imports
  PRJ_12_04_06_06_08__ENTRY

begin

definition lastProducesX :: "  
  (('a, 'd) cfg_step_label, ('a, 'd) cfg_configuration) derivation
  \<Rightarrow> ('a, 'd) cfg_step_label list
  \<Rightarrow> 'd list
  \<Rightarrow> bool"
  where
    "lastProducesX d \<pi> w \<equiv>
  \<forall>i < length \<pi>.
    \<not> (prefix
        (liftB w)
        (cfg_conf (the (get_configuration (d i)))))"

end
