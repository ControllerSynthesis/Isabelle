section {*T06\_02\_03\_EDPDA\_TO\_DPDA*}
theory
  T06_02_03_EDPDA_TO_DPDA

imports
  T06_02_01_EDPDA_REMOVE_NIL_POPPING_EDGES
  T06_02_02_EDPDA_REMOVE_MASS_POPPING_EDGES

begin

definition F_EDPDA_TO_DPDA :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> (('state, 'stack DT_symbol list, 'stack DT_symbol option) DT_tuple3, 'event, 'stack DT_symbol) epda"
  where
    "F_EDPDA_TO_DPDA G \<equiv>
  F_EDPDA_RMPOE (F_EDPDA_RNPE G)"

end
