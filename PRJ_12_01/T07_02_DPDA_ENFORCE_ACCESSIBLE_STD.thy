section {*T07\_02\_DPDA\_ENFORCE\_ACCESSIBLE\_STD*}
theory
  T07_02_DPDA_ENFORCE_ACCESSIBLE_STD

imports
  T07_01_DPDA_DETERMINE_ACCEESSIBLE_EDGES

begin

definition F_DPDA_EA_STD :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda"
  where
    "F_DPDA_EA_STD G \<equiv>
  F_EPDA_RE G (F_DPDA_DAE G)"

end
