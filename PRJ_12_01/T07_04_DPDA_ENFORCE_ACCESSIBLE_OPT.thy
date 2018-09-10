section {*T07\_04\_DPDA\_ENFORCE\_ACCESSIBLE\_OPT*}
theory
  T07_04_DPDA_ENFORCE_ACCESSIBLE_OPT

imports
  T07_03_DPDA_DETERMINE_REQUIRED_EDGES

begin

definition F_DPDA_EA_OPT :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda"
  where
    "F_DPDA_EA_OPT G \<equiv>
  F_EPDA_RE G (F_DPDA_DRE G (Suc 0))"

end
