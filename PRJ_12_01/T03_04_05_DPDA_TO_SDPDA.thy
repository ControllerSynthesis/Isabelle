section {*T03\_04\_05\_DPDA\_TO\_SDPDA*}
theory
  T03_04_05_DPDA_TO_SDPDA

imports
  T01_FRESH
  T03_04_01_DPDA_SEPERATE_EXECUTING_EDGES
  T03_04_02_DPDA_REMOVE_NEUTRAL_EDGES
  T03_04_03_DPDA_SEPERATE_PUSH_POP_EDGES
  T03_04_04_DPDA_REMOVE_MASS_PUSHING_EDGES

begin

definition F_DPDA_TO_SDPDA :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ((((('state, 'event, 'stack DT_symbol) DT_state_or_edge, 'event, 'stack DT_symbol) DT_state_or_edge, 'event, 'stack DT_symbol) DT_state_or_edge, 'event, 'stack DT_symbol) DT_state_or_edge_nat, 'event, 'stack DT_symbol) epda"
  where
    "F_DPDA_TO_SDPDA G \<equiv>
  let
    G2 = F_DPDA_SEE G;
    G3 = F_DPDA_RNE G2 (F_FRESH (epda_gamma G2));
    G4 = F_DPDA_SPPE G3;
    G5 = F_DPDA_RMPUE G4
  in
    G5"

end
