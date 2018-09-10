section {*T07\_03\_DPDA\_DETERMINE\_REQUIRED\_EDGES*}
theory
  T07_03_DPDA_DETERMINE_REQUIRED_EDGES

imports
  T07_01_DPDA_DETERMINE_ACCEESSIBLE_EDGES

begin

definition F_DPDA_DRE :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda_step_label set"
  where
    "F_DPDA_DRE G0 k \<equiv>
  let
    G1 = F_DPDA_SEE G0;
    PB = F_FRESH (epda_gamma G1);
    G2 = F_DPDA_RNE G1 PB;
    G3 = F_DPDA_SPPE G2;
    G4 = F_DPDA_RMPUE G3;
    G5 = F_SDPDA_TO_LR1_OPT G4 k;
    Pr = case G5 of None \<Rightarrow> {} | Some G5 \<Rightarrow> cfg_productions G5;
    RE4 = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G4 Pr;
    RE3 = F_DPDA_DRE__revert_F_DPDA_RMPUE G3 RE4;
    RE2 = F_DPDA_DRE__revert_F_DPDA_SPPE G2 RE3;
    RE1 = F_DPDA_DRE__revert_F_DPDA_RNE G1 PB RE2;
    RE0 = F_DPDA_DRE__revert_F_DPDA_SEE G0 RE1
  in
    RE0"

end

