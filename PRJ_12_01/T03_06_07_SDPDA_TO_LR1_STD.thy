section {*T03\_06\_07\_SDPDA\_TO\_LR1\_STD*}
theory
  T03_06_07_SDPDA_TO_LR1_STD

imports
  T03_06_01_SDPDA_TO_CFG_STD
  T03_06_05_CFG_TRIM

begin

definition F_SDPDA_TO_LR1_STD :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg option"
  where
    "F_SDPDA_TO_LR1_STD G \<equiv>
  F_CFG_TRIM (F_SDPDA_TO_CFG_STD G)"

end

