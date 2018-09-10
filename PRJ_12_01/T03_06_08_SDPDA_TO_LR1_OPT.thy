section {*T03\_06\_08\_SDPDA\_TO\_LR1\_OPT*}
theory
  T03_06_08_SDPDA_TO_LR1_OPT

imports
  T03_06_02_SDPDA_TO_CFG_OPT
  T03_06_05_CFG_TRIM

begin

definition F_SDPDA_TO_LR1_OPT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg option"
  where
    "F_SDPDA_TO_LR1_OPT G k \<equiv>
  case F_SDPDA_TO_CFG_OPT G k of
    None \<Rightarrow> None
    | Some G \<Rightarrow> F_CFG_TRIM G"

end

