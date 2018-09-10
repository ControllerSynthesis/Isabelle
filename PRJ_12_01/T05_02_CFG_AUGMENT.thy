section {*T05\_02\_CFG\_AUGMENT*}
theory
  T05_02_CFG_AUGMENT

imports
  PRJ_12_01__PRE

begin

definition F_CFG_AUGMENT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal
  \<Rightarrow> 'event
  \<Rightarrow> ('nonterminal, 'event) cfg"
  where
    "F_CFG_AUGMENT G FS FE \<equiv>
  \<lparr>cfg_nonterminals = cfg_nonterminals G \<union> {FS},
  cfg_events = cfg_events G \<union> {FE},
  cfg_initial = FS,
  cfg_productions =
      cfg_productions G
      \<union> {\<lparr>prod_lhs = FS, prod_rhs = [teB FE, teA (cfg_initial G), teB FE]\<rparr>}\<rparr>"

end

