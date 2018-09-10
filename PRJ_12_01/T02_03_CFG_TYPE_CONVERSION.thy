section {*T02\_03\_CFG\_TYPE\_CONVERSION*}
theory
  T02_03_CFG_TYPE_CONVERSION

imports
  T01_FRESH

begin

definition F_CFG_TC__word :: "
  ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal DT_symbol, 'event) DT_two_elements list"
  where
    "F_CFG_TC__word w \<equiv>
  map
    (\<lambda>x. case x of
          teA A \<Rightarrow> teA (cons_symbol_base A)
          | teB b \<Rightarrow>  teB b)
    w"

definition F_CFG_TC__production :: "
  ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg_step_label"
  where
    "F_CFG_TC__production e \<equiv>
  \<lparr>prod_lhs = cons_symbol_base (prod_lhs e),
  prod_rhs = F_CFG_TC__word (prod_rhs e)\<rparr>"

definition F_CFG_TC :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event) cfg"
  where
    "F_CFG_TC G \<equiv>
  \<lparr>cfg_nonterminals = cons_symbol_base ` cfg_nonterminals G,
  cfg_events = cfg_events G,
  cfg_initial = cons_symbol_base (cfg_initial G),
  cfg_productions = F_CFG_TC__production ` cfg_productions G\<rparr>"

end

