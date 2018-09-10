section {*T02\_02\_PARSER\_TYPE\_CONVERSION*}
theory
  T02_02_PARSER_TYPE_CONVERSION

imports
  T01_FRESH

begin

definition F_PARSER_TC__rule :: "
  ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stackA, 'event) parser_step_label
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label"
  where
    "F_PARSER_TC__rule fstack e \<equiv>
  \<lparr>rule_lpop = map fstack (rule_lpop e),
  rule_rpop = rule_rpop e,
  rule_lpush = map fstack (rule_lpush e),
  rule_rpush = rule_rpush e\<rparr>"

definition F_PARSER_TC__parser :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser"
  where
    "F_PARSER_TC__parser G fstack \<equiv>
  \<lparr>parser_nonterms = fstack ` parser_nonterms G,
  parser_events = parser_events G,
  parser_initial = fstack (parser_initial G),
  parser_marking = fstack ` parser_marking G,
  parser_rules = F_PARSER_TC__rule fstack ` parser_rules G,
  parser_marker = \<lambda>x. None,
  parser_bottom = parser_bottom G\<rparr>"

definition F_PARSER_TC :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser"
  where
    "F_PARSER_TC G \<equiv>
  F_PARSER_TC__parser
    G
    (SOME fstack. inj_on fstack (parser_nonterms G))"

end

