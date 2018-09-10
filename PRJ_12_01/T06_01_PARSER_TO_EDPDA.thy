section {*T06\_01\_PARSER\_TO\_EDPDA*}
theory
  T06_01_PARSER_TO_EDPDA

imports
  PRJ_12_01__PRE

begin

definition F_PARSER_TO_EDPDA__rules :: "
  ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event, 'stack) epda_step_label"
  where
    "F_PARSER_TO_EDPDA__rules e \<equiv>
  \<lparr>edge_src = last (rule_lpop e),
   edge_event = list_to_option (rule_rpop e),
   edge_pop = rev (butlast (rule_lpop e)),
   edge_push = rev (butlast (rule_lpush e)),
   edge_trg = last (rule_lpush e)\<rparr>"

definition F_PARSER_TO_EDPDA :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'stack
  \<Rightarrow> ('stack, 'event, 'stack) epda"
  where
    "F_PARSER_TO_EDPDA G BOX \<equiv>
  \<lparr>epda_states = parser_nonterms G,
   epda_events = parser_events G - {parser_bottom G},
   epda_gamma = parser_nonterms G \<union> {BOX},
   epda_delta = F_PARSER_TO_EDPDA__rules ` (parser_rules G),
   epda_initial = parser_initial G,
   epda_box = BOX,
   epda_marking = parser_marking G\<rparr>"

end
