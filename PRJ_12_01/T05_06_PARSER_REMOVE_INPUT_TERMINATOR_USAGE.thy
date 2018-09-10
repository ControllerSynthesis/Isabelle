section {*T05\_06\_PARSER\_REMOVE\_INPUT\_TERMINATOR\_USAGE*}
theory
  T05_06_PARSER_REMOVE_INPUT_TERMINATOR_USAGE

imports
  PRJ_12_01__PRE

begin

definition F_PARSER_RITU :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack, 'event, 'marker option) parser"
  where
    "F_PARSER_RITU P \<equiv>
  let
    R = {r. r \<in> parser_rules P \<and> rule_rpop r \<noteq> [parser_bottom P]}
  in
    P \<lparr>parser_rules := R,
       parser_marking :=
         {n. \<exists>r \<in> parser_rules P.
            rule_rpop r = [parser_bottom P]
            \<and> n = last (rule_lpop r)},
       parser_marker := \<lambda>r. if r \<in> R then parser_marker P r else None\<rparr>"

end
