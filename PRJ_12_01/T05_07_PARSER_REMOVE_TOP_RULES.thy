section {*T05\_07\_PARSER\_REMOVE\_TOP\_RULES*}
theory
  T05_07_PARSER_REMOVE_TOP_RULES

imports
  PRJ_12_01__PRE

begin

definition F_PARSER_RTR__rules_annotate_element :: "
  'stack
  \<Rightarrow> 'event list
  \<Rightarrow> 'stack \<times> 'event list"
  where
    "F_PARSER_RTR__rules_annotate_element a x \<equiv>
  (a, x)"

definition F_PARSER_RTR__rules_annotate_word :: "
  'stack list
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack \<times> 'event list) list"
  where
    "F_PARSER_RTR__rules_annotate_word w x \<equiv>
  case w of
  [] \<Rightarrow> []
  | a' # w' \<Rightarrow>
    map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @
    map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last w]"

definition F_PARSER_RTR__rules_shift_new_observed :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack \<times> 'event list, 'event) parser_step_label set"
  where
    "F_PARSER_RTR__rules_shift_new_observed P \<equiv>
  {\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [],
    rule_rpop = rule_rpop r,
    rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) [],
    rule_rpush = []\<rparr>
      | r. r \<in> parser_rules P \<and> rule_rpush r = []}"

definition F_PARSER_RTR__rules_shift_old_observed :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack \<times> 'event list, 'event) parser_step_label set"
  where
    "F_PARSER_RTR__rules_shift_old_observed P \<equiv>
  {\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r),
    rule_rpop = [],
    rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) [],
    rule_rpush = []\<rparr>
      | r. r \<in> parser_rules P \<and> rule_rpush r = []}"

definition F_PARSER_RTR__rules_reduce_old_observe :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack \<times> 'event list, 'event) parser_step_label set"
  where
    "F_PARSER_RTR__rules_reduce_old_observe P \<equiv>
  {\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [],
    rule_rpop = rule_rpop r,
    rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r),
    rule_rpush = []\<rparr>
      | r. r \<in> parser_rules P \<and> rule_rpush r = rule_rpop r}"

definition F_PARSER_RTR__rules_reduce_new_observe :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack \<times> 'event list, 'event) parser_step_label set"
  where
    "F_PARSER_RTR__rules_reduce_new_observe P \<equiv>
  {\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r),
    rule_rpop = [],
    rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r),
    rule_rpush = []\<rparr>
      | r. r \<in> parser_rules P \<and> rule_rpush r = rule_rpop r}"

definition F_PARSER_RTR :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> ('stack \<times> ('event list), 'event, 'marker option) parser"
  where
    "F_PARSER_RTR P \<equiv>
  let
    R = F_PARSER_RTR__rules_shift_new_observed P
        \<union> F_PARSER_RTR__rules_shift_old_observed P
        \<union> F_PARSER_RTR__rules_reduce_old_observe P
        \<union> F_PARSER_RTR__rules_reduce_new_observe P;
    N = {n. \<exists>r \<in> R.
          n \<in> set (rule_lpop r)
          \<or> n \<in> set(rule_lpush r)}
        \<union> {F_PARSER_RTR__rules_annotate_element (parser_initial P) []}
  in
    \<lparr>parser_nonterms = N,
     parser_events = parser_events P,
     parser_initial = F_PARSER_RTR__rules_annotate_element (parser_initial P) [],
     parser_marking = N \<inter> ((\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) ` (parser_marking P)),
     parser_rules = R,
     parser_marker = \<lambda>r. None,
     parser_bottom = parser_bottom P\<rparr>"

end
