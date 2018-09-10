section {*T05\_04\_LR\_MACHINE*}
theory
  T05_04_LR_MACHINE

imports
  T05_03_VALID_ITEM_SETS

begin

definition F_LR_MACHINE__one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set) set
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set"
  where
    "F_LR_MACHINE__one G F k S \<equiv>
  (\<lambda>(q, X).
    \<lparr>edge_src = q,
    edge_event = Some X,
    edge_pop = [0],
    edge_push = [0],
    edge_trg = F_VALID_ITEM_SET_GOTO G F k X q\<rparr>)
  `
  (S \<times> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)))"

function (domintros) F_LR_MACHINE__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set) set
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set) set
  \<Rightarrow> ((('nonterminal, 'event) DT_cfg_item set) set \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set)"
  where
    "F_LR_MACHINE__fp_one G F k E V S =
  (if S = {}
  then (V, E)
  else F_LR_MACHINE__fp_one G F k
       (E \<union> F_LR_MACHINE__one G F k S)
       (V \<union> S)
       ((edge_trg ` F_LR_MACHINE__one G F k S) - (V \<union> S)))"
  by pat_completeness auto

definition F_LR_MACHINE :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements , nat) epda"
  where
    "F_LR_MACHINE G F k \<equiv>
  \<lparr>epda_states = fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}),
  epda_events = two_elements_construct_domain (cfg_nonterminals G) (cfg_events G),
  epda_gamma = {0},
  epda_delta = snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}),
  epda_initial = F_VALID_ITEM_SET_INITIAL G F k,
  epda_box = 0,
  epda_marking = {}\<rparr>"

end
