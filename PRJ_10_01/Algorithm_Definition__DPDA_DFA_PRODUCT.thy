section {*Algorithm\_Definition\_\_DPDA\_DFA\_PRODUCT*}
theory
  Algorithm_Definition__DPDA_DFA_PRODUCT

imports
  PRJ_10_01__ENTRY

begin

declare [[ hypsubst_thin = false ]]
datatype ('a, 'b) DT_tuple2 =
  cons_tuple2  (sel_tuple2_1: "'a") (sel_tuple2_2: "'b")

datatype ('a, 'b, 'c) DT_tuple3 =
  cons_tuple3
  (sel_tuple3_1: "'a")
  (sel_tuple3_2: "'b")
  (sel_tuple3_3: "'c")
declare [[ hypsubst_thin = true ]]

definition F_DPDA_DFA_PRODUCT__states :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> ('stateA, 'stateB) DT_tuple2 set"
  where
    "F_DPDA_DFA_PRODUCT__states C P \<equiv>
  {cons_tuple2 p q | p q.
    p \<in> epda_states C \<and> q \<in> epda_states P}"

definition F_DPDA_DFA_PRODUCT__marking_states :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> ('stateA, 'stateB) DT_tuple2 set"
  where
    "F_DPDA_DFA_PRODUCT__marking_states C P \<equiv>
  {cons_tuple2 p q | p q.
    p \<in> epda_marking C \<and> q \<in> epda_marking P}"

definition F_DPDA_DFA_PRODUCT__events :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> 'event set"
  where
    "F_DPDA_DFA_PRODUCT__events C P \<equiv>
  epda_events C \<inter> epda_events P"

definition F_DPDA_DFA_PRODUCT__edges_execute :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> (('stateA, 'stateB) DT_tuple2, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DFA_PRODUCT__edges_execute C P \<equiv>
  {\<lparr>edge_src = cons_tuple2 (edge_src e) (edge_src e'),
    edge_event = edge_event e,
    edge_pop = edge_pop e,
    edge_push = edge_push e,
    edge_trg = cons_tuple2 (edge_trg e) (edge_trg e')\<rparr> | e e'.
      e \<in> epda_delta C
      \<and> e' \<in> epda_delta P
      \<and> edge_event e = edge_event e'}"

definition F_DPDA_DFA_PRODUCT__edges_empty :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> (('stateA, 'stateB) DT_tuple2, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DFA_PRODUCT__edges_empty C P \<equiv>
  {\<lparr>edge_src = cons_tuple2 (edge_src e) p,
    edge_event = None,
    edge_pop = edge_pop e,
    edge_push = edge_push e,
    edge_trg = cons_tuple2 (edge_trg e) p\<rparr> | e p.
      p \<in> epda_states P
      \<and> e \<in> epda_delta C
      \<and> edge_event e = None}"

definition F_DPDA_DFA_PRODUCT__edges :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> (('stateA, 'stateB) DT_tuple2, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DFA_PRODUCT__edges C P \<equiv>
  F_DPDA_DFA_PRODUCT__edges_execute C P \<union> F_DPDA_DFA_PRODUCT__edges_empty C P"

definition F_DPDA_DFA_PRODUCT :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, nat) epda
  \<Rightarrow> (('stateA, 'stateB) DT_tuple2, 'event, 'stack) epda"
  where
    "F_DPDA_DFA_PRODUCT C P \<equiv>
  \<lparr>epda_states = F_DPDA_DFA_PRODUCT__states C P,
   epda_events = F_DPDA_DFA_PRODUCT__events C P,
   epda_gamma = epda_gamma C,
   epda_delta = F_DPDA_DFA_PRODUCT__edges C P,
   epda_initial = cons_tuple2 (epda_initial C) (epda_initial P),
   epda_box = epda_box C,
   epda_marking = F_DPDA_DFA_PRODUCT__marking_states C P\<rparr>"

definition epda_nonstable_states :: "
  ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> 'state set"
  where
    "epda_nonstable_states E \<equiv>
  {q. \<exists>e \<in> E. edge_src e = q \<and> edge_event e = None}"    

end
