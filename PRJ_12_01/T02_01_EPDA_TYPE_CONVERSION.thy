section {*T02\_01\_EPDA\_TYPE\_CONVERSION*}
theory
  T02_01_EPDA_TYPE_CONVERSION

imports
  T01_FRESH

begin

definition F_EPDA_TC__edge :: "
  ('stateA \<Rightarrow> 'stateB DT_symbol)
  \<Rightarrow> ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stateA, 'event, 'stackA) epda_step_label
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda_step_label"
  where
    "F_EPDA_TC__edge f_states f_stack e \<equiv>
  \<lparr>edge_src = f_states (edge_src e),
  edge_event = edge_event e,
  edge_pop = map f_stack (edge_pop e),
  edge_push = map f_stack (edge_push e),
  edge_trg = f_states (edge_trg e)\<rparr>"

definition F_EPDA_TC__epda :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateA \<Rightarrow> 'stateB DT_symbol)
  \<Rightarrow> ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda"
  where
    "F_EPDA_TC__epda G f_states f_stack \<equiv>
  \<lparr>epda_states = f_states ` epda_states G,
  epda_events = epda_events G,
  epda_gamma = f_stack ` epda_gamma G,
  epda_delta = F_EPDA_TC__edge f_states f_stack ` epda_delta G,
  epda_initial = f_states (epda_initial G),
  epda_box = f_stack (epda_box G),
  epda_marking = f_states ` epda_marking G\<rparr>"

definition F_EPDA_TC :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB DT_symbol, 'event, 'stackB DT_symbol) epda"
  where
    "F_EPDA_TC G \<equiv>
  F_EPDA_TC__epda
    G
    (SOME f. inj_on f (epda_states G))
    (SOME f. inj_on f (epda_gamma G))"

end

