section {*T03\_05\_SDPDA\_ENFORCE\_UNIQUE\_MARKING\_EARLY*}
theory
  T03_05_SDPDA_ENFORCE_UNIQUE_MARKING_EARLY

imports
  PRJ_12_01__PRE

begin

declare [[ hypsubst_thin = false ]]
datatype 'state DT_state_or_state =
  cons_state_or_state_old "'state"
  | cons_state_or_state_new "'state"
declare [[ hypsubst_thin = true ]]

definition FB_executing_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "FB_executing_edge e \<equiv>
  edge_event e \<noteq> None"

definition F_SDPDA_EUME__edge_annotation :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state \<Rightarrow> 'state DT_state_or_state)
  \<Rightarrow> ('state \<Rightarrow> 'state DT_state_or_state)
  \<Rightarrow> ('state DT_state_or_state, 'event, 'stack) epda_step_label"
  where
    "F_SDPDA_EUME__edge_annotation e s t \<equiv>
  \<lparr>edge_src = s (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = t (edge_trg e)\<rparr>"

definition F_SDPDA_EUME__edges :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'state set
  \<Rightarrow> ('state DT_state_or_state, 'event, 'stack) epda_step_label set"
  where
    "F_SDPDA_EUME__edges e FS \<equiv>
  if FB_executing_edge e
  then {F_SDPDA_EUME__edge_annotation e cons_state_or_state_old cons_state_or_state_old, F_SDPDA_EUME__edge_annotation e cons_state_or_state_new cons_state_or_state_old}
  else {F_SDPDA_EUME__edge_annotation e cons_state_or_state_new cons_state_or_state_new}
    \<union> (if edge_src e \<in> FS
       then {F_SDPDA_EUME__edge_annotation e cons_state_or_state_old cons_state_or_state_new}
       else {F_SDPDA_EUME__edge_annotation e cons_state_or_state_old cons_state_or_state_old})"

definition F_SDPDA_EUME :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state DT_state_or_state, 'event, 'stack) epda"
  where
    "F_SDPDA_EUME G \<equiv>
  \<lparr>epda_states = cons_state_or_state_old ` epda_states G \<union> cons_state_or_state_new ` epda_states G,
  epda_events = epda_events G,
  epda_gamma = epda_gamma G,
  epda_delta = \<Union>((\<lambda>e. F_SDPDA_EUME__edges e (epda_marking G)) ` epda_delta G),
  epda_initial = cons_state_or_state_old (epda_initial G),
  epda_box = epda_box G,
  epda_marking = cons_state_or_state_old ` epda_marking G\<rparr>"

end

