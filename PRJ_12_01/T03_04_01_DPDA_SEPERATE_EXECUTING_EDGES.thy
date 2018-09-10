section {*T03\_04\_01\_DPDA\_SEPERATE\_EXECUTING\_EDGES*}
theory
  T03_04_01_DPDA_SEPERATE_EXECUTING_EDGES

imports
  PRJ_12_01__PRE

begin

datatype ('state, 'event, 'stack) DT_state_or_edge =
  cons_state_or_edge_old "'state"
  | cons_state_or_edge_new "('state, 'event, 'stack) epda_step_label"

definition F_DPDA_SEE__edge_then_1 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_SEE__edge_then_1 e \<equiv>
  \<lparr>edge_src = cons_state_or_edge_old (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_pop e,
  edge_trg = cons_state_or_edge_new e\<rparr>"

definition F_DPDA_SEE__edge_then_2 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_SEE__edge_then_2 e \<equiv>
  \<lparr>edge_src = cons_state_or_edge_new e,
  edge_event = None,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = cons_state_or_edge_old (edge_trg e)\<rparr>"

definition F_DPDA_SEE__edge_then :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_SEE__edge_then e \<equiv>
  {F_DPDA_SEE__edge_then_1 e, F_DPDA_SEE__edge_then_2 e}"

definition F_DPDA_SEE__edge_else_1 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_SEE__edge_else_1 e \<equiv>
  \<lparr>edge_src = cons_state_or_edge_old (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = cons_state_or_edge_old (edge_trg e)\<rparr>"

definition F_DPDA_SEE__edge_else :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_SEE__edge_else e \<equiv>
  {F_DPDA_SEE__edge_else_1 e}"

definition F_DPDA_SEE__edge_if :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_SEE__edge_if e \<equiv>
  edge_event e \<noteq> None \<and> edge_pop e \<noteq> edge_push e"

definition F_DPDA_SEE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda"
  where
    "F_DPDA_SEE G \<equiv>
  \<lparr>epda_states = cons_state_or_edge_old ` epda_states G \<union> cons_state_or_edge_new ` epda_delta G,
  epda_events = epda_events G,
  epda_gamma = epda_gamma G,
  epda_delta =
    \<Union> (
      (\<lambda>e.
        if F_DPDA_SEE__edge_if e
        then F_DPDA_SEE__edge_then e
        else F_DPDA_SEE__edge_else e)
      ` epda_delta G),
  epda_initial = cons_state_or_edge_old (epda_initial G),
  epda_box = epda_box G,
  epda_marking = cons_state_or_edge_old ` epda_marking G\<rparr>"

end

