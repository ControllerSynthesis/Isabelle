section {*T03\_04\_02\_DPDA\_REMOVE\_NEUTRAL\_EDGES*}
theory
  T03_04_02_DPDA_REMOVE_NEUTRAL_EDGES

imports
  T03_04_01_DPDA_SEPERATE_EXECUTING_EDGES

begin

definition F_DPDA_RNE__edge_else :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_RNE__edge_else e \<equiv>
  \<lparr>edge_src = cons_state_or_edge_old (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = cons_state_or_edge_old (edge_trg e)\<rparr>"

definition F_DPDA_RNE__edge_then_1 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_RNE__edge_then_1 e PB \<equiv>
  \<lparr>edge_src = cons_state_or_edge_old (edge_src e),
  edge_event = None,
  edge_pop = edge_pop e,
  edge_push = [PB] @ edge_pop e,
  edge_trg = cons_state_or_edge_new e\<rparr>"

definition F_DPDA_RNE__edge_then_2 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_RNE__edge_then_2 e PB \<equiv>
  \<lparr>edge_src = cons_state_or_edge_new e,
  edge_event = None,
  edge_pop = [PB],
  edge_push = [],
  edge_trg = cons_state_or_edge_old (edge_trg e)\<rparr>"

definition F_DPDA_RNE__edge_then :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_RNE__edge_then e PB \<equiv>
  {F_DPDA_RNE__edge_then_1 e PB, F_DPDA_RNE__edge_then_2 e PB}"

definition FB_neutral_edge :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "FB_neutral_edge e \<equiv>
  edge_event e = None \<and> edge_pop e = edge_push e"

definition F_DPDA_RNE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda"
  where
    "F_DPDA_RNE G PB \<equiv>
  \<lparr>epda_states = cons_state_or_edge_old ` epda_states G \<union> cons_state_or_edge_new ` epda_delta G,
  epda_events = epda_events G,
  epda_gamma = epda_gamma G \<union> {PB},
  epda_delta =
    \<Union> (
      (\<lambda>e.
        if FB_neutral_edge e
        then F_DPDA_RNE__edge_then e PB
        else {F_DPDA_RNE__edge_else e})
      ` epda_delta G),
  epda_initial = cons_state_or_edge_old (epda_initial G),
  epda_box = epda_box G,
  epda_marking = cons_state_or_edge_old ` epda_marking G\<rparr>"

end
