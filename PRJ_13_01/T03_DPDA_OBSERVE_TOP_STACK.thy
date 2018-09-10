section {*T03\_DPDA\_OBSERVE\_TOP\_STACK*}
theory
  T03_DPDA_OBSERVE_TOP_STACK

imports
  PRJ_13_01__ENTRY

begin

declare [[ hypsubst_thin = false ]]
datatype ('state, 'stack) DT_state_and_stack_or_state =
  cons_state_and_stack "'state" "'stack"
  | cons_state "'state"
declare [[ hypsubst_thin = true ]]

definition F_DPDA_OTS__marking_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_state_and_stack_or_state set"
  where
    "F_DPDA_OTS__marking_states M \<equiv>
  (\<lambda> (q, X) . cons_state_and_stack q X)
    ` (epda_marking M \<times> epda_gamma M)"

definition F_DPDA_OTS__states_auxiliary :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_state_and_stack_or_state set"
  where
    "F_DPDA_OTS__states_auxiliary M \<equiv>
  (\<lambda> (q, X) . cons_state_and_stack q X)
    ` (epda_states M \<times> epda_gamma M)"

definition F_DPDA_OTS__states_main :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_state_and_stack_or_state set"
  where
    "F_DPDA_OTS__states_main M \<equiv>
  cons_state ` epda_states M"

definition F_DPDA_OTS__states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_state_and_stack_or_state set"
  where
    "F_DPDA_OTS__states M \<equiv>
  F_DPDA_OTS__states_auxiliary M \<union> F_DPDA_OTS__states_main M"

definition F_DPDA_OTS__edges_auxiliary_main_1 :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_OTS__edges_auxiliary_main_1 e \<equiv>
  \<lparr>edge_src = cons_state_and_stack (edge_src e) (hd (edge_pop e)),
   edge_event = edge_event e,
   edge_pop = edge_pop e,
   edge_push = edge_push e,
   edge_trg = cons_state (edge_trg e)\<rparr>"

definition F_DPDA_OTS__edges_auxiliary_main :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_OTS__edges_auxiliary_main M \<equiv>
  F_DPDA_OTS__edges_auxiliary_main_1
    ` epda_delta M"

definition F_DPDA_OTS__edges_main_auxiliary_1 :: "
  'state
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_OTS__edges_main_auxiliary_1 q X \<equiv>
  \<lparr>edge_src = cons_state q,
   edge_event = None,
   edge_pop = [X],
   edge_push = [X],
   edge_trg = cons_state_and_stack q X\<rparr>"

definition F_DPDA_OTS__edges_main_auxiliary :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_OTS__edges_main_auxiliary M \<equiv>
  (\<lambda> (x, y) . F_DPDA_OTS__edges_main_auxiliary_1 x y)
    ` (epda_states M \<times> epda_gamma M)"

definition F_DPDA_OTS__edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_OTS__edges M \<equiv>
  F_DPDA_OTS__edges_main_auxiliary M \<union> F_DPDA_OTS__edges_auxiliary_main M"

definition F_DPDA_OTS :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_state_and_stack_or_state, 'event, 'stack) epda"
  where
    "F_DPDA_OTS M \<equiv>
  \<lparr>epda_states = F_DPDA_OTS__states M,
   epda_events = epda_events M,
   epda_gamma = epda_gamma M,
   epda_delta = F_DPDA_OTS__edges M,
   epda_initial = cons_state_and_stack (epda_initial M) (epda_box M),
   epda_box = epda_box M,
   epda_marking = F_DPDA_OTS__marking_states M\<rparr>"

end
