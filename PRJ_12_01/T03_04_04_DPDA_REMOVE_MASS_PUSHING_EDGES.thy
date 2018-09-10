section {*T03\_04\_04\_DPDA\_REMOVE\_MASS\_PUSHING\_EDGES*}
theory
  T03_04_04_DPDA_REMOVE_MASS_PUSHING_EDGES

imports
  PRJ_12_01__PRE

begin

declare [[ hypsubst_thin = false ]]
datatype ('state, 'event, 'stack) DT_state_or_edge_nat =
  cons_state_or_edge_nat_old "'state"
  | cons_state_or_edge_nat_new "('state, 'event, 'stack) epda_step_label" "nat"
declare [[ hypsubst_thin = true ]]

definition F_DPDA_RMPUE__state :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'event, 'stack) DT_state_or_edge_nat option"
  where
    "F_DPDA_RMPUE__state e n \<equiv>
  if n = 0
  then Some (cons_state_or_edge_nat_old (edge_src e))
  else (if Suc n < length (edge_push e)
        then Some (cons_state_or_edge_nat_new e n)
        else (if Suc n = length (edge_push e)
              then Some (cons_state_or_edge_nat_old (edge_trg e))
              else None))"

definition F_DPDA_RMPUE__edge_if :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_DPDA_RMPUE__edge_if e \<equiv>
  length (edge_push e) > Suc (Suc 0)"

definition F_DPDA_RMPUE__edge_then :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_RMPUE__edge_then e \<equiv>
  \<Union> (
    (\<lambda>i.
      {\<lparr>edge_src = the (F_DPDA_RMPUE__state e i),
      edge_event = None,
      edge_pop = [rev (edge_push e) ! i],
      edge_push = [rev (edge_push e) ! Suc i] @ [rev (edge_push e) ! i],
      edge_trg = the (F_DPDA_RMPUE__state e (Suc i))\<rparr>})
    ` {i. 0 \<le> i \<and> Suc i < length (edge_push e)})"

definition F_DPDA_RMPUE__edge_else :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label"
  where
    "F_DPDA_RMPUE__edge_else e \<equiv>
  \<lparr>edge_src = cons_state_or_edge_nat_old (edge_src e),
  edge_event = edge_event e,
  edge_pop = edge_pop e,
  edge_push = edge_push e,
  edge_trg = cons_state_or_edge_nat_old (edge_trg e)\<rparr>"

definition F_DPDA_RMPUE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda"
  where
    "F_DPDA_RMPUE G \<equiv>
  \<lparr>epda_states =
    (cons_state_or_edge_nat_old ` epda_states G)
    \<union> \<Union> (
      (\<lambda>e.
       (\<lambda>i.
        the (F_DPDA_RMPUE__state e i))
       ` {i. 0 \<le> i \<and> Suc i \<le> length (edge_push e)})
      ` epda_delta G),
  epda_events = epda_events G,
  epda_gamma = epda_gamma G,
  epda_delta =
    \<Union> (
      (\<lambda>e.
        if F_DPDA_RMPUE__edge_if e
        then F_DPDA_RMPUE__edge_then e
        else {F_DPDA_RMPUE__edge_else e})
      ` epda_delta G),
  epda_initial = cons_state_or_edge_nat_old (epda_initial G),
  epda_box = epda_box G,
  epda_marking = cons_state_or_edge_nat_old ` epda_marking G\<rparr>"

end
