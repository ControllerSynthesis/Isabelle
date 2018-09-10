section {*T04\_DPDA\_ENFORCE\_UNIQUE\_MARKING\_LATE*}
theory
  T04_DPDA_ENFORCE_UNIQUE_MARKING_LATE

imports
  PRJ_13_01__ENTRY

begin

definition F_DPDA_EUML :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state DT_state_or_state, 'event, 'stack) epda"
  where
    "F_DPDA_EUML G \<equiv>
  let
    G' = F_SDPDA_EUME G
  in
    G'\<lparr>epda_marking :=
      (cons_state_or_state_old ` epda_marking G \<union> cons_state_or_state_new ` epda_states G)
      - epda_nonstable_states (epda_delta G')\<rparr>"

end
