section {*T07\_DPDA\_RESTRICT\_TO\_CONTROLLABLE\_STATES*}
theory
  T07_DPDA_RESTRICT_TO_CONTROLLABLE_STATES

imports
  PRJ_13_01__ENTRY
  T03_DPDA_OBSERVE_TOP_STACK
  T04_DPDA_ENFORCE_UNIQUE_MARKING_LATE

begin

definition F_DPDA_NCS :: "
  ((((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> 'event set
  \<Rightarrow> (((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state set"
  where
    "F_DPDA_NCS S P \<Sigma>UC \<equiv>
  {q | q f pS pP X u eP.
    q \<in> epda_states S
    \<and> q = f (cons_state_and_stack (cons_tuple2 pS pP) X)
    \<and> f \<in> {cons_state_or_state_new, cons_state_or_state_old}
    \<and> q \<notin> epda_nonstable_states (epda_delta S)
    \<and> u \<in> \<Sigma>UC
    \<and> eP \<in> epda_delta P
    \<and> edge_src eP = pP
    \<and> edge_event eP = Some u
    \<and> \<not>(\<exists>eS \<in> epda_delta S.
        edge_src eS = q
        \<and> edge_event eS = Some u
        \<and> edge_pop eS = [X])}"

definition F_DPDA_RCS :: "
  ((((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> 'event set
  \<Rightarrow> (((((('stateA, 'stateB) DT_tuple2) , 'stackA) DT_state_and_stack_or_state) DT_state_or_state, 'event, 'stackA) epda) option \<times> bool"
  where
    "F_DPDA_RCS M P \<Sigma>UC \<equiv>
  let
    Q = F_DPDA_NCS M P \<Sigma>UC
  in
    (F_EPDA_RS M (epda_states M - Q), Q = {})"

end
