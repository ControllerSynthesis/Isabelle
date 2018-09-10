section {*T06\_02\_01\_EDPDA\_REMOVE\_NIL\_POPPING\_EDGES*}
theory
  T06_02_01_EDPDA_REMOVE_NIL_POPPING_EDGES

imports
  T01_FRESH

begin

definition F_EDPDA_RNPE__edges :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_EDPDA_RNPE__edges e X \<equiv>
  {\<lparr>edge_src = edge_src e,
   edge_event = edge_event e,
   edge_pop = [x],
   edge_push = edge_push e @ [x],
   edge_trg = edge_trg e\<rparr>
    | x. x \<in> X}"

definition F_EDPDA_RNPE :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda"
  where
    "F_EDPDA_RNPE G \<equiv>
  \<lparr>epda_states = epda_states G,
   epda_events = epda_events G,
   epda_gamma = epda_gamma G,
   epda_delta = \<Union>
      ((\<lambda>e.
        if edge_pop e = []
        then F_EDPDA_RNPE__edges e (epda_gamma G)
        else {e})
      ` epda_delta G),
   epda_initial = epda_initial G,
   epda_box = epda_box G,
   epda_marking = epda_marking G\<rparr>"

end
