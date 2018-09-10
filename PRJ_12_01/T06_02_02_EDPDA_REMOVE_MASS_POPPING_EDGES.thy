section {*T06\_02\_02\_EDPDA\_REMOVE\_MASS\_POPPING\_EDGES*}
theory
  T06_02_02_EDPDA_REMOVE_MASS_POPPING_EDGES

imports
  T01_FRESH

begin

definition F_EDPDA_RMPOE__states_before_pop :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states_before_pop G \<equiv>
  {cons_tuple3 (edge_src e) w None | e w.
    e \<in> epda_delta G
    \<and> strict_prefix w (edge_pop e)}"

definition F_EDPDA_RMPOE__states_bottom_on_top :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states_bottom_on_top G \<equiv>
  {cons_tuple3 (edge_src e) (butlast (edge_pop e)) (Some (epda_box G)) | e.
    e \<in> epda_delta G
    \<and> suffix (edge_pop e) [epda_box G]}"

definition F_EDPDA_RMPOE__states_last_of_pop :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states_last_of_pop G \<equiv>
  {cons_tuple3 (edge_src e) (edge_pop e) None | e.
    e \<in> epda_delta G
    \<and> \<not> suffix (edge_pop e) [epda_box G]}"

definition F_EDPDA_RMPOE__pop_components :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'stack list set"
  where
    "F_EDPDA_RMPOE__pop_components G q \<equiv>
  {edge_pop e | e. edge_src e = q \<and> e \<in> epda_delta G}"

definition F_EDPDA_RMPOE__states_context_of_top :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states_context_of_top G \<equiv>
  {cons_tuple3 (edge_src e) x (Some \<gamma>) | e \<gamma> x.
    e \<in> epda_delta G
    \<and> prefix x (edge_pop e)
    \<and> \<not> suffix x [epda_box G]
    \<and> \<gamma> \<in> epda_gamma G
    \<and> x @ [\<gamma>] \<notin> prefix_closure (F_EDPDA_RMPOE__pop_components G (edge_src e))}"

definition F_EDPDA_RMPOE__states_basic :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states_basic G \<equiv>
  {cons_tuple3 q [] None | q.
  q \<in> epda_states G}"

definition F_EDPDA_RMPOE__edges_append_list :: "
  ('state, 'stack list, 'stack option) DT_tuple3 set
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label set"
  where
    "F_EDPDA_RMPOE__edges_append_list Q \<equiv>
  {\<lparr>edge_src = cons_tuple3 q w None,
    edge_event = None,
    edge_pop = [a],
    edge_push = [],
    edge_trg = cons_tuple3 q (w @ [a]) None\<rparr> | q w a.
      cons_tuple3 q w None \<in> Q
      \<and> cons_tuple3 q (w @ [a]) None \<in> Q}"

definition F_EDPDA_RMPOE__edges_append_option :: "
  ('state, 'stack list, 'stack option) DT_tuple3 set
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label set"
  where
    "F_EDPDA_RMPOE__edges_append_option Q \<equiv>
  {\<lparr>edge_src = cons_tuple3 q w None,
    edge_event = None,
    edge_pop = [a],
    edge_push = [a],
    edge_trg = cons_tuple3 q w (Some a)\<rparr> | q w a.
      cons_tuple3 q w None \<in> Q
      \<and> cons_tuple3 q w (Some a) \<in> Q}"

definition F_EDPDA_RMPOE__edges_final :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label set"
  where
    "F_EDPDA_RMPOE__edges_final G Q \<equiv>
  {\<lparr>edge_src = cons_tuple3 (edge_src e) x (Some \<gamma>),
    edge_event = edge_event e,
    edge_pop = [\<gamma>],
    edge_push = edge_push e @ the (left_quotient_word (edge_pop e) (x @ [\<gamma>])),
    edge_trg = cons_tuple3 (edge_trg e) [] None\<rparr> | x e \<gamma>.
        e \<in> epda_delta G
        \<and> prefix (edge_pop e) (x @ [\<gamma>])
        \<and> cons_tuple3 (edge_src e) x (Some \<gamma>) \<in> Q}"

definition F_EDPDA_RMPOE__states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set"
  where
    "F_EDPDA_RMPOE__states G \<equiv>
  F_EDPDA_RMPOE__states_before_pop G
  \<union> F_EDPDA_RMPOE__states_bottom_on_top G
  \<union> F_EDPDA_RMPOE__states_last_of_pop G
  \<union> F_EDPDA_RMPOE__states_context_of_top G
  \<union> F_EDPDA_RMPOE__states_basic G"

definition F_EDPDA_RMPOE__edges :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack list, 'stack option) DT_tuple3 set
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label set"
  where
    "F_EDPDA_RMPOE__edges G Q \<equiv>
  F_EDPDA_RMPOE__edges_final G Q
  \<union> F_EDPDA_RMPOE__edges_append_list Q
  \<union> F_EDPDA_RMPOE__edges_append_option Q"
 
definition F_EDPDA_RMPOE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda"
  where
    "F_EDPDA_RMPOE G \<equiv>
  let
    states = F_EDPDA_RMPOE__states G;
    delta = F_EDPDA_RMPOE__edges G states
  in
    \<lparr>epda_states = states,
     epda_events = epda_events G,
     epda_gamma = epda_gamma G,
     epda_delta = delta,
     epda_initial = cons_tuple3 (epda_initial G) [] None,
     epda_box = epda_box G,
     epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G\<rparr>"

end
