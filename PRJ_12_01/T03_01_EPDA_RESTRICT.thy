section {*T03\_01\_EPDA\_RESTRICT*}
theory
  T03_01_EPDA_RESTRICT

imports
  PRJ_12_01__PRE

begin

definition F_EPDA_R :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda"
  where
    "F_EPDA_R G Q E \<equiv>
  \<lparr>epda_states = epda_states G \<inter> Q,
  epda_events = epda_events G,
  epda_gamma = epda_gamma G,
  epda_delta =
    {e \<in> epda_delta G \<inter> E.
      edge_src e \<in> epda_states G \<inter> Q \<and> edge_trg e \<in> epda_states G \<inter> Q},
  epda_initial = epda_initial G,
  epda_box = epda_box G,
  epda_marking = epda_marking G \<inter> Q\<rparr>"

definition F_EPDA_RE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda"
  where
    "F_EPDA_RE G E \<equiv>
  let
    Q = {epda_initial G}
        \<union> {q \<in> epda_states G.
            \<exists>e \<in> epda_delta G \<inter> E.
              edge_src e = q \<or> edge_trg e = q}
  in
    F_EPDA_R G Q E"

definition F_EPDA_RS :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state set
  \<Rightarrow> ('state, 'event, 'stack) epda option"
  where
    "F_EPDA_RS G Q \<equiv>
  if epda_initial G \<notin> Q
  then None
  else Some (F_EPDA_R G Q (epda_delta G))"

end

