section {*T03\_06\_01\_SDPDA\_TO\_CFG\_STD*}
theory
  T03_06_01_SDPDA_TO_CFG_STD

imports
  T03_03_EPDA_APPROXIMATE_ACCESSIBLE

begin

declare [[ hypsubst_thin = false ]]
datatype ('state, 'stack) DT_l2_l3_nonterminals =
  cons_l2 "'state" "'stack"
  | cons_l3 "'state" "'stack" "'state"
declare [[ hypsubst_thin = true ]]

definition F_SDPDA_TO_CFG_STD__edges_l3_read :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'state set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l3_read e Q \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e) (edge_pop e ! 0) qt,
    prod_rhs =
      [teB (the (edge_event e))]
      @ [teA (cons_l3   (edge_trg e) (edge_pop e ! 0) qt)]\<rparr>
  | qt. qt \<in> Q}"

definition F_SDPDA_TO_CFG_STD__edges_l3_pop :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l3_pop e \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e) (edge_pop e ! 0) (edge_trg e),
    prod_rhs =
      []\<rparr>}"

definition F_SDPDA_TO_CFG_STD__edges_l3_push :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'state set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l3_push e Q \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e) (edge_pop e ! 0) qt,
    prod_rhs =
      [teA (cons_l3   (edge_trg e) (edge_push e ! 0) qs)]
      @ [teA (cons_l3   qs (edge_pop e ! 0) qt)]\<rparr>
  | qs qt. qs \<in> Q \<and> qt \<in> Q}"

definition F_SDPDA_TO_CFG_STD__edges_l3 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l3 G \<equiv>
  \<Union> ((\<lambda>e.
    case edge_event e of
    None \<Rightarrow> {}
    | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_read e (epda_states G))
    ` epda_delta G)
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    a # y \<Rightarrow> {}
    | [] \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_pop e)
    ` epda_delta G)
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    [] \<Rightarrow> {}
    | a # y \<Rightarrow> (case edge_event e
                of Some A \<Rightarrow> {}
                | None \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l3_push e (epda_states G)))
    ` epda_delta G)"

definition F_SDPDA_TO_CFG_STD__edges_l2_read :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l2_read e \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 (edge_src e) (edge_pop e ! 0),
  prod_rhs =
      [teB (the (edge_event e))] @
      [teA (cons_l2   (edge_trg e) (edge_pop e ! 0))]\<rparr>}"

definition F_SDPDA_TO_CFG_STD__edges_l2_final :: "
  'state set
  \<Rightarrow> 'stack set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l2_final F S \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 i A,
  prod_rhs =
      []\<rparr>
  | i A. i \<in> F \<and> A \<in> S}"

definition F_SDPDA_TO_CFG_STD__edges_l2_push :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'state set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l2_push e Q \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 (edge_src e) (edge_pop e ! 0),
  prod_rhs =
      [teA (cons_l2   (edge_trg e) (edge_push e ! 0))]\<rparr>}
  \<union> {\<lparr>prod_lhs =
          cons_l2 (edge_src e) (edge_pop e ! 0),
      prod_rhs =
          [teA (cons_l3   (edge_trg e) (edge_push e ! 0) qs)]
          @ [teA (cons_l2   qs (edge_pop e ! 0))]\<rparr>
  | qs. qs \<in> Q}"

definition F_SDPDA_TO_CFG_STD__edges_l2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_STD__edges_l2 G \<equiv>
  \<Union> ((\<lambda>e.
    case edge_event e of
    None \<Rightarrow> {}
    | Some A \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l2_read e)
    ` epda_delta G)
  \<union> F_SDPDA_TO_CFG_STD__edges_l2_final (epda_marking G) (epda_gamma G)
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    [] \<Rightarrow> {}
    | a # y \<Rightarrow> (case edge_event e of
                Some A \<Rightarrow> {}
                | None \<Rightarrow> F_SDPDA_TO_CFG_STD__edges_l2_push e (epda_states G)))
    ` epda_delta G)"

definition F_SDPDA_TO_CFG_STD :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg"
  where
    "F_SDPDA_TO_CFG_STD G \<equiv>
  \<lparr>cfg_nonterminals =
    {cons_l2 q A | q A.
          q \<in> epda_states G
          \<and> A \<in> epda_gamma G}
    \<union> {cons_l3 q1 A q2 | q1 A q2.
          q1 \<in> epda_states G
          \<and> q2 \<in> epda_states G
          \<and> A \<in> epda_gamma G},
  cfg_events = epda_events G,
  cfg_initial = cons_l2 (epda_initial G) (epda_box G),
  cfg_productions = F_SDPDA_TO_CFG_STD__edges_l3 G \<union> F_SDPDA_TO_CFG_STD__edges_l2 G\<rparr>"

end
