section {*T03\_06\_02\_SDPDA\_TO\_CFG\_OPT*}
theory
  T03_06_02_SDPDA_TO_CFG_OPT

imports
  T03_06_01_SDPDA_TO_CFG_STD

begin

definition F_SDPDA_TO_CFG_OPT__pushed_symbols :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack set"
  where
    "F_SDPDA_TO_CFG_OPT__pushed_symbols G \<equiv>
  {x | x y e.
  e \<in> epda_delta G
  \<and> edge_event e = None
  \<and> edge_pop e = [y]
  \<and> edge_push e = [x, y]}"

definition F_SDPDA_TO_CFG_OPT__push_target_state :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack
  \<Rightarrow> 'state set"
  where
    "F_SDPDA_TO_CFG_OPT__push_target_state G x \<equiv>
  {edge_trg e | y e.
  e \<in> epda_delta G
  \<and> edge_event e = None
  \<and> edge_pop e = [y]
  \<and> edge_push e = [x, y]}"

definition F_SDPDA_TO_CFG_OPT__step_closure__l3_init :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__l3_init G x R \<equiv>
  {cons_tuple2 None (Some (cons_tuple3 q (x # w) (Some (Suc 0)))) | q w.
  cons_tuple2 q (x # w) \<in> R
  \<and> q \<in> F_SDPDA_TO_CFG_OPT__push_target_state G x}"

(*G is not required here but for F_SDPDA_TO_CFG_OPT__step_closure__l3_init it is required
and they are used assuming the same inputs *)
definition F_SDPDA_TO_CFG_OPT__step_closure__l2_init :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__l2_init G x R \<equiv>
  {cons_tuple2 None (Some(cons_tuple3 q v (Some (Suc 0)))) | q w v.
  cons_tuple2 q w \<in> R
  \<and> ((prefix [x] w \<and> v = w) \<or> (w = [] \<and> v = [x]))}"

definition F_SDPDA_TO_CFG_OPT__step_closure__read__exists__greater_than_0 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__read__exists__greater_than_0 G S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q r X w q' n.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = Some r,
      edge_pop = [X],
      edge_push = [X],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> n \<noteq> Some 0
  \<and> y = cons_tuple3 q (X # w) n
  \<and> z = cons_tuple3 q' (X # w) n}"

definition F_SDPDA_TO_CFG_OPT__step_closure__read__not_exists__none :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__read__not_exists__none G S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q r X q'.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = Some r,
      edge_pop = [X],
      edge_push = [X],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q [] None
  \<and> z = cons_tuple3 q' [X] None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__none :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__none G S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X w.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [X],
      edge_push = [],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q (X # w) None
  \<and> z = cons_tuple3 q' w None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__pop__not_exists__none :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__pop__not_exists__none G S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [X],
      edge_push = [],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q [] None
  \<and> z = cons_tuple3 q' [] None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__greater_than_0 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__greater_than_0 G S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X w n.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [X],
      edge_push = [],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q (X # w) (Some (Suc n))
  \<and> z = cons_tuple3 q' w (Some n)}"

definition F_SDPDA_TO_CFG_OPT__step_closure__push__exists__none :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__push__exists__none G k S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X Y w.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [Y],
      edge_push = [X, Y],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q (Y # w) None
  \<and> z = cons_tuple3 q' (take k (X # Y # w)) None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__push__not_exists__none :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__push__not_exists__none G k S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X Y.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [Y],
      edge_push = [X, Y],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q [] None
  \<and> z = cons_tuple3 q' (take k [X, Y]) None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__push__exists__less_than_k :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__push__exists__less_than_k G k S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X Y w n.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [Y],
      edge_push = [X, Y],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q (Y # w) (Some (Suc n))
  \<and> Suc (Suc n) \<le> k
  \<and> z = cons_tuple3 q' (take k (X # Y # w)) (Some (Suc (Suc n)))}"

definition F_SDPDA_TO_CFG_OPT__step_closure__push__exists__k :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__push__exists__k G k S \<equiv>
  {cons_tuple2 (Some y) (Some z)| x y z q q' X Y w n.
  cons_tuple2 x (Some y) \<in> S
  \<and> \<lparr>edge_src = q,
      edge_event = None,
      edge_pop = [Y],
      edge_push = [X, Y],
      edge_trg = q'\<rparr> \<in> epda_delta G
  \<and> y = cons_tuple3 q (Y # w) (Some (Suc n))
  \<and> Suc n = k
  \<and> z = cons_tuple3 q' (take k (X # Y # w)) None}"

definition F_SDPDA_TO_CFG_OPT__step_closure__fp_one :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__fp_one G S k \<equiv>
  S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__read__exists__greater_than_0 G S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__read__not_exists__none G S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__greater_than_0 G S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__pop__exists__none G S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__pop__not_exists__none G S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__push__exists__none G k S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__push__not_exists__none G k S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__push__exists__less_than_k G k S
  \<union> F_SDPDA_TO_CFG_OPT__step_closure__push__exists__k G k S"

function (domintros) F_SDPDA_TO_CFG_OPT__step_closure__fp :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph"
  where
    "F_SDPDA_TO_CFG_OPT__step_closure__fp G S k =
  (let
    S' = F_SDPDA_TO_CFG_OPT__step_closure__fp_one G S k
  in
    if S = S'
    then S
    else F_SDPDA_TO_CFG_OPT__step_closure__fp G S' k)"
   apply(rename_tac P x)(*strict*)
   apply(force)
  apply(rename_tac G S k Ga Sa ka)(*strict*)
  apply(force)
  done

definition F_SDPDA_TO_CFG_OPT__l3_approx_1 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> 'stack
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set"
  where
    "F_SDPDA_TO_CFG_OPT__l3_approx_1 G k x R CL \<equiv>
  {cons_l3 q A q' | q A q' SE w n w' n'.
  cons_tuple2 None SE \<in> F_SDPDA_TO_CFG_OPT__step_closure__l3_init G x R
  \<and> cons_tuple2 SE (Some (cons_tuple3 q w n)) \<in> CL
  \<and> cons_tuple2 (Some (cons_tuple3 q w n)) (Some (cons_tuple3 q' w' n')) \<in> CL
  \<and> A \<in> epda_gamma G
  \<and> (w = [] \<or> prefix [A] w)
  \<and> n' \<in> {Some 0, None}}"

definition F_SDPDA_TO_CFG_OPT__l3_approx :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('stack \<Rightarrow> ('state, 'stack) DT_accessibility_graph)
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set"
  where
    "F_SDPDA_TO_CFG_OPT__l3_approx G k R CL \<equiv>
  \<Union> {F_SDPDA_TO_CFG_OPT__l3_approx_1 G k x R (CL x)
      | x.
      x \<in> F_SDPDA_TO_CFG_OPT__pushed_symbols G}"

definition F_SDPDA_TO_CFG_OPT__l2_approx_1 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> 'stack
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack) DT_accessibility_graph
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set"
  where
    "F_SDPDA_TO_CFG_OPT__l2_approx_1 G k A R CL \<equiv>
  {cons_l2 q A | q w n q' w' n'.
  cons_tuple2 (Some (cons_tuple3 q w n)) (Some (cons_tuple3 q' w' n')) \<in> CL
  \<and> cons_tuple2 None (Some (cons_tuple3 q w n)) \<in> F_SDPDA_TO_CFG_OPT__step_closure__l2_init G A R
  \<and> q' \<in> epda_marking G
  \<and> n' \<noteq> Some 0}"

definition F_SDPDA_TO_CFG_OPT__l2_approx :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('stack \<Rightarrow> ('state, 'stack) DT_accessibility_graph)
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set"
  where
    "F_SDPDA_TO_CFG_OPT__l2_approx G k R CL \<equiv>
  \<Union> {F_SDPDA_TO_CFG_OPT__l2_approx_1 G k A R (CL A)
      | A.
      A \<in> F_SDPDA_TO_CFG_OPT__pushed_symbols G \<union> {epda_box G}}"

definition F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp_one :: "
  'a DT_graph
  \<Rightarrow> 'a DT_graph"
  where
    "F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp_one S \<equiv>
  S
  \<union> {cons_tuple2 x x | x y. cons_tuple2 x y \<in> S}
  \<union> {cons_tuple2 y y | x y. cons_tuple2 x y \<in> S}
  \<union> {cons_tuple2 x z | x y z. cons_tuple2 x y \<in> S \<and> cons_tuple2 y z \<in> S}"

function (domintros) F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp :: "
  'a DT_graph
  \<Rightarrow> 'a DT_graph"
  where
    "F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp S =
  (let
    S' = F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp_one S
  in
    if S' = S
    then S
    else F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp S')"
   apply(rename_tac P x)(*strict*)
   apply(force)
  apply(rename_tac S Sa)(*strict*)
  apply(force)
  done

definition F_SDPDA_TO_CFG_OPT__nonterminals :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals set, ('state, 'stack) DT_l2_l3_nonterminals set) DT_tuple2"
  where
    "F_SDPDA_TO_CFG_OPT__nonterminals G k \<equiv>
  let
     R = F_EPDA_AIA G k;
     CL = \<lambda>INIT x. F_SDPDA_TO_CFG_OPT__transitive_reflexive_closure__fp (F_SDPDA_TO_CFG_OPT__step_closure__fp G (INIT G x R) k)
  in
    cons_tuple2
      (F_SDPDA_TO_CFG_OPT__l2_approx G k R (CL F_SDPDA_TO_CFG_OPT__step_closure__l2_init))
      (F_SDPDA_TO_CFG_OPT__l3_approx G k R (CL F_SDPDA_TO_CFG_OPT__step_closure__l3_init))"

definition F_SDPDA_TO_CFG_OPT__edges_l3_read :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l3_read e S3 \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e) (edge_pop e ! 0) qt,
    prod_rhs =
      [teB (the (edge_event e))]
    @ [teA (cons_l3 (edge_trg e) (edge_pop e ! 0) qt)]\<rparr>
  | qt.
  cons_l3 (edge_src e) (edge_pop e ! 0) qt \<in> S3
  \<and> cons_l3 (edge_trg e) (edge_pop e ! 0) qt \<in> S3}"

definition F_SDPDA_TO_CFG_OPT__edges_l3_pop :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l3_pop e S3 \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e1) (edge_pop e1 ! 0) (edge_trg e1),
    prod_rhs =
      []\<rparr>
  | e1.
  e1 = e
  \<and> cons_l3 (edge_src e) (edge_pop e ! 0) (edge_trg e) \<in> S3}"

definition F_SDPDA_TO_CFG_OPT__edges_l3_push :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l3_push e S3 \<equiv>
  {\<lparr>prod_lhs =
      cons_l3 (edge_src e) (edge_pop e ! 0) qt,
    prod_rhs =
      [teA (cons_l3 (edge_trg e) (edge_push e ! 0) qs)]
      @ [teA (cons_l3 qs (edge_pop e ! 0) qt)]\<rparr>
  | qs qt.
  cons_l3 (edge_src e) (edge_pop e ! 0) qt \<in> S3
  \<and> cons_l3 (edge_trg e) (edge_push e ! 0) qs \<in> S3
  \<and> cons_l3 qs (edge_pop e ! 0) qt \<in> S3}"

definition F_SDPDA_TO_CFG_OPT__edges_l3 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l3 G S3 \<equiv>
  \<Union> ((\<lambda>e.
    case edge_event e of
    None \<Rightarrow> {}
    | Some A \<Rightarrow> F_SDPDA_TO_CFG_OPT__edges_l3_read e S3)
    ` epda_delta G)
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    a # y \<Rightarrow> {}
    | [] \<Rightarrow> F_SDPDA_TO_CFG_OPT__edges_l3_pop e S3)
    ` epda_delta G)
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    [] \<Rightarrow> {}
    | a # y \<Rightarrow> (case edge_event e
                of Some A \<Rightarrow> {}
                | None \<Rightarrow> F_SDPDA_TO_CFG_OPT__edges_l3_push e S3))
    ` epda_delta G)"

definition F_SDPDA_TO_CFG_OPT__edges_l2_read :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l2_read e S2 \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 (edge_src e) (edge_pop e ! 0),
  prod_rhs =
      [teB (the (edge_event e))] @
      [teA (cons_l2   (edge_trg e) (edge_pop e ! 0))]\<rparr>
  | e1.
  e1 = e
  \<and> cons_l2 (edge_src e) (edge_pop e ! 0) \<in> S2
  \<and> cons_l2 (edge_trg e) (edge_pop e ! 0) \<in> S2}"

definition F_SDPDA_TO_CFG_OPT__edges_l2_final :: "
  'state set
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l2_final F S2 \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 i A,
  prod_rhs =
      []\<rparr>
  | i A.
  i \<in> F
  \<and> cons_l2 i A \<in> S2}"

definition F_SDPDA_TO_CFG_OPT__edges_l2_push :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l2_push e S2 S3 \<equiv>
  {\<lparr>prod_lhs =
      cons_l2 (edge_src e1) (edge_pop e1 ! 0),
  prod_rhs =
      [teA (cons_l2   (edge_trg e1) (edge_push e1 ! 0))]\<rparr>
  | e1. e1=e
  \<and> cons_l2 (edge_src e) (edge_pop e ! 0) \<in> S2
  \<and> cons_l2 (edge_trg e) (edge_push e ! 0) \<in> S2}
  \<union> {\<lparr>prod_lhs =
          cons_l2 (edge_src e) (edge_pop e ! 0),
      prod_rhs =
          [teA (cons_l3   (edge_trg e) (edge_push e ! 0) qs)]
          @ [teA (cons_l2   qs (edge_pop e ! 0))]\<rparr>
  | qs.
  cons_l2 (edge_src e) (edge_pop e ! 0) \<in> S2
  \<and> cons_l3 (edge_trg e) (edge_push e ! 0) qs \<in> S3
  \<and> cons_l2 qs (edge_pop e ! 0) \<in> S2}"

definition F_SDPDA_TO_CFG_OPT__edges_l2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> ('state, 'stack) DT_l2_l3_nonterminals set
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set"
  where
    "F_SDPDA_TO_CFG_OPT__edges_l2 G S2 S3 \<equiv>
  \<Union> ((\<lambda>e.
    case edge_event e of
    None \<Rightarrow> {}
    | Some A \<Rightarrow> F_SDPDA_TO_CFG_OPT__edges_l2_read e S2)
    ` epda_delta G)
  \<union> F_SDPDA_TO_CFG_OPT__edges_l2_final (epda_marking G) S2
  \<union> \<Union> ((\<lambda>e.
    case edge_push e of
    [] \<Rightarrow> {}
    | a # y \<Rightarrow> (case edge_event e of
                Some A \<Rightarrow> {}
                | None \<Rightarrow> F_SDPDA_TO_CFG_OPT__edges_l2_push e S2 S3))
    ` epda_delta G)"

definition F_SDPDA_TO_CFG_OPT :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg option"
  where
    "F_SDPDA_TO_CFG_OPT G k \<equiv>
  let
      X = F_SDPDA_TO_CFG_OPT__nonterminals G k;
      S2 = case X of cons_tuple2 S2 S3 \<Rightarrow> S2;
      S3 = case X of cons_tuple2 S2 S3 \<Rightarrow> S3
  in
  if cons_l2 (epda_initial G) (epda_box G) \<in> S2
  then Some
        \<lparr>cfg_nonterminals = S2 \<union> S3,
        cfg_events = epda_events G,
        cfg_initial = cons_l2 (epda_initial G) (epda_box G),
        cfg_productions =
          F_SDPDA_TO_CFG_OPT__edges_l3 G S3
          \<union> F_SDPDA_TO_CFG_OPT__edges_l2 G S2 S3\<rparr>
  else None"

end
