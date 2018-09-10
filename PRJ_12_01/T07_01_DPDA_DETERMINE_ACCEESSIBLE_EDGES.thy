section {*T07\_01\_DPDA\_DETERMINE\_ACCEESSIBLE\_EDGES*}
theory
  T07_01_DPDA_DETERMINE_ACCEESSIBLE_EDGES

imports
  T01_FRESH
  T03_06_08_SDPDA_TO_LR1_OPT
  T03_04_04_DPDA_REMOVE_MASS_PUSHING_EDGES
  T03_04_01_DPDA_SEPERATE_EXECUTING_EDGES
  T03_04_02_DPDA_REMOVE_NEUTRAL_EDGES
  T03_04_03_DPDA_SEPERATE_PUSH_POP_EDGES
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS

begin

definition F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p \<equiv>
  {e \<in> epda_delta G.
    (p \<in> F_SDPDA_TO_CFG_STD__edges_l3_read e (epda_states G) \<and> (edge_event e \<noteq> None))
  \<or> (p \<in> F_SDPDA_TO_CFG_STD__edges_l3_pop e \<and> edge_push e = [])
  \<or> (p \<in> F_SDPDA_TO_CFG_STD__edges_l3_push e (epda_states G) \<and> edge_push e \<noteq> [] \<and> (edge_event e = None))
  \<or> (p \<in> F_SDPDA_TO_CFG_STD__edges_l2_read e \<and> (edge_event e \<noteq> None))
  \<or> (p \<in> F_SDPDA_TO_CFG_STD__edges_l2_push e (epda_states G) \<and> edge_push e \<noteq> [] \<and> (edge_event e = None))}"

definition F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack) DT_l2_l3_nonterminals, 'event) cfg_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G X \<equiv>
  \<Union> ((\<lambda>p. F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD_1 G p) ` X)"

definition F_DPDA_DRE__revert_F_DPDA_RMPUE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge_nat, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_DPDA_RMPUE G X \<equiv>
  {e \<in> epda_delta G.
    \<exists>p \<in> X.
      p \<in> F_DPDA_RMPUE__edge_then e
      \<or> p = F_DPDA_RMPUE__edge_else e}"

definition F_DPDA_DRE__revert_F_DPDA_SPPE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_DPDA_SPPE G X \<equiv>
  {e \<in> epda_delta G.
    \<exists>p \<in> X.
      p \<in> F_DPDA_SPPE__edge_then e (epda_gamma G)
      \<or> p = F_DPDA_SPPE__edge_else e}"

definition F_DPDA_DRE__revert_F_DPDA_RNE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_DPDA_RNE G PB X \<equiv>
  {e \<in> epda_delta G.
    \<exists>p \<in> X.
      p \<in> F_DPDA_RNE__edge_then e PB
      \<or> p = F_DPDA_RNE__edge_else e}"

definition F_DPDA_DRE__revert_F_DPDA_SEE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'event, 'stack) DT_state_or_edge, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "F_DPDA_DRE__revert_F_DPDA_SEE G X \<equiv>
  {e \<in> epda_delta G.
    \<exists>p \<in> X.
      p \<in> F_DPDA_SEE__edge_then e
      \<or> p \<in> F_DPDA_SEE__edge_else e}"

definition F_CFG_APLM__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_APLM__fp_one G E N \<equiv>
  N \<union>
  {A | A p w1 w2.
    p \<in> cfg_productions G
    \<and> prod_lhs p \<in> N
    \<and> prod_rhs p = w1 @ teA A # w2
    \<and> setA w1 \<subseteq> E}"

function (domintros) F_CFG_APLM__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_APLM__fp G E N =
  (if F_CFG_APLM__fp_one G E N = N
  then N
  else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
   apply(rename_tac P x)(*strict*)
   apply(auto)
  done

definition F_CFG_APLM :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label set"
  where
    "F_CFG_APLM G \<equiv>
  {p \<in> cfg_productions G.
    prod_lhs p \<in> F_CFG_APLM__fp G (F_CFG_EB__fp G {}) {cfg_initial G}}"

definition F_DPDA_DAE :: "
  ('state, 'event, 'stack DT_symbol) epda
  \<Rightarrow> ('state, 'event, 'stack DT_symbol) epda_step_label set"
  where
    "F_DPDA_DAE G0 \<equiv>
  let
    G1 = F_DPDA_SEE G0;
    PB = F_FRESH (epda_gamma G1);
    G2 = F_DPDA_RNE G1 PB;
    G3 = F_DPDA_SPPE G2;    
    G4 = F_DPDA_RMPUE G3;    
    G5 = F_SDPDA_TO_CFG_STD G4;    
    RE4 = F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD G4 (F_CFG_APLM G5);
    RE3 = F_DPDA_DRE__revert_F_DPDA_RMPUE G3 RE4;
    RE2 = F_DPDA_DRE__revert_F_DPDA_SPPE G2 RE3;
    RE1 = F_DPDA_DRE__revert_F_DPDA_RNE G1 PB RE2;
    RE0 = F_DPDA_DRE__revert_F_DPDA_SEE G0 RE1
  in
    RE0"

end

