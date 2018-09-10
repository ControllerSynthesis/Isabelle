section {*Algorithm\_Definition\_\_Enforce\_Nonblockingness*}
theory
  Algorithm_Definition__Enforce_Nonblockingness

imports
  T01_FRESH
  T02_01_EPDA_TYPE_CONVERSION
  T02_02_PARSER_TYPE_CONVERSION
  T02_03_CFG_TYPE_CONVERSION
  T03_01_EPDA_RESTRICT
  T03_02_EPDA_APPROXIMATE_INITIAL_ACCESSIBLE
  T03_03_EPDA_APPROXIMATE_ACCESSIBLE
  T03_04_01_DPDA_SEPERATE_EXECUTING_EDGES
  T03_04_02_DPDA_REMOVE_NEUTRAL_EDGES
  T03_04_03_DPDA_SEPERATE_PUSH_POP_EDGES
  T03_04_04_DPDA_REMOVE_MASS_PUSHING_EDGES
  T03_04_05_DPDA_TO_SDPDA
  T03_05_SDPDA_ENFORCE_UNIQUE_MARKING_EARLY
  T03_06_01_SDPDA_TO_CFG_STD
  T03_06_02_SDPDA_TO_CFG_OPT
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS
  T03_06_04_CFG_ENFORCE_ACCESSIBILITY
  T03_06_05_CFG_TRIM
  T03_06_07_SDPDA_TO_LR1_STD
  T03_06_08_SDPDA_TO_LR1_OPT
  T04_CFG_FIRST
  T05_01_EPDA_GOTO
  T05_02_CFG_AUGMENT
  T05_03_VALID_ITEM_SETS
  T05_04_LR_MACHINE
  T05_05_LR_PARSER
  T05_06_PARSER_REMOVE_INPUT_TERMINATOR_USAGE
  T05_07_PARSER_REMOVE_TOP_RULES
  T06_01_PARSER_TO_EDPDA
  T06_02_01_EDPDA_REMOVE_NIL_POPPING_EDGES
  T06_02_02_EDPDA_REMOVE_MASS_POPPING_EDGES
  T06_02_03_EDPDA_TO_DPDA
  T07_01_DPDA_DETERMINE_ACCEESSIBLE_EDGES
  T07_02_DPDA_ENFORCE_ACCESSIBLE_STD
  T07_03_DPDA_DETERMINE_REQUIRED_EDGES
  T07_04_DPDA_ENFORCE_ACCESSIBLE_OPT

begin

definition F_DPDA_EB_STD :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option"
  where
    "F_DPDA_EB_STD G0 \<equiv>
  let
    G1 = F_DPDA_TO_SDPDA G0;
    G2 = F_SDPDA_EUME G1;
    G3 = F_SDPDA_TO_LR1_STD G2
  in
    case G3 of
    None \<Rightarrow> None
    | Some G3 \<Rightarrow>
      let
        G = F_CFG_TC G3;
        Do = F_FRESH (cfg_events G);
        S' = F_FRESH (cfg_nonterminals G);
        G' = F_CFG_AUGMENT G S' Do;
        M = F_LR_MACHINE G' F_CFG_FIRST (Suc 0);
        P0 = F_LR_PARSER G G' M Do;
        P1 = F_PARSER_RITU P0;
        P2 = F_PARSER_RTR P1;
        P2' = (F_PARSER_TC P2)::('state DT_symbol, 'event DT_symbol, nat option) parser;
        E1 = F_PARSER_TO_EDPDA P2' (F_FRESH (parser_nonterms P2'));
        E2 = F_EDPDA_TO_DPDA E1;
        E3 = F_DPDA_EA_STD E2
      in
        Some (F_EPDA_TC E3)"

definition F_DPDA_EB_OPT :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option"
  where
    "F_DPDA_EB_OPT G0 \<equiv>
  let
    G1 = F_DPDA_TO_SDPDA G0;
    G2 = F_SDPDA_EUME G1;
    G3 = F_SDPDA_TO_LR1_OPT G2 (Suc 0)
  in
    case G3 of
    None \<Rightarrow> None
    | Some G3 \<Rightarrow>
      let
        G = F_CFG_TC G3;
        Do = F_FRESH (cfg_events G);
        S' = F_FRESH (cfg_nonterminals G);
        G' = F_CFG_AUGMENT G S' Do;
        M = F_LR_MACHINE G' F_CFG_FIRST (Suc 0);
        P0 = F_LR_PARSER G G' M Do;
        P1 = F_PARSER_RITU P0;
        P2 = F_PARSER_RTR P1;
        P2' = (F_PARSER_TC P2)::('state DT_symbol, 'event DT_symbol, nat option) parser;
        E1 = F_PARSER_TO_EDPDA P2' (F_FRESH (parser_nonterms P2'));
        E2 = F_EDPDA_TO_DPDA E1;
        E3 = F_DPDA_EA_OPT E2
      in
        Some (F_EPDA_TC E3)"

end

