section {*Algorithm\_Definition\_\_Enforce\_Controllable*}
theory
  Algorithm_Definition__Enforce_Controllable

imports
  PRJ_13_01__ENTRY
  T03_DPDA_OBSERVE_TOP_STACK
  T04_DPDA_ENFORCE_UNIQUE_MARKING_LATE
  T07_DPDA_RESTRICT_TO_CONTROLLABLE_STATES

begin

definition F_DPDA_EC :: "
  ('stateA DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('stateB DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> (('stateA DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option) \<times> bool"
  where
    "F_DPDA_EC G0 P \<Sigma>UC \<equiv>
  let
    M0 = F_DPDA_DFA_PRODUCT G0 P;
    M1 = F_DPDA_OTS M0;
    M2 = F_DPDA_EUML M1;
    M3 = F_DPDA_EA_OPT M2
  in
    case F_DPDA_RCS M3 P \<Sigma>UC of
    (None, x) \<Rightarrow> (None, x)
    | (Some M, False) \<Rightarrow> (Some (F_EPDA_TC M), False)
    | (Some M, True) \<Rightarrow> (Some G0, True)"

end

