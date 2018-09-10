section {*Algorithm\_Definition\_\_Construct\_Controller*}
theory
  Algorithm_Definition__Construct_Controller

imports
  PRJ_14_01__ENTRY

begin

definition F_DPDA_DFA_CC__fp_one :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option \<times> bool"
  where
    "F_DPDA_DFA_CC__fp_one C P \<Sigma>UC \<equiv>
  case F_DPDA_EC C P \<Sigma>UC of
    (None, x) \<Rightarrow> (None, False)
    | (Some C', True) \<Rightarrow> (Some C', False)
    | (Some C', False) \<Rightarrow> (F_DPDA_EB_OPT C', F_DPDA_EB_OPT C' \<noteq> None)"

function (domintros) FB_iterate :: "
  ('event \<Rightarrow> ('event option \<times> bool))
  \<Rightarrow> 'event
  \<Rightarrow> 'event option"
  where
    "FB_iterate F A =
  (case F A of
    (None, x) \<Rightarrow> None
    | (Some A', True) \<Rightarrow> FB_iterate F A'
    | (Some A', False) \<Rightarrow> Some A')"
   apply(rename_tac P x)(*strict*)
   apply(force)+
  done

definition F_DPDA_DFA_CC__fp :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option"
  where
    "F_DPDA_DFA_CC__fp C P \<Sigma>UC \<equiv>
  FB_iterate (\<lambda>X. F_DPDA_DFA_CC__fp_one X P \<Sigma>UC) C"

definition F_DPDA_DFA_CC__fp_start :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option"
  where
    "F_DPDA_DFA_CC__fp_start S P \<equiv>
  F_DPDA_EB_OPT (F_EPDA_TC (F_DPDA_DFA_PRODUCT S P))"

definition F_DPDA_DFA_CC :: "
  ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, nat) epda
  \<Rightarrow> 'event DT_symbol set
  \<Rightarrow> ('state DT_symbol, 'event DT_symbol, 'stack DT_symbol) epda option"
  where
    "F_DPDA_DFA_CC S P \<Sigma>UC \<equiv>
  case F_DPDA_DFA_CC__fp_start S P of
    None \<Rightarrow> None
    | Some C \<Rightarrow> F_DPDA_DFA_CC__fp C P \<Sigma>UC"

end

