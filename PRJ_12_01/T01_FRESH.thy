section {*T01\_FRESH*}
theory
  T01_FRESH

imports
  PRJ_12_01__PRE

begin

declare [[ hypsubst_thin = false ]]
datatype 'a DT_symbol =
  cons_symbol_nat "nat"
  | cons_symbol_base "'a"
declare [[ hypsubst_thin = true ]]

function (domintros) F_FRESH__recursive :: "
  'a DT_symbol set
  \<Rightarrow> nat
  \<Rightarrow> 'a DT_symbol"
  where
    "F_FRESH__recursive Q n =
  (if cons_symbol_nat n \<notin> Q
  then cons_symbol_nat n
  else F_FRESH__recursive Q (Suc n))"
   apply(rename_tac P x)(*strict*)
   apply(auto)
  done

definition F_FRESH :: "
  'a DT_symbol set
  \<Rightarrow> 'a DT_symbol"
  where
    "F_FRESH Q \<equiv>
  F_FRESH__recursive Q 0"

end
