section {*T03\_06\_03\_CFG\_ENFORCE\_NONBLOCKINGNESS*}
theory
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS

imports
  PRJ_12_01__PRE

begin

definition F_CFG_EB__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_EB__fp_one G N \<equiv>
  N
  \<union> {A | A p.
    p \<in> cfg_productions G
    \<and> prod_lhs p = A
    \<and> setA (prod_rhs p) \<subseteq> N}"

function (domintros) F_CFG_EB__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_EB__fp G N =
  (if F_CFG_EB__fp_one G N = N
  then N
  else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
   apply(rename_tac P x)(*strict*)
   apply(auto)
  done

definition F_CFG_EB :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg option"
  where
    "F_CFG_EB G \<equiv>
  let
    N = F_CFG_EB__fp G {}
  in
    if cfg_initial G \<in> F_CFG_EB__fp G {}
    then Some
        \<lparr>cfg_nonterminals = F_CFG_EB__fp G {},
        cfg_events = cfg_events G,
        cfg_initial = cfg_initial G,
        cfg_productions =
            {p \<in> cfg_productions G.
            setA (teA (prod_lhs p) # prod_rhs p) \<subseteq> F_CFG_EB__fp G {}}\<rparr>
    else None"

end
