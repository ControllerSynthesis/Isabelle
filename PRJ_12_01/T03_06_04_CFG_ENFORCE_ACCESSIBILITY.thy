section {*T03\_06\_04\_CFG\_ENFORCE\_ACCESSIBILITY*}
theory
  T03_06_04_CFG_ENFORCE_ACCESSIBILITY

imports
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS

begin

definition F_CFG_EASTD__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_EASTD__fp_one G N \<equiv>
   N \<union>
   {A | A p.
   p \<in> cfg_productions G
   \<and> prod_lhs p \<in> N
   \<and> A \<in> setA (prod_rhs p)}"

function (domintros) F_CFG_EASTD__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set"
  where
    "F_CFG_EASTD__fp G N =
  (if F_CFG_EASTD__fp_one G N = N
  then N
  else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
   apply(rename_tac P x)(*strict*)
   apply(auto)
  done

definition F_CFG_EASTD :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg"
  where
    "F_CFG_EASTD G \<equiv>
  let
    N = F_CFG_EASTD__fp G {cfg_initial G}
  in
    \<lparr>cfg_nonterminals = N,
    cfg_events = cfg_events G,
    cfg_initial = cfg_initial G,
    cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> N}\<rparr>"

end
