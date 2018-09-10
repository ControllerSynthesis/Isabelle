section {*T03\_06\_05\_CFG\_TRIM*}
theory
  T03_06_05_CFG_TRIM

imports
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS
  T03_06_04_CFG_ENFORCE_ACCESSIBILITY

begin

definition F_CFG_TRIM :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg option"
  where
    "F_CFG_TRIM G \<equiv>
   case F_CFG_EB G of
     None \<Rightarrow> None
     | Some G' \<Rightarrow> Some (F_CFG_EASTD G')"

end

