section {*T03\_03\_EPDA\_APPROXIMATE\_ACCESSIBLE*}
theory
  T03_03_EPDA_APPROXIMATE_ACCESSIBLE

imports
  T03_01_EPDA_RESTRICT
  T03_02_EPDA_APPROXIMATE_INITIAL_ACCESSIBLE

begin

definition F_EPDA_AA :: "
  ('states, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('states, 'event, 'stack) epda"
  where
    "F_EPDA_AA G k \<equiv>
  F_EPDA_R
    G
    {q | q s. cons_tuple2 q s \<in> F_EPDA_AIA G k}
    {e | q s e. cons_tuple2 q s \<in> F_EPDA_AIA G k
        \<and> e \<in> epda_delta G
        \<and> edge_src e = q
        \<and> (prefix (edge_pop e) s \<or> prefix s (edge_pop e))}"

end

