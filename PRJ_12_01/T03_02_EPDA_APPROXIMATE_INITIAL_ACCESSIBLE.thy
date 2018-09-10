section {*T03\_02\_EPDA\_APPROXIMATE\_INITIAL\_ACCESSIBLE*}
theory
  T03_02_EPDA_APPROXIMATE_INITIAL_ACCESSIBLE

imports
  PRJ_12_01__PRE

begin

definition F_EPDA_AIA__fp_start :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2"
  where
    "F_EPDA_AIA__fp_start G k \<equiv>
  cons_tuple2 (epda_initial G) (take k [epda_box G])"

definition F_EPDA_AIA__fp_one :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set"
  where
    "F_EPDA_AIA__fp_one G k E \<equiv>
  E \<union>
  {cons_tuple2 q2 s2 | q1 s1 q2 s2 x w1 w2.
   cons_tuple2 q1 s1 \<in> E
   \<and> \<lparr>edge_src = q1,
      edge_event = x,
      edge_pop = w1,
      edge_push = w2,
      edge_trg = q2\<rparr> \<in> epda_delta G
   \<and> (prefix w1 s1 \<or> prefix s1 w1)
   \<and> s2 = take k (w2 @ drop (length w1) s1)}"

function (domintros) F_EPDA_AIA__fp :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set"
  where
    "F_EPDA_AIA__fp G k E =
  (if F_EPDA_AIA__fp_one G k E = E
  then E
  else F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k E))"
   apply(rename_tac P x)(*strict*)
   apply(force)
  apply(rename_tac G k E Ga ka Ea)(*strict*)
  apply(force)
  done

definition F_EPDA_AIA :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set"
  where
    "F_EPDA_AIA G k \<equiv>
  F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}"

end
