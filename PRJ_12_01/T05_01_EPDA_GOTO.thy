section {*T05\_01\_EPDA\_GOTO*}
theory
  T05_01_EPDA_GOTO

imports
  PRJ_12_01__PRE

begin

definition F_EPDA_GOTO :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'event
  \<Rightarrow> 'state set"
  where
    "F_EPDA_GOTO G q X \<equiv>
  {q'. \<lparr>edge_src = q,
        edge_event = Some X,
        edge_pop = [epda_box G],
        edge_push = [epda_box G],
        edge_trg = q'\<rparr>
        \<in> epda_delta G}"

primrec F_EPDA_GOTO_SEQUENCE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'event list
  \<Rightarrow> 'state list set"
  where
    "F_EPDA_GOTO_SEQUENCE G q [] =
      {[]}"
  | "F_EPDA_GOTO_SEQUENCE G q (X # w) =
      {p # p_seq | p p_seq.
          p \<in> F_EPDA_GOTO G q X
          \<and> p_seq \<in> F_EPDA_GOTO_SEQUENCE G p w}"

definition F_DFA_GOTO :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'event
  \<Rightarrow> 'state"
  where
    "F_DFA_GOTO G q X \<equiv>
  THE_default q (\<lambda>x. x \<in> F_EPDA_GOTO G q X)"

definition F_DFA_GOTO_SEQUENCE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'state
  \<Rightarrow> 'event list
  \<Rightarrow> 'state list"
  where
    "F_DFA_GOTO_SEQUENCE G q w \<equiv>
  THE_default [] (\<lambda>x. x \<in> F_EPDA_GOTO_SEQUENCE G q w)"

end
