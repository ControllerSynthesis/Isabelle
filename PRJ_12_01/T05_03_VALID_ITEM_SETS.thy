section {*T05\_03\_VALID\_ITEM\_SETS*}
theory
  T05_03_VALID_ITEM_SETS

imports
  T04_CFG_FIRST

begin

record ('nonterminal, 'event) DT_cfg_item =
  cfg_item_lhs :: "'nonterminal"
  cfg_item_rhs1 :: "('nonterminal, 'event) DT_two_elements list"
  cfg_item_rhs2 :: "('nonterminal, 'event) DT_two_elements list"
  cfg_item_look_ahead :: "'event list"

definition F_VALID_ITEM_SET_GOTO__descent__fp_one_1 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I \<equiv>
  {\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = w, cfg_item_look_ahead = z\<rparr> | B w z \<beta>.
      \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<in> cfg_productions G
    \<and> cfg_item_rhs2 I = teA B # \<beta>
    \<and> z \<in> F G k (\<beta> @ liftB (cfg_item_look_ahead I))}
  \<union> {I}"

definition F_VALID_ITEM_SET_GOTO__descent__fp_one_1s :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S \<equiv>
  {I. \<exists>x \<in> S. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x}"

function (domintros) F_VALID_ITEM_SET_GOTO__descent__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp G F k S =
  (if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S
  then S
  else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
  by pat_completeness auto

definition F_VALID_ITEM_SET_GOTO__passes :: "
  ('nonterminal, 'event) DT_two_elements
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> bool"
  where
    "F_VALID_ITEM_SET_GOTO__passes X I1 I2 \<equiv>
  cfg_item_lhs I1 = cfg_item_lhs I2
  \<and> cfg_item_look_ahead I1 = cfg_item_look_ahead I2
  \<and> (\<exists>\<beta>.
      cfg_item_rhs2 I1 = X # \<beta>
      \<and> cfg_item_rhs1 I2 = cfg_item_rhs1 I1 @ [X]
      \<and> cfg_item_rhs2 I2 = \<beta>)"

definition F_VALID_ITEM_SET_GOTO__basis :: "
  ('nonterminal, 'event) DT_two_elements
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_GOTO__basis X S \<equiv>
  {I2. \<exists>I1 \<in> S. F_VALID_ITEM_SET_GOTO__passes X I1 I2}"

definition F_VALID_ITEM_SET_GOTO :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_GOTO G F k X S \<equiv>
  F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis X S)"

definition F_VALID_ITEM_SET_INITIAL__fp_start :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_INITIAL__fp_start G \<equiv>
  {\<lparr>cfg_item_lhs = cfg_initial G, cfg_item_rhs1 = [], cfg_item_rhs2 = prod_rhs p, cfg_item_look_ahead = []\<rparr> | p.
    p \<in> cfg_productions G
    \<and> prod_lhs p = cfg_initial G}"

definition F_VALID_ITEM_SET_INITIAL :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "F_VALID_ITEM_SET_INITIAL G F k \<equiv>
  F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)"

end
