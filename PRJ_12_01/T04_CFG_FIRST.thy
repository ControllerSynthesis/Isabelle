section {*T04\_CFG\_FIRST*}
theory
  T04_CFG_FIRST

imports
  T03_06_03_CFG_ENFORCE_NONBLOCKINGNESS

begin

type_synonym ('nonterminal, 'event) DT_first_function
  = "('nonterminal, 'event) cfg
    \<Rightarrow> nat
    \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
    \<Rightarrow> 'event list set"

definition F_CFG_FIRST__table_domain :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list set"
  where
    "F_CFG_FIRST__table_domain G \<equiv>
  {As | As e A. prod_lhs e = A \<and> [teA A] = As \<and> e \<in> cfg_productions G}
  \<union> {ws | ws e w. prod_rhs e = w \<and> e \<in> cfg_productions G \<and> ws \<in> suffixes w}"

definition F_CFG_FIRST__table__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_two_elements list \<Rightarrow> ('event option) set)
  \<Rightarrow> (('nonterminal, 'event) DT_two_elements list \<Rightarrow> ('event option) set)"
  where
    "F_CFG_FIRST__table__fp_one G f \<equiv>
  \<lambda>w.
  if w \<notin> F_CFG_FIRST__table_domain G
  then {}
  else
    f w \<union> (
    case w of
      [] \<Rightarrow> {None}
      | teA A # w' \<Rightarrow>
          f [teA A]
          - (if w' \<noteq> [] then {None} else {})
          \<union> (if None \<in> f [teA A] then f w' else {})
          \<union> ({b. \<exists>x. b \<in> f x \<and> \<lparr>prod_lhs = A, prod_rhs = x\<rparr> \<in> cfg_productions G}
              - (if w' \<noteq> [] then {None} else {}))
      | teB a # w' \<Rightarrow> {Some a})"

function (domintros) F_CFG_FIRST__table__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_two_elements list \<Rightarrow> ('event option) set)
  \<Rightarrow> (('nonterminal, 'event) DT_two_elements list \<Rightarrow> ('event option) set)"
  where
    "F_CFG_FIRST__table__fp G f =
   (if F_CFG_FIRST__table__fp_one G f = f
   then f
   else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
  by pat_completeness auto

definition F_CFG_FIRST__fp_one :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "F_CFG_FIRST__fp_one G w \<equiv>
  F_CFG_FIRST__table__fp G (\<lambda>x. {}) w"

function F_CFG_FIRST__fp :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "F_CFG_FIRST__fp G w =
  (case w of
  [] \<Rightarrow> {None}
  | teA A # w' \<Rightarrow>
    (F_CFG_FIRST__fp_one G [teA A] - {None})
    \<union> (if None \<in> F_CFG_FIRST__fp_one G [teA A] then F_CFG_FIRST__fp G w' else {})
  | teB b # w' \<Rightarrow> {Some b})"
  by pat_completeness auto
termination by lexicographic_order

primrec FB_first_teA :: "
  ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'nonterminal option"
  where
    "FB_first_teA [] =
      None"
  | "FB_first_teA (x # w) =
      (case x of teA A \<Rightarrow> Some A | teB x \<Rightarrow> FB_first_teA w)"

definition F_CFG_FIRST__input_valid :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "F_CFG_FIRST__input_valid G w \<equiv>
  if setA w \<subseteq> cfg_nonterminals G
  then F_CFG_FIRST__fp G w
  else {}"

definition F_CFG_FIRST__enforce_Nonblockingness :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "F_CFG_FIRST__enforce_Nonblockingness G w \<equiv>
  if setA w = {}
  then F_CFG_FIRST__fp G w
  else
    (case FB_first_teA w of
    None \<Rightarrow> {}
    | Some A \<Rightarrow>
        (case F_CFG_EB (G\<lparr>cfg_initial := A\<rparr>) of
          Some G' \<Rightarrow> F_CFG_FIRST__input_valid G' w
          | None \<Rightarrow> {}))"

definition F_CFG_FIRST :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event list set"
  where
    "F_CFG_FIRST G k w \<equiv>
  if k = 0
  then
    (if F_CFG_FIRST__enforce_Nonblockingness G w \<noteq> {}
      then {[]}
      else {})
  else
    (if k = Suc 0
      then (\<lambda>x. case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a]) ` F_CFG_FIRST__enforce_Nonblockingness G w
      else {})"

end
