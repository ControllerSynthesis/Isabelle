section {*I\_kparser\_base*}
theory
  I_kparser_base

imports
  PRJ_08__ENTRY

begin

record ('stack, 'event) parser_step_label =
  rule_lpop :: "'stack list"
  rule_rpop :: "'event list"
  rule_lpush :: "'stack list"
  rule_rpush :: "'event list"

record ('stack, 'event, 'marker) parser =
  parser_nonterms :: "'stack set"
  parser_events :: "'event set"
  parser_initial :: "'stack"
  parser_marking :: "'stack set"
  parser_rules :: "('stack, 'event) parser_step_label set"
  parser_marker :: "('stack, 'event) parser_step_label \<Rightarrow> 'marker"
  parser_bottom :: "'event"

definition valid_parser_step_label :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> bool"
  where
    "valid_parser_step_label G e \<equiv>
  (\<exists>k. rule_rpop e \<in> (kPrefix k) `
    {w @ [parser_bottom G] | w.
      set w \<subseteq> parser_events G - {parser_bottom G}})
  \<and> set (rule_rpush e) \<subseteq> parser_events G
  \<and> set (rule_lpop e) \<subseteq> parser_nonterms G
  \<and> set (rule_lpush e) \<subseteq> parser_nonterms G
  \<and> rule_lpop e \<noteq> []
  \<and> rule_lpush e \<noteq> []
  \<and> (\<exists>x. x @ rule_rpush e = rule_rpop e)
  \<and> ((\<exists>x. x @ [parser_bottom G] = rule_rpop e)
      \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rule_rpush e))"

lemma kPrefix_vs_take: "
  kPrefix k w = take k w"
  apply(simp add: kPrefix_def)
  done

definition valid_parser :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "valid_parser G \<equiv>
  finite (parser_events G)
  \<and> finite (parser_nonterms G)
  \<and> parser_initial G \<in> parser_nonterms G
  \<and> parser_marking G \<subseteq> parser_nonterms G
  \<and> finite (parser_rules G)
  \<and> (\<forall>e \<in> parser_rules G.
      valid_parser_step_label G e)
  \<and> parser_bottom G \<in> parser_events G"

definition parser_step_labels :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parser_step_label set"
  where
    "parser_step_labels G \<equiv>
  parser_rules G"

datatype ('stack, 'event) parser_destinations =
  state "'stack"
  | rule "('stack, 'event) parser_step_label"

definition parser_destinations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parser_destinations set"
  where
    "parser_destinations G \<equiv>
  state ` (parser_nonterms G)
  \<union> rule ` (parser_rules G)"

definition parser_markers :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list set"
  where
    "parser_markers G \<equiv>
  {w. set w \<subseteq> parser_events G}"

definition parser_schedulers :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list set"
  where
    "parser_schedulers G \<equiv>
  {w. \<exists>v.
    set v \<subseteq> parser_events G
    \<and> parser_bottom G \<notin> set v
    \<and> w = v @ [parser_bottom G]}"

definition parser_fixed_schedulers :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list set"
  where
    "parser_fixed_schedulers G \<equiv>
  prefix_closure (parser_schedulers G)"

definition parser_unfixed_schedulers :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list set"
  where
    "parser_unfixed_schedulers G \<equiv>
  suffix_closure (parser_schedulers G)"

definition parser_scheduler_fragments :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list set"
  where
    "parser_scheduler_fragments G \<equiv>
  {w. set w \<subseteq> parser_events G \<and> parser_bottom G \<notin> set w}"

definition parser_no_top_rules :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_no_top_rules G \<equiv>
  \<forall>e \<in> parser_rules G. rule_rpush e = []"

definition parser_observes_input_terminator :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_observes_input_terminator G \<equiv>
  \<exists>e \<in> parser_rules G. parser_bottom G \<in> set (rule_rpop e)"

definition parser_not_observes_input_terminator :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_not_observes_input_terminator G \<equiv>
  \<forall>e \<in> parser_rules G. parser_bottom G \<notin> set (rule_rpush e)"

definition parser_no_access_final_with_read :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_no_access_final_with_read G \<equiv>
  \<forall>e \<in> parser_rules G. \<forall>a.
  rule_rpop e = [a]
  \<and> rule_rpush e = []
  \<and> last (rule_lpush e) \<in> parser_marking G
  \<longrightarrow> False"

definition parser_no_leave_final_with_empty_step :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_no_leave_final_with_empty_step G \<equiv>
  \<forall>q \<in> parser_marking G.
  \<forall>e \<in> parser_rules G.
  last (rule_lpop e) = q
  \<and> rule_rpop e \<in> {[parser_bottom G], []}
  \<longrightarrow> last (rule_lpush e) \<in> parser_marking G"

primrec tau :: "
  ('a \<Rightarrow> 'b option option)
  \<Rightarrow> 'a option list
  \<Rightarrow> 'b option list"
  where
    "tau f [] = []"
  | "tau f (a # w) =
  (case a
  of None \<Rightarrow> []
  | Some a' \<Rightarrow> (case (f a')
                of None \<Rightarrow> []
                | Some a'' \<Rightarrow> (case a''
                              of None \<Rightarrow> []
                              | Some a''' \<Rightarrow> [Some a'''])))
  @ tau f w"

lemma tau_select: "
  x \<in> set (tau f w)
  \<Longrightarrow> (\<exists>y. x \<in> set (tau f [y]) \<and> y \<in> set w)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w uu_ uua_)(*strict*)
   apply(rename_tac x1 x2)
   apply(rename_tac w x1 x2)(*strict*)
   apply(rule_tac
      x="Some x2"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w uu_ uua_)(*strict*)
  apply(rename_tac x1 x2)
  apply(rename_tac a w x1 x2)(*strict*)
  apply(rule_tac
      x="Some x2"
      in exI)
  apply(clarsimp)
  done

definition valid_bounded_parser :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "valid_bounded_parser G k \<equiv>
  valid_parser G
  \<and> (\<forall>e \<in> parser_rules G. length (rule_rpop e) \<le> k)"

lemma valid_parser_initial_in_nonterms: "
  valid_parser P
  \<Longrightarrow> parser_initial P \<in> parser_nonterms P"
  apply(simp add: valid_parser_def)
  done

lemma valid_parser_bottom_in_parser_events: "
  valid_parser P
  \<Longrightarrow> parser_bottom P \<in> parser_events P"
  apply(simp add: valid_parser_def)
  done

lemma valid_parser_step_label_not_parser_bottom_random_insertion: "
  valid_parser_step_label G e
  \<Longrightarrow> (\<exists>x. x@[parser_bottom G]=rule_rpush e) \<longrightarrow> (\<exists>x. x@[parser_bottom G]=rule_rpop e)"
  apply(simp add: valid_parser_step_label_def)
  apply(erule conjE)+
  apply(rule impI)
  apply(erule exE)+
  apply(rename_tac k x xa)(*strict*)
  apply(rule_tac
      x="x@xa"
      in exI)
  apply(force)
  done

lemma valid_parser_step_label_also_req_for_rpush: "
  valid_parser_step_label G e
  \<Longrightarrow> (\<exists>k. rule_rpush e \<in> ((kPrefix k) ` ({w@[parser_bottom G]|w. set w\<subseteq> (parser_events G)-{parser_bottom G}})))"
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac k w xa)(*strict*)
  apply(case_tac e)
  apply(rename_tac k w xa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w>0")
   apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
   apply(rename_tac k xa rule_lpop rule_lpush x)(*strict*)
   apply(rule_tac
      x="Suc (length x)"
      in exI)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="x@[parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
  apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(clarsimp)
  apply(case_tac "rule_rpush")
   apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule inMap)
   apply(rule_tac
      x="[parser_bottom G]"
      in bexI)
    apply(rename_tac k w rule_lpop rule_lpush)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac k w rule_lpop rule_lpush)(*strict*)
   apply(clarsimp)
  apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_rpush = w' @ [x']")
   apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac k w xa rule_lpop rule_lpush rule_rpush a list)(*strict*)
  apply(thin_tac "rule_rpush = a # list")
  apply(clarsimp)
  apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
  apply(case_tac "x'=parser_bottom G")
   apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
   apply(rule_tac
      x="Suc(length w')"
      in exI)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="w' @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(rule_tac
      B="set w"
      in subset_trans)
    apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
    apply(rule_tac
      B="set (take k w)"
      in subset_trans)
     apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
     apply(rule_tac
      B="set (xa @ w' @ [parser_bottom G])"
      in subset_trans)
      apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
      apply(rule set_bi_append)
     apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
     apply(force)
    apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac k w xa rule_lpop rule_lpush w')(*strict*)
   apply(force)
  apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="Suc(length w')"
      in exI)
  apply(rule inMap)
  apply(clarsimp)
  apply(rule_tac
      x="w' @ [x'] @ [parser_bottom G]"
      in exI)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(rule_tac
      B="set w"
      in subset_trans)
   apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
   apply(rule_tac
      B="set (take k w)"
      in subset_trans)
    apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
    apply(rule_tac
      B="set (xa @ w' @ [x'])"
      in subset_trans)
     apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
     apply(rule set_bi_append)
    apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
    apply(force)
   apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
   apply(rule set_take_subset)
  apply(rename_tac k w xa rule_lpop rule_lpush w' x')(*strict*)
  apply(force)
  done

lemma tau_append_commutes: "
  tau f (w@v) = tau f w @ (tau f v)"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  done

primrec parser_fixed_input_length_recN :: "
  (('stack, 'event) parser_step_label, 'abstr_parser_conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where
    "parser_fixed_input_length_recN d 0 = 0"
  | "parser_fixed_input_length_recN d (Suc n) =
    (case d (Suc n) of
      Some (pair (Some e) c) \<Rightarrow>
          max
            (parser_fixed_input_length_recN d n)
            (length (rule_rpop e))
          - (length (rule_rpop e) - length (rule_rpush e))
    | _ \<Rightarrow> parser_fixed_input_length_recN d n)"

definition parser_fixed_input_length_foldl :: "
  (('stack, 'event) parser_step_label, 'abstr_parser_conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where
    "parser_fixed_input_length_foldl d n \<equiv>
  foldl
    (\<lambda>x s. (case s of [a, b] \<Rightarrow> (max x a) - (a - b)))
    0
    (map
      (\<lambda>n.
        case d n of
          Some (pair (Some e) c) \<Rightarrow>
            [length (rule_rpop e), length (rule_rpush e)])
      (nat_seq (Suc 0) n))"

primrec parser_fixed_input_length_rec1 :: "
  (('stack, 'event) parser_step_label, 'abstr_parser_conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where
    "parser_fixed_input_length_rec1 d 0 = 0"
  | "(parser_fixed_input_length_rec1 d (Suc n)) =
    (case d (Suc n) of
      Some (pair (Some e) c) \<Rightarrow>
        (case rule_rpop e of
            [] \<Rightarrow> parser_fixed_input_length_rec1 d n
            | _ \<Rightarrow> length (rule_rpush e))
      | _ \<Rightarrow> parser_fixed_input_length_rec1 d n)"

(*
  The unmarked language should be contained in the prefixclosure of the set of words which (if the parser is started with one of them) can touch every every DT_symbol.
  Furthermore, an element of this prefixclosure is only contained, if

  r·s in unmarked_language
  \<longleftrightarrow> \<exists>d t. d start with r·s·t·$ and ends with s·t·$ where s (and (if t=\<lambda>) possibly $) has been seen and t has not been seen
  \<longleftrightarrow> \<exists>d. d start with r·s·$ and ends with s·$ where s (and possibly $) has been seen

  Note, the translation of a parser into a topfree parser should preserve marked and unmarked language.
  Therefore the interpretation is reasonable.

  Example:
  derivation: q0 | ab$ \<Rightarrow> (q0, ab$, q1, $) \<Rightarrow> q1|$
  unmarked_language_element: i=0: \<lambda>
  unmarked_language_element: i=1: ab
  derivation: q0 | ab$ \<Rightarrow> (q0, ab, q1, b) \<Rightarrow> q1|b$
  unmarked_language_element: i=0: \<lambda>
  unmarked_language_element: i=1: ab
  derivation: q0 | ab$ \<Rightarrow> (q0, a, q1, \<lambda>) \<Rightarrow> q1|b$
  unmarked_language_element: i=0: \<lambda>
  unmarked_language_element: i=1: a
*)

lemma parser_inst_AX_empty_fixed_scheduler_in_fixed_schedulers: "
  \<forall>G. valid_parser G \<longrightarrow> [] \<in> parser_fixed_schedulers G"
  apply(simp add: parser_fixed_schedulers_def prefix_closure_def prefix_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma parser_inst_AX_empty_scheduler_fragment_in_scheduler_fragments: "
  \<forall>G. valid_parser G \<longrightarrow> [] \<in> parser_scheduler_fragments G"
  apply(simp add: parser_scheduler_fragments_def)
  done

lemma parser_inst_AX_join_scheduler_fragments_closed : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sE1. sE1 \<in> parser_scheduler_fragments G \<longrightarrow> (\<forall>sE2. sE2 \<in> parser_scheduler_fragments G \<longrightarrow> sE1 @ sE2 \<in> parser_scheduler_fragments G)))"
  apply(simp add: parser_scheduler_fragments_def)
  done

lemma parser_inst_AX_join_scheduler_fragments_foldl_split: "
  (\<forall>w v. foldl (@) (foldl (@) [] w) v = foldl (@) [] w @ foldl (@) [] v)"
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma parser_inst_AX_foldl_join_scheduler_fragments : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sE. sE \<in> parser_scheduler_fragments G \<longrightarrow> (\<forall>w. set w \<subseteq> parser_scheduler_fragments G \<longrightarrow> foldl (@) sE w = sE @ foldl (@) [] w)))"
  apply(clarsimp)
  apply(rename_tac G sE w)(*strict*)
  apply (metis concat_conv_foldl foldl_conv_concat)
  done

lemma parser_inst_AX_extend_unfixed_scheduler_unfixed_scheduler_right_quotient_empty: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> the (right_quotient_word sUF []) = sUF))"
  apply(simp add: right_quotient_word_def)
  done

lemma parser_inst_AX_unfixed_scheduler_right_quotient_all: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> right_quotient_word sUF sUF = Some []))"
  apply(clarsimp)
  apply(rename_tac G sUF)(*strict*)
  apply(simp add: right_quotient_word_def)
  done

lemma parser_inst_AX_empty_unfixed_scheduler_in_unfixed_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> [] \<in> parser_unfixed_schedulers G)"
  apply(simp add: parser_unfixed_schedulers_def suffix_closure_def suffix_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma parser_inst_AX_extend_unfixed_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sE. sE \<in> parser_scheduler_fragments G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> sE @ sUF \<in> parser_unfixed_schedulers G)))"
  apply(simp add: suffix_def parser_unfixed_schedulers_def parser_scheduler_fragments_def parser_schedulers_def suffix_closure_def)
  apply(clarsimp)
  apply(rename_tac G sE c ca)(*strict*)
  apply(rule_tac
      x="sE@ca@[parser_bottom G]"
      in exI)
  apply(clarsimp)
  done

lemma parser_inst_AX_extend_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sE. sE \<in> parser_scheduler_fragments G \<longrightarrow> (\<forall>s. s \<in> parser_schedulers G \<longrightarrow> sE @ s \<in> parser_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G sE s)(*strict*)
  apply(simp add: parser_schedulers_def parser_scheduler_fragments_def)
  apply(clarsimp)
  done

lemma parser_inst_AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sUF. sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sE. (sE @ sUF) \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G sUF sE)(*strict*)
  apply(simp add: suffix_def)
  apply(force)
  done

lemma parser_inst_AX_empty_scheduler_in_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> [parser_bottom G] \<in> parser_schedulers G)"
  apply(simp add: parser_schedulers_def)
  done

lemma parser_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sF. sF \<in> parser_fixed_schedulers G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> (\<not> sF \<sqsupseteq> [parser_bottom G]) = sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> sF @ sUF \<in> parser_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G sF sUF)(*strict*)
  apply(simp add: suffix_def)
  apply(simp add: parser_schedulers_def parser_fixed_schedulers_def parser_unfixed_schedulers_def prefix_closure_def prefix_def suffix_closure_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G sF sUF vb c vc ca)(*strict*)
  apply(case_tac sUF)
   apply(rename_tac G sF sUF vb c vc ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G vb c vc cb)(*strict*)
   apply(case_tac c)
    apply(rename_tac G vb c vc cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac G vb c vc cb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G vb c vc cb a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G vb c vc cb a list)(*strict*)
   apply(thin_tac "c = a # list")
   apply(clarsimp)
  apply(rename_tac G sF sUF vb c vc ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. sUF = w' @ [x']")
   apply(rename_tac G sF sUF vb c vc ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G sF sUF vb c vc ca a list)(*strict*)
  apply(thin_tac "sUF = a # list")
  apply(clarsimp)
  apply(rename_tac G sF vb c ca w')(*strict*)
  apply(case_tac c)
   apply(rename_tac G sF vb c ca w')(*strict*)
   apply(clarsimp)
  apply(rename_tac G sF vb c ca w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G sF vb c ca w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G sF vb c ca w' a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  done

lemma valid_bounded_parser_vs_valid_parser: "
  valid_bounded_parser G k
  \<Longrightarrow> valid_parser G"
  apply(simp add: valid_bounded_parser_def)
  done

lemma parser1X_inst_AX_empty_fixed_scheduler_in_fixed_schedulers: "
  \<forall>G. valid_bounded_parser G (Suc 0) \<longrightarrow> [] \<in> parser_fixed_schedulers G"
  apply(metis valid_bounded_parser_vs_valid_parser parser_inst_AX_empty_fixed_scheduler_in_fixed_schedulers)
  done

lemma parser_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>sF. sF \<in> parser_fixed_schedulers G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sF @ sUF \<in> parser_schedulers G \<longrightarrow> (\<not> sF \<sqsupseteq> [parser_bottom G]) = sUF \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G sF sUF)(*strict*)
  apply(simp add: suffix_closure_def prefix_closure_def prefix_def suffix_def parser_schedulers_def parser_fixed_schedulers_def parser_unfixed_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G sF sUF vb vc c vd ca)(*strict*)
  apply(case_tac sF)
   apply(rename_tac G sF sUF vb vc c vd ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G sF sUF vb vc c vd ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. sF = w' @ [x']")
   apply(rename_tac G sF sUF vb vc c vd ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G sF sUF vb vc c vd ca a list)(*strict*)
  apply(thin_tac "sF = a # list")
  apply(clarsimp)
  apply(rename_tac G sUF vb vc c vd ca w' x')(*strict*)
  apply(case_tac c)
   apply(rename_tac G sUF vb vc c vd ca w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac G sUF vb vc c vd ca w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G sUF vb vc c vd ca w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G sUF vb vc c vd ca w' x' a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  apply(rename_tac G sUF vb vd ca w' x' w'a)(*strict*)
  apply(metis last_append last_snoc snoc_eq_iff_butlast)
  done

lemma valid_parser_rules_rhs_gets_shorter: "
  valid_parser P
  \<Longrightarrow> e \<in> parser_rules P
  \<Longrightarrow> length (rule_rpush e) \<le> length (rule_rpop e)"
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(auto)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac k w xa)(*strict*)
  apply(rule_tac
      t="kPrefix k (w @ [parser_bottom P])"
      and s="xa @ rule_rpush e"
      in ssubst)
   apply(rename_tac k w xa)(*strict*)
   apply(force)
  apply(rename_tac k w xa)(*strict*)
  apply(simp (no_asm_use))
  done

definition parser_empty_fixed_scheduler :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_fixed_scheduler G \<equiv>
  []"
declare parser_empty_fixed_scheduler_def [simp add]

definition parser_empty_unfixed_scheduler :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_unfixed_scheduler G \<equiv>
  []"
declare parser_empty_unfixed_scheduler_def [simp add]

definition parser_fixed_scheduler_extendable :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "parser_fixed_scheduler_extendable G w \<equiv>
  \<not> suffix w [parser_bottom G]"
declare parser_fixed_scheduler_extendable_def [simp add]

definition parser_unfixed_scheduler_extendable :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "parser_unfixed_scheduler_extendable G w \<equiv>
  suffix w [parser_bottom G]"
declare parser_unfixed_scheduler_extendable_def [simp add]

definition parser_empty_history :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_history G \<equiv>
  []"
declare parser_empty_history_def [simp add]

definition parser_empty_history_fragment :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_history_fragment G \<equiv>
  []"
declare parser_empty_history_fragment_def [simp add]

definition parser_empty_scheduler :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_scheduler G \<equiv>
  [parser_bottom G]"
declare parser_empty_scheduler_def [simp add]

definition parser_empty_scheduler_fragment :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list"
  where
    "parser_empty_scheduler_fragment G \<equiv>
  []"
declare parser_empty_scheduler_fragment_def [simp add]

lemma parser_inst_ATS_SchedF_Basic_axioms: "
  ATS_SchedF_Basic_axioms valid_parser parser_fixed_schedulers
     parser_empty_fixed_scheduler"
  apply(simp add: ATS_SchedF_Basic_axioms_def)
  apply(simp add: parser_inst_AX_empty_fixed_scheduler_in_fixed_schedulers )
  done

lemma parser_inst_ATS_Scheduler_Fragment_axioms: "
  ATS_Scheduler_Fragment_axioms valid_parser parser_scheduler_fragments
     parser_empty_scheduler_fragment (@)"
  apply(simp add: ATS_Scheduler_Fragment_axioms_def)
  apply(simp add: parser_inst_AX_join_scheduler_fragments_closed parser_inst_AX_join_scheduler_fragments_foldl_split parser_inst_AX_empty_scheduler_fragment_in_scheduler_fragments )
  apply(simp add: parser_inst_AX_foldl_join_scheduler_fragments)
  done

lemma parser_inst_ATS_SchedUF_Basic_axioms: "
  ATS_SchedUF_Basic_axioms valid_parser parser_scheduler_fragments
     parser_empty_scheduler_fragment parser_unfixed_schedulers
     parser_empty_unfixed_scheduler right_quotient_word (@)
     parser_unfixed_scheduler_extendable"
  apply(simp add: ATS_SchedUF_Basic_axioms_def)
  apply(simp add: parser_inst_AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable parser_inst_AX_extend_unfixed_scheduler_unfixed_scheduler_right_quotient_empty parser_inst_AX_unfixed_scheduler_right_quotient_all parser_inst_AX_empty_unfixed_scheduler_in_unfixed_schedulers parser_inst_AX_extend_unfixed_scheduler_closed )
  done

lemma parser_inst_ATS_Sched_Basic_axioms: "
  ATS_Sched_Basic_axioms valid_parser parser_fixed_schedulers
     parser_fixed_scheduler_extendable parser_unfixed_schedulers
     parser_unfixed_scheduler_extendable parser_schedulers (@)"
  apply(simp add: ATS_Sched_Basic_axioms_def)
  apply(simp add: parser_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed )
  done

lemmas parser_interpretations =
  parser_inst_ATS_SchedF_Basic_axioms
  parser_inst_ATS_Sched_Basic_axioms
  parser_inst_ATS_Scheduler_Fragment_axioms
  parser_inst_ATS_SchedUF_Basic_axioms

lemma PARSER_rule_rpop_in_parser_events: "
  valid_parser G
  \<Longrightarrow> e \<in> parser_rules G
  \<Longrightarrow> set (rule_rpop e) \<subseteq> parser_events G"
  apply(simp add: valid_parser_def valid_parser_step_label_def kPrefix_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w xb)(*strict*)
  apply(simp add: valid_parser_def valid_parser_step_label_def kPrefix_def)
  apply(erule disjE)
   apply(rename_tac x k w xb)(*strict*)
   apply(rule_tac
      A="set w"
      in set_mp)
    apply(rename_tac x k w xb)(*strict*)
    apply(force)
   apply(rename_tac x k w xb)(*strict*)
   apply (metis in_set_takeD)
  apply(rename_tac x k w xb)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac x k w xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac x k w xb nat)(*strict*)
  apply(clarsimp)
  done

end
