section {*FUNCTION\_\_EDPDA\_RMPOE\_\_EDPDA\_REMOVE\_MASS\_POPPING\_EDGES*}
theory
  FUNCTION__EDPDA_RMPOE__EDPDA_REMOVE_MASS_POPPING_EDGES

imports
  PRJ_12_07_02_02__ENTRY

begin

definition restrict_to_extensions :: "
  'a list
  \<Rightarrow> 'a list set
  \<Rightarrow> 'a list set"
  where
    "restrict_to_extensions w B \<equiv>
  {w' \<in> B. prefix w w'}"

definition common_prefixes :: "
  'a list
  \<Rightarrow> 'a list
  \<Rightarrow> 'a list set"
  where
    "common_prefixes w v \<equiv>
  {x. \<exists>n. take n w = x \<and> take n v = x}"

definition longest :: "
  'a list set
  \<Rightarrow> 'a list"
  where
    "longest B \<equiv>
  THE w. w \<in> B \<and> (\<forall>w' \<in> B. length w' \<le> length w)"

definition longest_common_prefix :: "
  'stack list
  \<Rightarrow> 'stack list
  \<Rightarrow> 'stack list"
  where
    "longest_common_prefix w v \<equiv>
  longest (common_prefixes w v)"

definition longest_popping_sequence :: "
  'stack list
  \<Rightarrow> 'stack list set
  \<Rightarrow> 'stack list
  \<Rightarrow> 'stack list"
  where
    "longest_popping_sequence wpop POP wstack \<equiv>
  longest ((\<lambda>w. longest_common_prefix w wstack) ` restrict_to_extensions wpop POP)"

definition F_EDPDA_RMPOE_longest_popping_sequence :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'stack list
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> 'stack list"
  where
    "F_EDPDA_RMPOE_longest_popping_sequence G w e \<equiv>
  longest_popping_sequence (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) w"

lemma longest_popping_sequence_exists: "
  valid_epda G
  \<Longrightarrow> set w \<subseteq> epda_gamma G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> prefix (edge_pop e) w
  \<Longrightarrow> \<exists>e'. e' \<in> epda_delta G \<and> edge_src e' = edge_src e \<and> prefix (edge_pop e') w \<and> prefix (edge_pop e) (edge_pop e') \<and> (\<forall>e'' \<in> epda_delta G. edge_src e'' = edge_src e' \<and> prefix (edge_pop e'') w \<and> prefix (edge_pop e) (edge_pop e'') \<longrightarrow> prefix (edge_pop e'') (edge_pop e'))"
  apply(subgoal_tac "\<exists>x. (\<lambda>x. (\<exists>e' \<in> epda_delta G. prefix (edge_pop e) (edge_pop e') \<and> edge_src e=edge_src e' \<and> prefix (edge_pop e') w \<and> edge_pop e'=x)) x \<and> length x = Max {length x| x. SSP x}" for SSP)
   prefer 2
   apply(rule Max_Sat)
    apply(clarsimp)
    apply(rule_tac
      x="edge_pop e"
      in exI)
    apply(rule_tac
      x="e"
      in bexI)
     apply(clarsimp)
     apply(simp add: prefix_def)
    apply(force)
   apply(rule_tac
      B="(length ` (((edge_pop) ` (epda_delta G))))"
      in finite_subset)
    apply(force)
   apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac e')(*strict*)
  apply(rule_tac
      x="e'"
      in exI)
  apply(clarsimp)
  apply(rename_tac e' e'')(*strict*)
  apply(subgoal_tac "length (edge_pop e'') \<le> length (edge_pop e')")
   apply(rename_tac e' e'')(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac e' e'' c ca cb cc "cd")(*strict*)
   apply(subgoal_tac "edge_pop e'' \<sqsubseteq> (edge_pop e) \<or> (edge_pop e) \<sqsubseteq> edge_pop e''")
    apply(rename_tac e' e'' c ca cb cc "cd")(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac e' e'' c ca cb cc "cd")(*strict*)
   apply(erule disjE)
    apply(rename_tac e' e'' c ca cb cc "cd")(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac e' e'' c ca cb cc "cd" ce)(*strict*)
    apply(case_tac e)
    apply(rename_tac e' e'' c ca cb cc "cd" ce edge_srca edge_event edge_popa edge_push edge_trg)(*strict*)
    apply(case_tac e'')
    apply(rename_tac e' e'' c ca cb cc "cd" ce edge_srca edge_event edge_popa edge_push edge_trg edge_srcaa edge_eventa edge_popaa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac e' c ca cb edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga)(*strict*)
    apply(case_tac e')
    apply(rename_tac e' c ca cb edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_popaa edge_pushb edge_trgb)(*strict*)
    apply(clarsimp)
   apply(rename_tac e' e'' c ca cb cc "cd")(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac e' e'' c ca cb cc "cd" ce)(*strict*)
   apply(case_tac e)
   apply(rename_tac e' e'' c ca cb cc "cd" ce edge_srca edge_event edge_popa edge_push edge_trg)(*strict*)
   apply(case_tac e'')
   apply(rename_tac e' e'' c ca cb cc "cd" ce edge_srca edge_event edge_popa edge_push edge_trg edge_srcaa edge_eventa edge_popaa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac e' ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga)(*strict*)
   apply(case_tac e')
   apply(rename_tac e' ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_popaa edge_pushb edge_trgb)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb)(*strict*)
   apply(subgoal_tac "ca \<sqsubseteq> cd \<or> cd \<sqsubseteq> ca")
    apply(rename_tac ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb)(*strict*)
   apply(erule disjE)
    apply(rename_tac ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac ca cc edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb c)(*strict*)
    apply(case_tac c)
     apply(rename_tac ca cc edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb c)(*strict*)
     apply(force)
    apply(rename_tac ca cc edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb c a list)(*strict*)
    apply(force)
   apply(rename_tac ca cb cc "cd" edge_event edge_popa edge_push edge_trg edge_eventa edge_pusha edge_trga edge_srca edge_eventb edge_pushb edge_trgb)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac e' e'')(*strict*)
  apply(rule_tac
      t="length (edge_pop e')"
      and s="x" for x
      in ssubst)
   apply(rename_tac e' e'')(*strict*)
   prefer 2
   apply(rule Max_ge)
    apply(rename_tac e' e'')(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac e' e'')(*strict*)
   apply(rule_tac
      B="(length ` (((edge_pop) ` (epda_delta G))))"
      in finite_subset)
    apply(rename_tac e' e'')(*strict*)
    apply(force)
   apply(rename_tac e' e'')(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac e' e'')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="edge_pop e''"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="e''"
      in bexI)
   apply(rename_tac e' e'')(*strict*)
   apply(clarsimp)
  apply(rename_tac e' e'')(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE__states_on_gamma: "
  valid_epda G
  \<Longrightarrow> cons_tuple3 q w (Some x) \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> x \<in> epda_gamma G"
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(simp add: valid_epda_def)
  apply(clarsimp)
  done

lemma F_EDPDA_RMPOE__states_on_gamma2: "
  valid_epda G
  \<Longrightarrow> cons_tuple3 q w x \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> set w \<subseteq> epda_gamma G"
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x e)(*strict*)
   apply(simp add: strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac x e c)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac x e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x e c)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x e c a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G]"
      in disjE)
    apply(rename_tac x e c a aa)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac x e c a aa)(*strict*)
     apply(clarsimp)
     apply (metis Diff_iff butlast_append_prime butlast_snoc nset_mp set_append1)
    apply(rename_tac x e c a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x e c a)(*strict*)
    apply (metis Diff_subset List.insert_def List.set_insert butlast_shift butlast_snoc insert_subset set_app_subset subsetE)
   apply(rename_tac x e c a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x e c aa)(*strict*)
   apply (metis DiffE subsetD)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x e)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac x e c)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac x e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x e c)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x e c a aa)(*strict*)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x e)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac x e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x e)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x e a)(*strict*)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac x e \<gamma>)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac x e \<gamma>)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x e \<gamma>)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x e \<gamma> c a aa)(*strict*)
   apply (metis DiffE append_self_conv butlast_append_prime butlast_snoc set_append_contra1 subsetD)
  apply(clarsimp)
  done

lemma F_EDPDA_RMPOE__states_do_not_consume_box: "
  valid_epda G
  \<Longrightarrow> cons_tuple3 q w x \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> epda_box G \<notin> set w"
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(simp add: strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e c)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac e c a aa)(*strict*)
   apply(case_tac c)
    apply(rename_tac e c a aa)(*strict*)
    apply(force)
   apply(rename_tac e c a aa ab list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac e c a aa ab list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac e c a aa ab list)(*strict*)
   apply(thin_tac "c=ab#list")
   apply(clarsimp)
   apply(rename_tac e a aa w' x')(*strict*)
   apply (metis List.insert_def List.set_insert butlast_snoc butlast_snoc_2 insert_subset nset_diff set_app_subset)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e c)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac e c a aa)(*strict*)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac e a)(*strict*)
   apply(force)
  apply(erule disjE)
   apply(clarsimp)
   apply(rename_tac e \<gamma>)(*strict*)
   apply(simp add: suffix_def strict_prefix_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e \<gamma>)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e \<gamma>)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def prefix_def)
   apply(clarsimp)
   apply(rename_tac e \<gamma> c a aa)(*strict*)
   apply (metis List.butlast_append append_Nil2 butlast_snoc insert_absorb insert_subset nset_diff set_append1)
  apply(force)
  done

theorem F_EDPDA_RMPOE_preserves_epda: "
  valid_epda G
  \<Longrightarrow> valid_epda (F_EDPDA_RMPOE G)"
  apply(simp (no_asm) add: valid_epda_def F_EDPDA_RMPOE_def)
  apply(rule context_conjI)
   apply(simp add: valid_epda_def)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
    apply(rule_tac
      f="\<lambda>(e,w). cons_tuple3 (edge_src e) w None"
      and A="epda_delta G"
      and B="prefix_closure{(edge_pop e')| e'. e' \<in> epda_delta G}"
      in finite_cart_image2)
      apply(force)
     apply(rule_tac
      X="epda_gamma G"
      in prefix_closure_preserves_finiteness)
       apply(force)
      apply(clarsimp)
     apply(clarsimp)
     apply(rename_tac e')(*strict*)
     apply(simp add: kleene_star_def)
     apply(erule_tac
      x="e'"
      in ballE)
      apply(rename_tac e')(*strict*)
      apply(simp add: valid_epda_step_label_def)
      apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
      apply(force)
     apply(rename_tac e')(*strict*)
     apply(force)
    apply(clarsimp)
    apply(rename_tac e w)(*strict*)
    apply(rule inMap)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac e w)(*strict*)
     apply(rule_tac
      x="e"
      in bexI)
      apply(rename_tac e w)(*strict*)
      apply(force)
     apply(rename_tac e w)(*strict*)
     apply(force)
    apply(rename_tac e w)(*strict*)
    apply(simp add: strict_prefix_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac e w c)(*strict*)
    apply(case_tac c)
     apply(rename_tac e w c)(*strict*)
     apply(force)
    apply(rename_tac e w c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac e w c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac e w c a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac e w w' x')(*strict*)
    apply(force)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__states_bottom_on_top_def)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__states_last_of_pop_def)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__states_context_of_top_def)
    apply(rule_tac
      f="\<lambda>(e,\<gamma>,x). cons_tuple3 (edge_src e) x (Some \<gamma>)"
      and A="epda_delta G"
      and B="epda_gamma G"
      and C="prefix_closure{(edge_pop e')| e'. e' \<in> epda_delta G}"
      in finite_cart_image3)
       apply(force)
      apply(force)
     apply(rule_tac
      X="epda_gamma G"
      in prefix_closure_preserves_finiteness)
       apply(force)
      apply(clarsimp)
     apply(clarsimp)
     apply(rename_tac e')(*strict*)
     apply(simp add: kleene_star_def)
     apply(erule_tac
      x="e'"
      in ballE)
      apply(rename_tac e')(*strict*)
      apply(simp add: valid_epda_step_label_def)
      apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
      apply(force)
     apply(rename_tac e')(*strict*)
     apply(force)
    apply(clarsimp)
    apply(rename_tac e \<gamma> xa)(*strict*)
    apply(rule inMap)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac e \<gamma> xa)(*strict*)
     apply(rule_tac
      x="e"
      in bexI)
      apply(rename_tac e \<gamma> xa)(*strict*)
      apply(force)
     apply(rename_tac e \<gamma> xa)(*strict*)
     apply(force)
    apply(rename_tac e \<gamma> xa)(*strict*)
    apply(simp add: strict_prefix_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac e \<gamma> xa c)(*strict*)
    apply(case_tac c)
     apply(rename_tac e \<gamma> xa c)(*strict*)
     apply(force)
    apply(rename_tac e \<gamma> xa c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac e \<gamma> xa c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac e \<gamma> xa c a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac e \<gamma> xa w' x')(*strict*)
    apply(force)
   apply(simp add: F_EDPDA_RMPOE__states_basic_def)
  apply(simp add: Let_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def)
    apply(rule_tac
      f="\<lambda>e q. {\<lparr>edge_src = cons_tuple3 (edge_src e) x (Some \<gamma>), edge_event = edge_event e, edge_pop = [\<gamma>], edge_push = edge_push e @ the (left_quotient_word (edge_pop e) (x @ [\<gamma>])), edge_trg = cons_tuple3 (edge_trg e) [] None\<rparr>| x \<gamma>. q=cons_tuple3 (edge_src e) x (Some \<gamma>)}"
      and A="epda_delta G"
      and B="F_EDPDA_RMPOE__states G"
      in finite_image_subset2)
       apply(force)
      apply(force)
     apply(rename_tac x y)(*strict*)
     apply(rule finite_by_one)
     apply(rename_tac x y a b)(*strict*)
     apply(force)
    apply(force)
   apply(rule conjI)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(rule_tac
      f="\<lambda>qx qy. {\<lparr>edge_src = cons_tuple3 q w None, edge_event = None, edge_pop = [a], edge_push = [], edge_trg = cons_tuple3 q (w @ [a]) None\<rparr>| q w a. qx=cons_tuple3 q w None \<and> qy=cons_tuple3 q (w @ [a]) None}"
      and A="F_EDPDA_RMPOE__states G"
      and B="F_EDPDA_RMPOE__states G"
      in finite_image_subset2)
       apply(force)
      apply(force)
     apply(rename_tac x y)(*strict*)
     apply(rule finite_by_one)
     apply(rename_tac x y a b)(*strict*)
     apply(force)
    apply(force)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(rule_tac
      f="\<lambda>qx qy. {\<lparr>edge_src = cons_tuple3 q w None, edge_event = None, edge_pop = [a], edge_push = [a], edge_trg = cons_tuple3 q w (Some a)\<rparr>| q w a. qx=cons_tuple3 q w None \<and> qy=cons_tuple3 q w (Some a)}"
      and A="F_EDPDA_RMPOE__states G"
      and B="F_EDPDA_RMPOE__states G"
      in finite_image_subset2)
      apply(force)
     apply(force)
    apply(rename_tac x y)(*strict*)
    apply(rule finite_by_one)
    apply(rename_tac x y a b)(*strict*)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
   apply(simp add: F_EDPDA_RMPOE__states_def F_EDPDA_RMPOE__states_basic_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
  apply(rule conjI)
   apply(simp add: valid_epda_def)
   apply(simp add: F_EDPDA_RMPOE__states_def F_EDPDA_RMPOE__states_basic_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp only: F_EDPDA_RMPOE__edges_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(clarsimp)
   apply(rename_tac x ea \<gamma>)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(subgoal_tac "valid_epda_step_label G ea")
    apply(rename_tac x ea \<gamma>)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def)
   apply(rename_tac x ea \<gamma>)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x ea \<gamma>)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def F_EDPDA_RMPOE__states_basic_def)
   apply(rename_tac x ea \<gamma>)(*strict*)
   apply(rule conjI)
    apply(rename_tac x ea \<gamma>)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac x ea \<gamma> a aa)(*strict*)
    apply(case_tac "\<gamma>=epda_box G")
     apply(rename_tac x ea \<gamma> a aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea a aa)(*strict*)
     apply(rule_tac
      x="[]"
      in exI)
     apply(force)
    apply(rename_tac x ea \<gamma> a aa)(*strict*)
    apply(clarsimp)
    apply(rule F_EDPDA_RMPOE__states_on_gamma)
     apply(rename_tac x ea \<gamma> a aa)(*strict*)
     apply(force)
    apply(rename_tac x ea \<gamma> a aa)(*strict*)
    apply(force)
   apply(rename_tac x ea \<gamma>)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac x ea \<gamma> c)(*strict*)
   apply(rule_tac
      t="left_quotient_word (edge_pop ea) (x @ [\<gamma>])"
      and s="Some c"
      in ssubst)
    apply(rename_tac x ea \<gamma> c)(*strict*)
    apply (metis left_quotient_word_removes_right_addition_hlp)
   apply(rename_tac x ea \<gamma> c)(*strict*)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac x ea \<gamma> c)(*strict*)
    prefer 2
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac x ea \<gamma> c a aa ab)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac x ea \<gamma> c a aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea c a aa ab)(*strict*)
     apply(erule_tac
      P="edge_push ea = aa @ [epda_box G]"
      in disjE)
      apply(rename_tac x ea c a aa ab)(*strict*)
      apply(clarsimp)
      apply(rename_tac x ea c a aa ab ac)(*strict*)
      apply(erule_tac
      P="ac = a"
      in disjE)
       apply(rename_tac x ea c a aa ab ac)(*strict*)
       apply(clarsimp)
       apply(rename_tac x ea c a aa ab)(*strict*)
       apply(force)
      apply(rename_tac x ea c a aa ab ac)(*strict*)
      apply(force)
     apply(rename_tac x ea c a aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea c a ab)(*strict*)
     apply(erule_tac
      P="edge_pop ea = a @ [epda_box G]"
      in disjE)
      apply(rename_tac x ea c a ab)(*strict*)
      apply(force)
     apply(rename_tac x ea c a ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea c ab)(*strict*)
     apply(erule disjE)
      apply(rename_tac x ea c ab)(*strict*)
      apply(force)
     apply(rename_tac x ea c ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea c)(*strict*)
     apply(case_tac c)
      apply(rename_tac x ea c)(*strict*)
      apply(force)
     apply(rename_tac x ea c a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac x ea c a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac x ea c a list)(*strict*)
     apply(thin_tac "c=a#list")
     apply(clarsimp)
    apply(rename_tac x ea \<gamma> c a aa ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac x ea \<gamma> c a aa ab ac)(*strict*)
    apply(case_tac c)
     apply(rename_tac x ea \<gamma> c a aa ab ac)(*strict*)
     apply(clarsimp)
    apply(rename_tac x ea \<gamma> c a aa ab ac ad list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac x ea \<gamma> c a aa ab ac ad list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x ea \<gamma> c a aa ab ac ad list)(*strict*)
    apply(thin_tac "c=ad#list")
    apply(clarsimp)
   apply(rename_tac x ea \<gamma> c)(*strict*)
   apply(thin_tac "finite (F_EDPDA_RMPOE__states G)")
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
   apply(simp add: prefix_def suffix_def)
   apply(erule disjE)
    apply(rename_tac x ea \<gamma> c)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea c e ca)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac ea c e ca a aa)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G e")
     apply(rename_tac ea c e ca a aa)(*strict*)
     prefer 2
     apply(simp add: valid_epda_def)
    apply(rename_tac ea c e ca a aa)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac ea c e ca a aa ab ac)(*strict*)
    apply(erule_tac
      P="edge_push ea = aa @ [epda_box G]"
      in disjE)
     apply(rename_tac ea c e ca a aa ab ac)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea c e ca a aa ab ac ad)(*strict*)
     apply(case_tac c)
      apply(rename_tac ea c e ca a aa ab ac ad)(*strict*)
      apply(clarsimp)
      apply(rename_tac ea e ca a aa ab ac ae)(*strict*)
      apply(rule_tac
      x="aa"
      in exI)
      apply(force)
     apply(rename_tac ea c e ca a aa ab ac ad ae list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac ea c e ca a aa ab ac ad ae list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac ea c e ca a aa ab ac ad ae list)(*strict*)
     apply(thin_tac "c=ae#list")
     apply(clarsimp)
     apply(rename_tac ea e a aa ab ad w')(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac ea e a aa ab ad w')(*strict*)
      apply(force)
     apply(rename_tac ea e a aa ab ad w')(*strict*)
     apply (metis ConsApp List.set_simps(2) append_eq_appendI not_in_diff set_append2 set_append_contra1 set_subset_in)
    apply(rename_tac ea c e ca a aa ab ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea c e ca a ab ac)(*strict*)
    apply(case_tac c)
     apply(rename_tac ea c e ca a ab ac)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea e ca a ab ac)(*strict*)
     apply(subgoal_tac "(\<exists>a. set a \<subseteq> epda_gamma G - {epda_box G} \<and> edge_push ea = a @ [epda_box G])")
      apply(rename_tac ea e ca a ab ac)(*strict*)
      prefer 2
      apply(subgoal_tac "(\<exists>a. set a \<subseteq> epda_gamma G - {epda_box G} \<and> edge_push e = a @ [epda_box G])")
       apply(rename_tac ea e ca a ab ac)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac ea e ca a ab ac)(*strict*)
      apply(force)
     apply(rename_tac ea e ca a ab ac)(*strict*)
     apply(clarsimp)
    apply(rename_tac ea c e ca a ab ac aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac ea c e ca a ab ac aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ea c e ca a ab ac aa list)(*strict*)
    apply(thin_tac "c=aa#list")
    apply(clarsimp)
    apply(rename_tac ea e a ab ac w')(*strict*)
    apply(erule_tac
      P="edge_pop ea = a @ [epda_box G]"
      in disjE)
     apply(rename_tac ea e a ab ac w')(*strict*)
     apply(clarsimp)
    apply(rename_tac ea e a ab ac w')(*strict*)
    apply(clarsimp)
    apply(rename_tac ea e ab ac w')(*strict*)
    apply(subgoal_tac "valid_epda_step_label G e")
     apply(rename_tac ea e ab ac w')(*strict*)
     prefer 2
     apply(simp add: valid_epda_def)
    apply(rename_tac ea e ab ac w')(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac ea e ab ac w' a aa)(*strict*)
    apply(rule_tac
      x="edge_push ea @ w'"
      in exI)
    apply(clarsimp)
    apply(rename_tac ea e ab w' a x)(*strict*)
    apply(erule_tac
      P="edge_pop ea @ w' = ab"
      in disjE)
     apply(rename_tac ea e ab w' a x)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea e w' a x)(*strict*)
     apply(force)
    apply(rename_tac ea e ab w' a x)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea e w' a x)(*strict*)
    apply (metis List.set_simps(2) append_eq_appendI not_in_diff set_append2 set_subset_in)
   apply(rename_tac x ea \<gamma> c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x ea \<gamma> c e ca)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G e")
    apply(rename_tac x ea \<gamma> c e ca)(*strict*)
    prefer 2
    apply(simp add: valid_epda_def)
   apply(rename_tac x ea \<gamma> c e ca)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x ea \<gamma> c e ca a aa ab ac)(*strict*)
   apply(case_tac c)
    apply(rename_tac x ea \<gamma> c e ca a aa ab ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac x ea \<gamma> e ca a aa ab ac)(*strict*)
    apply(erule_tac
      P="edge_push ea = aa @ [epda_box G]"
      in disjE)
     apply(rename_tac x ea \<gamma> e ca a aa ab ac)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ea e ca a aa ab ac)(*strict*)
     apply(rule_tac
      x="aa"
      in exI)
     apply(force)
    apply(rename_tac x ea \<gamma> e ca a aa ab ac)(*strict*)
    apply(rule_tac
      x="aa"
      in exI)
    apply(force)
   apply(rename_tac x ea \<gamma> c e ca a aa ab ac ad list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac x ea \<gamma> c e ca a aa ab ac ad list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x ea \<gamma> c e ca a aa ab ac ad list)(*strict*)
   apply(thin_tac "c=ad#list")
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca a aa ab ac w')(*strict*)
   apply(erule_tac
      P="edge_push ea = aa @ [epda_box G]"
      in disjE)
    apply(rename_tac ea \<gamma> e ca a aa ab ac w')(*strict*)
    apply(clarsimp)
    apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad)(*strict*)
    apply(erule_tac
      P="edge_pop e = ab @ [epda_box G]"
      in disjE)
     apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad ae)(*strict*)
     apply(case_tac "w'@ca")
      apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad ae)(*strict*)
      apply(clarsimp)
     apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad ae af list)(*strict*)
     apply(subgoal_tac "\<exists>wx x'. w'@ca = wx @ [x']")
      apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad ae af list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad ae af list)(*strict*)
     apply(thin_tac "w'@ca=af#list")
     apply(clarsimp)
    apply(rename_tac ea \<gamma> e ca a aa ab ac w' ad)(*strict*)
    apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca a aa ab ac w')(*strict*)
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca a ab ac w')(*strict*)
   apply(erule_tac
      P="edge_pop ea = a @ [epda_box G]"
      in disjE)
    apply(rename_tac ea \<gamma> e ca a ab ac w')(*strict*)
    apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca a ab ac w')(*strict*)
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w')(*strict*)
   apply(case_tac "\<gamma>=epda_box G")
    apply(rename_tac ea \<gamma> e ca ab ac w')(*strict*)
    apply(clarsimp)
    apply(rename_tac ea e ca ab ac w')(*strict*)
    apply(rule_tac
      x="edge_push ea @ w'"
      in exI)
    apply(clarsimp)
    apply(rename_tac ea e ca ab ac w' x)(*strict*)
    apply(subgoal_tac "\<exists>w1 w2. w1@[x]@w2=w'")
     apply(rename_tac ea e ca ab ac w' x)(*strict*)
     prefer 2
     apply (metis ConsApp in_set_conv_decomp)
    apply(rename_tac ea e ca ab ac w' x)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
    apply(rule conjI)
     apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
     apply(rule_tac
      A="set(edge_pop e)"
      in set_mp)
      apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
      apply(rule valid_epda_pop_in_gamma)
       apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
       apply(force)
      apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
     apply(rule_tac
      t="edge_pop e"
      and s="edge_pop ea @ w1 @ x # w2 @ ca"
      in ssubst)
      apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac ea e ca ab ac x w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea e ca ab ac w1 w2)(*strict*)
    apply(case_tac "w2")
     apply(rename_tac ea e ca ab ac w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ea e ca ab ac w1 w2 a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. w2 = w' @ [x']")
     apply(rename_tac ea e ca ab ac w1 w2 a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ea e ca ab ac w1 w2 a list)(*strict*)
    apply(thin_tac "w2=a#list")
    apply(clarsimp)
    apply(rename_tac ea e ca ab ac w1 w' x')(*strict*)
    apply(erule_tac
      P="edge_pop e = ab @ [epda_box G]"
      in disjE)
     apply(rename_tac ea e ca ab ac w1 w' x')(*strict*)
     apply(clarsimp)
     apply(rename_tac ea e ca ab ac w1 w' x' a)(*strict*)
     apply(subgoal_tac "epda_box G \<in> set a")
      apply(rename_tac ea e ca ab ac w1 w' x' a)(*strict*)
      apply(force)
     apply(rename_tac ea e ca ab ac w1 w' x' a)(*strict*)
     apply(case_tac "ca")
      apply(rename_tac ea e ca ab ac w1 w' x' a)(*strict*)
      apply(clarsimp)
     apply(rename_tac ea e ca ab ac w1 w' x' a aa list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
      apply(rename_tac ea e ca ab ac w1 w' x' a aa list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac ea e ca ab ac w1 w' x' a aa list)(*strict*)
     apply(thin_tac "ca=aa#list")
     apply(clarsimp)
    apply(rename_tac ea e ca ab ac w1 w' x')(*strict*)
    apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w')(*strict*)
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w' x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1@[x]@w2=w'")
    apply(rename_tac ea \<gamma> e ca ab ac w' x)(*strict*)
    prefer 2
    apply (metis ConsApp in_set_conv_decomp)
   apply(rename_tac ea \<gamma> e ca ab ac w' x)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
   apply(rule conjI)
    apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
    apply(rule_tac
      A="set(edge_pop e)"
      in set_mp)
     apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
     apply(rule valid_epda_pop_in_gamma)
      apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
    apply(rule_tac
      t="edge_pop e"
      and s="edge_pop ea @ w1 @ x # w2 @ ca"
      in ssubst)
     apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac ea \<gamma> e ca ab ac x w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w1 w2)(*strict*)
   apply(case_tac "w2")
    apply(rename_tac ea \<gamma> e ca ab ac w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ea \<gamma> e ca ab ac w1 w2 a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. w2 = w' @ [x']")
    apply(rename_tac ea \<gamma> e ca ab ac w1 w2 a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac ea \<gamma> e ca ab ac w1 w2 a list)(*strict*)
   apply(thin_tac "w2=a#list")
   apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w1 w' x')(*strict*)
   apply(erule_tac
      P="edge_pop e = ab @ [epda_box G]"
      in disjE)
    apply(rename_tac ea \<gamma> e ca ab ac w1 w' x')(*strict*)
    apply(clarsimp)
    apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a)(*strict*)
    apply(subgoal_tac "epda_box G \<in> set a")
     apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a)(*strict*)
     apply(force)
    apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a)(*strict*)
    apply(case_tac "ca")
     apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a)(*strict*)
     apply(clarsimp)
    apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ea \<gamma> e ca ab ac w1 w' x' a aa list)(*strict*)
    apply(thin_tac "ca=aa#list")
    apply(clarsimp)
   apply(rename_tac ea \<gamma> e ca ab ac w1 w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(clarsimp)
   apply(rename_tac q w a)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(rule conjI)
    apply(rename_tac q w a)(*strict*)
    apply(simp add: option_to_set_def)
   apply(rename_tac q w a)(*strict*)
   apply(rule conjI)
    apply(rename_tac q w a)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(case_tac "a=epda_box G")
     apply(rename_tac q w a)(*strict*)
     apply(force)
    apply(rename_tac q w a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      A="set (w @ [a])"
      in set_mp)
     apply(rename_tac q w a)(*strict*)
     apply(rule F_EDPDA_RMPOE__states_on_gamma2)
      apply(rename_tac q w a)(*strict*)
      apply(force)
     apply(rename_tac q w a)(*strict*)
     apply(force)
    apply(rename_tac q w a)(*strict*)
    apply(force)
   apply(rename_tac q w a)(*strict*)
   apply(rule conjI)
    apply(rename_tac q w a)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(rename_tac q w a)(*strict*)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(subgoal_tac "epda_box G \<notin> set (w@[a])")
    apply(rename_tac q w a)(*strict*)
    apply(force)
   apply(rename_tac q w a)(*strict*)
   apply(rule F_EDPDA_RMPOE__states_do_not_consume_box)
    apply(rename_tac q w a)(*strict*)
    apply(force)
   apply(rename_tac q w a)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(clarsimp)
  apply(rename_tac q w a)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(rule conjI)
   apply(rename_tac q w a)(*strict*)
   apply(simp add: option_to_set_def)
  apply(rename_tac q w a)(*strict*)
  apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
  apply(case_tac "a=epda_box G")
   apply(rename_tac q w a)(*strict*)
   apply(force)
  apply(rename_tac q w a)(*strict*)
  apply(clarsimp)
  apply(rule F_EDPDA_RMPOE__states_on_gamma)
   apply(rename_tac q w a)(*strict*)
   apply(force)
  apply(rename_tac q w a)(*strict*)
  apply(force)
  done

theorem F_EDPDA_RMPOE_preserves_epda_no_nil_popping_edges: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epda_no_nil_popping_edges (F_EDPDA_RMPOE G)"
  apply(simp add: epda_no_nil_popping_edges_def F_EDPDA_RMPOE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(clarsimp)
  done

theorem F_EDPDA_RMPOE_enforces_epda_no_mass_popping_edges: "
  valid_epda G
  \<Longrightarrow> epda_no_mass_popping_edges (F_EDPDA_RMPOE G)"
  apply(simp add: epda_no_mass_popping_edges_def F_EDPDA_RMPOE_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(clarsimp)
  done

definition F_EDPDA_RMPOE__relation_LR_TSstructure :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<equiv>
  valid_epda G1
  \<and> G2 = F_EDPDA_RMPOE G1
  \<and> epda_no_nil_popping_edges G1"

definition F_EDPDA_RMPOE__configuration :: "
  'stack list
  \<Rightarrow> 'stack option
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf"
  where
    "F_EDPDA_RMPOE__configuration w x c \<equiv>
  \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c) w x,
  epdaS_conf_scheduler = epdaS_conf_scheduler c,
  epdaS_conf_stack = epdaS_conf_stack c\<rparr>"

definition F_EDPDA_RMPOE__relation_LR_configuration :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_EDPDA_RMPOE__configuration [] None c1"

definition F_EDPDA_RMPOE__relation_LR_initial_configuration :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_EDPDA_RMPOE__configuration [] None c1"

definition F_EDPDA_RMPOE__relation_LR_effect :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_effect G1 G2 w1 w2 \<equiv>
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EDPDA_RMPOE__relation_LR_TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_EDPDA_RMPOE_preserves_epda)
  done

definition F_EDPDA_RMPOE__nth_popping_edge :: "
  'state
  \<Rightarrow> 'stack list
  \<Rightarrow> nat
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label"
  where
    "F_EDPDA_RMPOE__nth_popping_edge q w n \<equiv>
  \<lparr>edge_src = cons_tuple3 q (take n w) None,
  edge_event = None,
  edge_pop = [w ! n],
  edge_push = [],
  edge_trg = cons_tuple3 q (take (Suc n) w) None\<rparr>"

definition F_EDPDA_RMPOE__relation_LR_step_simulation_pre :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation"
  where
    "F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c1 \<equiv>
  let
    w = F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c1) e
  in
    (\<lambda>n.
      if n < length w
      then Some (pair
              (if n = 0
              then None
              else Some (F_EDPDA_RMPOE__nth_popping_edge (edge_src e) w (n - 1)))
              \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) (take n w) None,
              epdaS_conf_scheduler = epdaS_conf_scheduler c1,
              epdaS_conf_stack = drop n (epdaS_conf_stack c1)\<rparr>)
      else None)"

lemma common_prefixes_nonempty: "
  \<exists>x. x \<in> common_prefixes w v"
  apply(rule_tac
      x="[]"
      in exI)
  apply(simp add: common_prefixes_def)
  apply(rule_tac
      x="0"
      in exI)
  apply(clarsimp)
  done

lemma common_prefixes_prefix2: "
  x \<in> common_prefixes w v
  \<Longrightarrow> prefix x v"
  apply(simp add: common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(simp add: prefix_def)
  apply(rule_tac
      x="drop n v"
      in exI)
  apply (metis append_take_drop_id)
  done

lemma common_prefixes_prefix1: "
  x \<in> common_prefixes w v
  \<Longrightarrow> prefix x w"
  apply(simp add: common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(simp add: prefix_def)
  apply(rule_tac
      x="drop n w"
      in exI)
  apply (metis append_take_drop_id)
  done

lemma common_prefixes_related: "
  x \<in> common_prefixes w v
  \<Longrightarrow> y \<in> common_prefixes w v
  \<Longrightarrow> prefix x y \<or> prefix y x"
  apply(subgoal_tac "prefix x v")
   prefer 2
   apply (metis common_prefixes_prefix2)
  apply(subgoal_tac "prefix y v")
   prefer 2
   apply (metis common_prefixes_prefix2)
  apply (metis nat_le_linear prefix_common_max)
  done

lemma longest_common_prefix_exists: "
  \<exists>x \<in> common_prefixes w v. \<forall>y \<in> common_prefixes w v. length y \<le> length x"
  apply(subgoal_tac "\<exists>x. SSP x \<and> length x = Max {length x| x. SSP x}" for SSP)
   prefer 2
   apply(rule_tac
      P="\<lambda>x. x \<in> common_prefixes w v"
      in Max_Sat)
    apply(subgoal_tac "\<exists>x. x \<in> common_prefixes w v")
     apply(force)
    apply(rule common_prefixes_nonempty)
   apply(rule_tac
      B="length`(prefix_closure {v})"
      in finite_subset)
    apply(clarsimp)
    apply(rename_tac xa)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="xa"
      in bexI)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(simp add: prefix_closure_def)
    apply (metis common_prefixes_prefix2)
   apply(rule finite_imageI)
   apply(subgoal_tac "card (prefix_closure{v}) = Suc (length v)")
    prefer 2
    apply (metis tmp00xx)
   apply (metis Suc_not_Zero card_eq_0_iff tmp00xx)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x="x"
      in bexI)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(subgoal_tac "prefix x y \<or> prefix y x")
   apply(rename_tac x y)(*strict*)
   prefer 2
   apply(rule common_prefixes_related)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(rename_tac x y)(*strict*)
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(erule disjE)
   apply(rename_tac x y)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(subgoal_tac "length (x@c) \<le> Max {y. \<exists>x. y=length x \<and> x \<in> common_prefixes w v}")
    apply(rename_tac x c)(*strict*)
    apply(force)
   apply(rename_tac x c)(*strict*)
   apply(thin_tac "length x=Max {y. \<exists>x. y=length x \<and> x \<in> common_prefixes w v}")
   apply(thin_tac "x \<in> common_prefixes w v")
   apply(rule Max_ge)
    apply(rename_tac x c)(*strict*)
    apply(rule_tac
      B="length`(prefix_closure {v})"
      in finite_subset)
     apply(rename_tac x c)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c xb)(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="xb"
      in bexI)
      apply(rename_tac x c xb)(*strict*)
      apply(force)
     apply(rename_tac x c xb)(*strict*)
     apply(simp add: prefix_closure_def)
     apply (metis common_prefixes_prefix2)
    apply(rename_tac x c)(*strict*)
    apply(rule finite_imageI)
    apply(subgoal_tac "card (prefix_closure{v}) = Suc (length v)")
     apply(rename_tac x c)(*strict*)
     prefer 2
     apply (metis tmp00xx)
    apply(rename_tac x c)(*strict*)
    apply (metis Suc_not_Zero card_eq_0_iff tmp00xx)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(rule Max_ge)
   apply(rename_tac x y)(*strict*)
   apply(rule_tac
      B="length`(prefix_closure {v})"
      in finite_subset)
    apply(rename_tac x y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x y xb)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="xb"
      in bexI)
     apply(rename_tac x y xb)(*strict*)
     apply(force)
    apply(rename_tac x y xb)(*strict*)
    apply(simp add: prefix_closure_def)
    apply (metis common_prefixes_prefix2)
   apply(rename_tac x y)(*strict*)
   apply(rule finite_imageI)
   apply(subgoal_tac "card (prefix_closure{v}) = Suc (length v)")
    apply(rename_tac x y)(*strict*)
    prefer 2
    apply (metis tmp00xx)
   apply(rename_tac x y)(*strict*)
   apply (metis Suc_not_Zero card_eq_0_iff tmp00xx)
  apply(rename_tac x y)(*strict*)
  apply(force)
  done

lemma longest_common_prefix_with_prefix: "
  prefix w v
  \<Longrightarrow> longest_common_prefix w v = w"
  apply(simp add: prefix_def)
  apply(simp add: longest_common_prefix_def longest_def common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      a="w"
      in HOL.theI2)
    apply(rename_tac c)(*strict*)
    apply(rule conjI)
     apply(rename_tac c)(*strict*)
     apply (metis append_Nil2 butn_def butn_zero diff_self_eq_0 minus_nat.diff_0 take_0)
    apply(rename_tac c)(*strict*)
    apply(clarsimp)
   apply(rename_tac c x)(*strict*)
   apply(clarsimp)
   apply(rename_tac c n)(*strict*)
   apply(erule_tac
      x="w"
      in allE)
   apply(clarsimp)
   apply(erule impE)
    apply(rename_tac c n)(*strict*)
    apply(rule_tac
      x="length w"
      in exI)
    apply(force)
   apply(rename_tac c n)(*strict*)
   apply(force)
  apply(rename_tac c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac c n)(*strict*)
  apply(erule_tac
      x="w"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac c n)(*strict*)
   apply(rule_tac
      x="length w"
      in exI)
   apply(force)
  apply(rename_tac c n)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE__pop_components_longest_exists: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> \<exists>e'. e' \<in> epda_delta G \<and> edge_src e' = edge_src e \<and> (\<forall>e'' \<in> epda_delta G. edge_src e'' = edge_src e' \<longrightarrow> length (edge_pop e'') \<le> length (edge_pop e'))"
  apply(subgoal_tac "\<exists>x. (\<lambda>x. (\<exists>e' \<in> epda_delta G. edge_src e=edge_src e' \<and> edge_pop e'=x)) x \<and> length x = Max {length x| x. SSP x}" for SSP)
   prefer 2
   apply(rule Max_Sat)
    apply(force)
   apply(rule_tac
      B="(length ` (((edge_pop) ` (epda_delta G))))"
      in finite_subset)
    apply(force)
   apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac e')(*strict*)
  apply(rule_tac
      x="e'"
      in exI)
  apply(clarsimp)
  apply(rename_tac e' e'')(*strict*)
  apply(rule Max_ge)
   apply(rename_tac e' e'')(*strict*)
   apply(rule_tac
      B="(length ` (((edge_pop) ` (epda_delta G))))"
      in finite_subset)
    apply(rename_tac e' e'')(*strict*)
    apply(force)
   apply(rename_tac e' e'')(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac e' e'')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="edge_pop e''"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="e''"
      in bexI)
   apply(rename_tac e' e'')(*strict*)
   apply(clarsimp)
  apply(rename_tac e' e'')(*strict*)
  apply(force)
  done

lemma longest_common_prefix_prefix_upper1: "
  longest_common_prefix w v \<sqsubseteq> w"
  apply(simp add: longest_common_prefix_def)
  apply(subgoal_tac "\<exists>x \<in> common_prefixes w v. \<forall>y \<in> common_prefixes w v. length y\<le>length x")
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_def)
  apply(simp add: longest_def)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix x xa \<or> prefix xa x")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule common_prefixes_related)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      and P="\<lambda>y. length y \<le> length x"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(erule_tac
      x="x"
      in ballE)
     apply(rename_tac x xa)(*strict*)
     apply(simp add: prefix_def)
     apply (metis append_eq_appendI length_append_equal)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(fold prefix_def)
  apply (metis common_prefixes_prefix1)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_exists: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> w \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> prefix (edge_pop e) w
  \<Longrightarrow> \<exists>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) \<and> (\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) . length (longest_common_prefix w' w) \<le> length wa)"
  apply(subgoal_tac "finite ({y. \<exists>x. y=(length x) \<and> (x \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)))})")
   prefer 2
   apply(rule_tac
      B="length ` (prefix_closure((edge_pop) ` (epda_delta G)))"
      in finite_subset)
    apply(clarsimp)
    apply(rename_tac wa)(*strict*)
    apply(simp add: restrict_to_extensions_def F_EDPDA_RMPOE__pop_components_def prefix_closure_def)
    apply(clarsimp)
    apply(rename_tac ea)(*strict*)
    apply(rule inMap)
    apply(clarsimp)
    apply(rule_tac
      x="longest_common_prefix (edge_pop ea) w"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="edge_pop ea"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>x \<in> common_prefixes (edge_pop ea) w. \<forall>y \<in> common_prefixes (edge_pop ea) w. length y\<le>length x")
     apply(rename_tac ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac ea x)(*strict*)
     apply(rule longest_common_prefix_prefix_upper1)
    apply(rename_tac ea)(*strict*)
    apply(rule longest_common_prefix_exists)
   apply(rule finite_imageI)
   apply(rule_tac
      X="epda_gamma G"
      in prefix_closure_preserves_finiteness)
     apply(simp add: valid_epda_def)
    apply(rule finite_imageI)
    apply(simp add: valid_epda_def)
   apply(simp add: kleene_star_def)
   apply(clarsimp)
   apply(rename_tac xa xb)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G xa")
    apply(rename_tac xa xb)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(erule_tac
      P="edge_pop xa = a @ [epda_box G]"
      in disjE)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      P="xb = epda_box G"
      in disjE)
      apply(rename_tac xa xb a aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa a aa)(*strict*)
      apply(simp add: valid_epda_def)
     apply(rename_tac xa xb a aa)(*strict*)
     apply(force)
    apply(rename_tac xa xb a aa)(*strict*)
    apply(force)
   apply(rename_tac xa xb)(*strict*)
   apply(simp add: valid_epda_def)
  apply(subgoal_tac "\<exists>wa. (\<lambda>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e))) wa \<and> length wa = Max {length x| x. SSP x}" for SSP)
   prefer 2
   apply(rule Max_Sat)
    apply(rule_tac
      x="length(edge_pop e)"
      in elem_not_empty)
    apply(clarsimp)
    apply(rule_tac
      x="edge_pop e"
      in exI)
    apply(clarsimp)
    apply(rule inMap)
    apply(rule_tac
      x="edge_pop e"
      in bexI)
     apply (metis longest_common_prefix_with_prefix)
    apply(simp add: restrict_to_extensions_def)
    apply(rule conjI)
     apply(simp add: F_EDPDA_RMPOE__pop_components_def)
     apply(rule_tac
      x="e"
      in exI)
     apply(force)
    apply(simp add: prefix_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(rule_tac
      x="longest_common_prefix waa w"
      in exI)
  apply(rule conjI)
   apply(rename_tac waa)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="waa"
      in bexI)
    apply(rename_tac waa)(*strict*)
    apply(force)
   apply(rename_tac waa)(*strict*)
   apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa w')(*strict*)
  apply(rule Max_ge)
   apply(rename_tac waa w')(*strict*)
   apply(force)
  apply(rename_tac waa w')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="longest_common_prefix w' w"
      in exI)
  apply(clarsimp)
  done

lemma longest_common_prefix_contained: "
  longest_common_prefix wa w \<in> common_prefixes wa w"
  apply(simp add: longest_common_prefix_def)
  apply(subgoal_tac "\<exists>x \<in> common_prefixes wa w. \<forall>y \<in> common_prefixes wa w. length y\<le>length x")
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: longest_def)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix x xa \<or> prefix xa x")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule_tac
      w="wa"
      and v="w"
      in common_prefixes_related)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. length x \<le> length xa"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length xa \<le> length x"
      in ballE)
     apply(rename_tac x xa)(*strict*)
     apply(clarsimp)
     apply (metis le_refl mutual_prefix_implies_equality2)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_bound_lower: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> w \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> prefix (edge_pop e) w
  \<Longrightarrow> prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G w e)"
  apply(simp add: F_EDPDA_RMPOE_longest_popping_sequence_def longest_popping_sequence_def longest_def)
  apply(subgoal_tac "\<exists>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) \<and> (\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)). length (longest_common_prefix w' w) \<le> length wa) ")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_exists)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(rule_tac
      a="longest_common_prefix waa w"
      in HOL.theI2)
    apply(rename_tac waa)(*strict*)
    apply(rule conjI)
     apply(rename_tac waa)(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="waa"
      in bexI)
      apply(rename_tac waa)(*strict*)
      apply(force)
     apply(rename_tac waa)(*strict*)
     apply(clarsimp)
    apply(rename_tac waa)(*strict*)
    apply(force)
   apply(rename_tac waa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac waa wa)(*strict*)
   apply(simp add: restrict_to_extensions_def)
   apply(clarsimp)
   apply(erule_tac
      x="waa"
      and P="\<lambda>waa. waa \<in> F_EDPDA_RMPOE__pop_components G (edge_src e) \<and> edge_pop e \<sqsubseteq> waa \<longrightarrow> length (longest_common_prefix waa w) \<le> length (longest_common_prefix wa w)"
      in allE)
   apply(rename_tac waa wa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="wa"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "prefix (longest_common_prefix wa w) w")
    apply(rename_tac waa wa)(*strict*)
    apply(subgoal_tac "prefix (longest_common_prefix waa w) w")
     apply(rename_tac waa wa)(*strict*)
     apply (metis order_eq_refl mutual_prefix_implies_equality2 prefix_common_max)
    apply(rename_tac waa wa)(*strict*)
    apply (metis longest_common_prefix_contained common_prefixes_prefix2)
   apply(rename_tac waa wa)(*strict*)
   apply (metis longest_common_prefix_contained common_prefixes_prefix2)
  apply(rename_tac waa x)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa wa)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> common_prefixes wa w. \<forall>y \<in> common_prefixes wa w. length y\<le>length x")
   apply(rename_tac waa wa)(*strict*)
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(rename_tac waa wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa wa x)(*strict*)
  apply(simp (no_asm) add: longest_common_prefix_def longest_def)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac waa wa x)(*strict*)
    apply(clarsimp)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(subgoal_tac "prefix x xa \<or> prefix xa x")
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(rule common_prefixes_related)
     apply(rename_tac waa wa x xa)(*strict*)
     apply(force)
    apply(rename_tac waa wa x xa)(*strict*)
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length xa \<le> length x"
      in ballE)
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. length x \<le> length xa"
      in ballE)
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(clarsimp)
   apply (metis append_Nil2 length_append_equal prefix_def)
  apply(rename_tac waa wa x xa)(*strict*)
  apply(clarsimp)
  apply(simp add: common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac waa wa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>w'. length (longest_common_prefix w' w) \<le> length (longest_common_prefix waa w)"
      in ballE)
   apply(rename_tac waa wa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa wa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      in ballE)
   apply(rename_tac waa wa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa wa n na)(*strict*)
  apply(subgoal_tac "longest_common_prefix (edge_pop e) w=edge_pop e")
   apply(rename_tac waa wa n na)(*strict*)
   apply(simp add: prefix_def)
   apply(simp add: restrict_to_extensions_def)
   apply(clarsimp)
   apply(rename_tac waa w n na c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n na c ca cb)(*strict*)
   apply (metis take_all take_append take_append_prime)
  apply(rename_tac waa wa n na)(*strict*)
  apply (metis longest_common_prefix_with_prefix)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_bound_upper: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> w \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> prefix (edge_pop e) w
  \<Longrightarrow> prefix (F_EDPDA_RMPOE_longest_popping_sequence G w e) w"
  apply(simp add: F_EDPDA_RMPOE_longest_popping_sequence_def longest_popping_sequence_def longest_def)
  apply(subgoal_tac "\<exists>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) \<and> (\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)). length (longest_common_prefix w' w) \<le> length wa) ")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_exists)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(rule_tac
      a="longest_common_prefix waa w"
      in HOL.theI2)
    apply(rename_tac waa)(*strict*)
    apply(rule conjI)
     apply(rename_tac waa)(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="waa"
      in bexI)
      apply(rename_tac waa)(*strict*)
      apply(force)
     apply(rename_tac waa)(*strict*)
     apply(clarsimp)
    apply(rename_tac waa)(*strict*)
    apply(force)
   apply(rename_tac waa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac waa wa)(*strict*)
   apply(simp add: restrict_to_extensions_def)
   apply(clarsimp)
   apply(erule_tac
      x="waa"
      and P="\<lambda>waa. waa \<in> F_EDPDA_RMPOE__pop_components G (edge_src e) \<and> edge_pop e \<sqsubseteq> waa \<longrightarrow> length (longest_common_prefix waa w) \<le> length (longest_common_prefix wa w)"
      in allE)
   apply(rename_tac waa wa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="wa"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "prefix (longest_common_prefix wa w) w")
    apply(rename_tac waa wa)(*strict*)
    apply(subgoal_tac "prefix (longest_common_prefix waa w) w")
     apply(rename_tac waa wa)(*strict*)
     apply (metis order_eq_refl mutual_prefix_implies_equality2 prefix_common_max)
    apply(rename_tac waa wa)(*strict*)
    apply (metis longest_common_prefix_contained common_prefixes_prefix2)
   apply(rename_tac waa wa)(*strict*)
   apply (metis longest_common_prefix_contained common_prefixes_prefix2)
  apply(rename_tac waa x)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa wa)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> common_prefixes wa w. \<forall>y \<in> common_prefixes wa w. length y\<le>length x")
   apply(rename_tac waa wa)(*strict*)
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(rename_tac waa wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa wa x)(*strict*)
  apply(simp (no_asm) add: longest_common_prefix_def longest_def)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac waa wa x)(*strict*)
    apply(clarsimp)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(subgoal_tac "prefix x xa \<or> prefix xa x")
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(rule common_prefixes_related)
     apply(rename_tac waa wa x xa)(*strict*)
     apply(force)
    apply(rename_tac waa wa x xa)(*strict*)
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      and P="\<lambda>xa. length xa \<le> length x"
      in ballE)
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. length x \<le> length xa"
      in ballE)
    apply(rename_tac waa wa x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa wa x xa)(*strict*)
   apply(clarsimp)
   apply (metis append_Nil2 length_append_equal prefix_def)
  apply(rename_tac waa wa x xa)(*strict*)
  apply(clarsimp)
  apply(simp add: common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac waa wa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>w'. length (longest_common_prefix w' w) \<le> length (longest_common_prefix waa w)"
      in ballE)
   apply(rename_tac waa wa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa wa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      in ballE)
   apply(rename_tac waa wa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa wa n na)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac waa w n na c)(*strict*)
  apply (metis append_take_drop_id take_append)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_realizer: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> w \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> prefix (edge_pop e) w
  \<Longrightarrow> \<exists>e' \<in> epda_delta G. edge_src e' = edge_src e \<and> prefix (F_EDPDA_RMPOE_longest_popping_sequence G w e) (edge_pop e')"
  apply(simp add: F_EDPDA_RMPOE_longest_popping_sequence_def longest_popping_sequence_def longest_def)
  apply(subgoal_tac "\<exists>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa w) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) \<and> (\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)). length (longest_common_prefix w' w) \<le> length wa) ")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_exists)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(rule_tac
      a="longest_common_prefix waa w"
      in HOL.theI2)
    apply(rename_tac waa)(*strict*)
    apply(rule conjI)
     apply(rename_tac waa)(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="waa"
      in bexI)
      apply(rename_tac waa)(*strict*)
      apply(force)
     apply(rename_tac waa)(*strict*)
     apply(clarsimp)
    apply(rename_tac waa)(*strict*)
    apply(force)
   apply(rename_tac waa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac waa xa)(*strict*)
   apply(simp add: restrict_to_extensions_def)
   apply(clarsimp)
   apply(erule_tac
      x="waa"
      and P="\<lambda>waa. waa \<in> F_EDPDA_RMPOE__pop_components G (edge_src e) \<and> edge_pop e \<sqsubseteq> waa \<longrightarrow> length (longest_common_prefix waa w) \<le> length (longest_common_prefix xa w)"
      in allE)
   apply(rename_tac waa xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="xa"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "prefix (longest_common_prefix xa w) w")
    apply(rename_tac waa xa)(*strict*)
    apply(subgoal_tac "prefix (longest_common_prefix waa w) w")
     apply(rename_tac waa xa)(*strict*)
     apply (metis order_eq_refl mutual_prefix_implies_equality2 prefix_common_max)
    apply(rename_tac waa xa)(*strict*)
    apply (metis longest_common_prefix_contained common_prefixes_prefix2)
   apply(rename_tac waa xa)(*strict*)
   apply (metis longest_common_prefix_contained common_prefixes_prefix2)
  apply(rename_tac waa x)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa xa)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> common_prefixes xa w. \<forall>y \<in> common_prefixes xa w. length y\<le>length x")
   apply(rename_tac waa xa)(*strict*)
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(rename_tac waa xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac waa xa x)(*strict*)
  apply(simp (no_asm) add: longest_common_prefix_def longest_def)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac waa xa x)(*strict*)
    apply(clarsimp)
   apply(rename_tac waa xa x xb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix x xb \<or> prefix xb x")
    apply(rename_tac waa xa x xb)(*strict*)
    prefer 2
    apply(rule common_prefixes_related)
     apply(rename_tac waa xa x xb)(*strict*)
     apply(force)
    apply(rename_tac waa xa x xb)(*strict*)
    apply(force)
   apply(rename_tac waa xa x xb)(*strict*)
   apply(erule_tac
      x="xb"
      and P="\<lambda>xb. length xb \<le> length x"
      in ballE)
    apply(rename_tac waa xa x xb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa xa x xb)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. length x \<le> length xb"
      in ballE)
    apply(rename_tac waa xa x xb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac waa xa x xb)(*strict*)
   apply(clarsimp)
   apply (metis append_Nil2 length_append_equal prefix_def)
  apply(rename_tac waa xa x xb)(*strict*)
  apply(clarsimp)
  apply(simp add: common_prefixes_def)
  apply(clarsimp)
  apply(rename_tac waa xa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>w'. length (longest_common_prefix w' w) \<le> length (longest_common_prefix waa w)"
      in ballE)
   apply(rename_tac waa xa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa xa n na)(*strict*)
  apply(erule_tac
      x="edge_pop e"
      in ballE)
   apply(rename_tac waa xa n na)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def)
   apply(simp add: prefix_def)
   apply(simp add: F_EDPDA_RMPOE__pop_components_def)
  apply(rename_tac waa xa n na)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac waa xa n na c)(*strict*)
  apply(simp add: restrict_to_extensions_def F_EDPDA_RMPOE__pop_components_def)
  apply(clarsimp)
  apply(rename_tac n na c ea eaa)(*strict*)
  apply(rule_tac
      x="eaa"
      in bexI)
   apply(rename_tac n na c ea eaa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n na c ea eaa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="drop na (edge_pop eaa)"
      in exI)
  apply(force)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> epdaS.derivation (F_EDPDA_RMPOE G) (F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c)"
  apply(simp add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
   apply(simp add: Let_def)
   apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
    apply(clarsimp)
    apply(simp add: epda_no_nil_popping_edges_def)
    apply(simp add: prefix_def)
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
  apply(simp add: Let_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE__nth_popping_edge_def)
  apply(simp only: epdaS_step_relation_def)
  apply(rule conjI)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat w)(*strict*)
   apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ w) e)")
    apply(rename_tac nat w)(*strict*)
    prefer 2
    apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: epdaS_step_relation_def prefix_def)
   apply(rename_tac nat w)(*strict*)
   apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ w) e) (edge_pop e @ w)")
    apply(rename_tac nat w)(*strict*)
    prefer 2
    apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: epdaS_step_relation_def prefix_def)
   apply(rename_tac nat w)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac nat w ca caa)(*strict*)
   apply(subgoal_tac "w=ca@caa")
    apply(rename_tac nat w ca caa)(*strict*)
    prefer 2
    apply (metis append_linj concat_asso)
   apply(rename_tac nat w ca caa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat ca caa)(*strict*)
   apply(rule_tac
      t="F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e"
      and s="edge_pop e @ ca"
      in ssubst)
    apply(rename_tac nat ca caa)(*strict*)
    apply(force)
   apply(rename_tac nat ca caa)(*strict*)
   apply(rule F_DPDARMPE__help1)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ w) e)")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ w) e) (edge_pop e @ w)")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
  apply(rename_tac nat w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac nat w ca caa)(*strict*)
  apply(subgoal_tac "w=ca@caa")
   apply(rename_tac nat w ca caa)(*strict*)
   prefer 2
   apply (metis append_linj concat_asso)
  apply(rename_tac nat w ca caa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat ca caa)(*strict*)
  apply(simp add: F_EDPDA_RMPOE_def)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
  apply(rule conjI)
   apply(rename_tac nat ca caa)(*strict*)
   apply (metis Suc_lessD rotate_simps take_Suc_conv_app_nth)
  apply(rename_tac nat ca caa)(*strict*)
  apply(subgoal_tac "\<exists>e' \<in> epda_delta G. edge_src e'=edge_src e \<and> prefix(F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e)(edge_pop e')")
   apply(rename_tac nat ca caa)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_realizer)
      apply(rename_tac nat ca caa)(*strict*)
      apply(force)
     apply(rename_tac nat ca caa)(*strict*)
     apply(force)
    apply(rename_tac nat ca caa)(*strict*)
    apply(force)
   apply(rename_tac nat ca caa)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
  apply(rename_tac nat ca caa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat ca caa e')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac nat ca caa e' cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat ca caa e' cb)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
   apply(rule_tac
      x="e'"
      in exI)
   apply(clarsimp)
   apply(simp add: strict_prefix_def prefix_def)
   apply(rule_tac
      x="drop nat (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e)@cb"
      in exI)
   apply(clarsimp)
   apply (metis append_assoc append_take_drop_id)
  apply(rename_tac nat ca caa e' cb)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(rule disjI1)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
  apply(rule_tac
      x="e'"
      in exI)
  apply(clarsimp)
  apply(simp add: strict_prefix_def)
  apply(rule_tac
      x="drop (Suc nat) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e)@cb"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="take nat (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e) @ F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e ! nat # drop (Suc nat) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e) @ cb"
      and s="(take nat (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e) @ [F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e ! nat]) @ drop (Suc nat) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e) @ cb"
      in ssubst)
   apply(rename_tac nat ca caa e' cb)(*strict*)
   apply(force)
  apply(rename_tac nat ca caa e' cb)(*strict*)
  apply(rule_tac
      t="take nat (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e) @ [F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e ! nat]"
      and s="take (Suc nat) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ caa) e)"
      in ssubst)
   apply(rename_tac nat ca caa e' cb)(*strict*)
   apply (metis Suc_lessD rotate_simps take_Suc_conv_app_nth)
  apply(rename_tac nat ca caa e' cb)(*strict*)
  apply (metis append_assoc append_take_drop_id)
  done

definition F_EDPDA_RMPOE__relation_LR_step_simulation_mid :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation"
  where
    "F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c1 \<equiv>
  let
    w = F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c1) e
  in
    if suffix w [epda_box G]
    then der2
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) (butlast w) None,
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word (butlast w) (epdaS_conf_stack c1))\<rparr>
            \<lparr>edge_src = cons_tuple3 (epdaS_conf_state c1) (butlast w) None,
            edge_event = None,
            edge_pop = [epda_box G],
            edge_push = [epda_box G],
          edge_trg = cons_tuple3 (epdaS_conf_state c1) (butlast w) (Some (epda_box G))\<rparr> \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) (butlast w) (Some (epda_box G)),
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word (butlast w) (epdaS_conf_stack c1))\<rparr>
    else der3
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) (butlast w) None,
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word (butlast w) (epdaS_conf_stack c1))\<rparr>
            \<lparr>edge_src = cons_tuple3 (epdaS_conf_state c1) (butlast w) None,
            edge_event = None,
            edge_pop = [last w],
            edge_push = [],
            edge_trg = cons_tuple3 (epdaS_conf_state c1) w None\<rparr>
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) w None,
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word w (epdaS_conf_stack c1))\<rparr>
            \<lparr>edge_src = cons_tuple3 (epdaS_conf_state c1) w None,
            edge_event = None,
            edge_pop = [hd (the (left_quotient_word w (epdaS_conf_stack c1)))],
            edge_push = [hd (the (left_quotient_word w (epdaS_conf_stack c1)))],
            edge_trg = cons_tuple3 (epdaS_conf_state c1) w (Some (hd (the (left_quotient_word w (epdaS_conf_stack c1)))))\<rparr>
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) w (Some (hd (the (left_quotient_word w (epdaS_conf_stack c1))))),
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word w (epdaS_conf_stack c1))\<rparr>"

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_mid_derivation_maximum_of_domain: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> maximum_of_domain (F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c) (if (suffix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) ([epda_box G])) then 1 else 2)"
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def)
  apply(simp add: Let_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rule der2_maximum_of_domain)
  apply(clarsimp)
  apply(rule der3_maximum_of_domain2)
  done

lemma longest_common_prefix_lower_bound: "
  prefix w (longest_common_prefix (w @ v1) (w @ v2))"
  apply(subgoal_tac "\<exists>x \<in> common_prefixes (w @ v1) (w @ v2). \<forall>y \<in> common_prefixes (w @ v1) (w @ v2). length y\<le>length x")
   prefer 2
   apply(rule longest_common_prefix_exists)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: longest_common_prefix_def longest_def)
  apply(rule_tac
      t="(THE wa. wa \<in> common_prefixes (w @ v1) (w @ v2) \<and> (\<forall>w' \<in> common_prefixes (w @ v1) (w @ v2). length w' \<le> length wa))"
      and s="x"
      in ssubst)
   apply(rename_tac x)(*strict*)
   defer
   apply(simp add: common_prefixes_def prefix_def)
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(erule_tac
      x="w"
      in allE)
   apply(erule impE)
    apply(rename_tac n)(*strict*)
    apply(rule_tac
      x="length w"
      in exI)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      a="x"
      in HOL.theI2)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix x xa \<or> prefix xa x")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule common_prefixes_related)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      and P="\<lambda>y. length y \<le> length x"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(erule_tac
      x="x"
      in ballE)
     apply(rename_tac x xa)(*strict*)
     apply(simp add: prefix_def)
     apply (metis append_eq_appendI length_append_equal)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix x xa \<or> prefix xa x")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(rule common_prefixes_related)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x="xa"
      and P="\<lambda>y. length y \<le> length x"
      in ballE)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(simp add: prefix_def)
    apply (metis append_eq_appendI length_append_equal)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_bound_lower2: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> w @ v2 \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> edge_src e' = edge_src e
  \<Longrightarrow> e' \<in> epda_delta G
  \<Longrightarrow> w @ v1 = edge_pop e'
  \<Longrightarrow> x = w @ v2
  \<Longrightarrow> prefix (edge_pop e) (w @ v2)
  \<Longrightarrow> prefix w (F_EDPDA_RMPOE_longest_popping_sequence G x e)"
  apply(simp add: F_EDPDA_RMPOE_longest_popping_sequence_def longest_popping_sequence_def longest_def)
  apply(subgoal_tac "\<exists>wa. wa \<in> (\<lambda>wa. longest_common_prefix wa (w@v2)) ` restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)) \<and> (\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)). length (longest_common_prefix w' (w@v2)) \<le> length wa) ")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_exists)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac waa)(*strict*)
  apply(rule_tac
      a="longest_common_prefix waa (w@v2)"
      in HOL.theI2)
    apply(rename_tac waa)(*strict*)
    apply(rule conjI)
     apply(rename_tac waa)(*strict*)
     apply(rule inMap)
     apply(rule_tac
      x="waa"
      in bexI)
      apply(rename_tac waa)(*strict*)
      apply(force)
     apply(rename_tac waa)(*strict*)
     apply(clarsimp)
    apply(rename_tac waa)(*strict*)
    apply(force)
   apply(rename_tac waa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac waa wa)(*strict*)
   apply(simp add: restrict_to_extensions_def)
   apply(clarsimp)
   apply(erule_tac
      x="waa"
      and P="\<lambda>waa. waa \<in> F_EDPDA_RMPOE__pop_components G (edge_src e) \<and> edge_pop e \<sqsubseteq> waa \<longrightarrow> length (longest_common_prefix waa (w @ v2)) \<le> length (longest_common_prefix wa (w @ v2))"
      in allE)
   apply(rename_tac waa wa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="wa"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "prefix (longest_common_prefix wa (w@v2)) (w@v2)")
    apply(rename_tac waa wa)(*strict*)
    apply(subgoal_tac "prefix (longest_common_prefix waa (w@v2)) (w@v2)")
     apply(rename_tac waa wa)(*strict*)
     apply (metis order_eq_refl mutual_prefix_implies_equality2 prefix_common_max)
    apply(rename_tac waa wa)(*strict*)
    apply (metis longest_common_prefix_contained common_prefixes_prefix2)
   apply(rename_tac waa wa)(*strict*)
   apply (metis longest_common_prefix_contained common_prefixes_prefix2)
  apply(rename_tac waa x)(*strict*)
  apply(thin_tac "\<forall>w' \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e)). length (longest_common_prefix w' (w @ v2)) \<le> length (longest_common_prefix waa (w @ v2))")
  apply(rename_tac waa x)(*strict*)
  apply(thin_tac "waa \<in> restrict_to_extensions (edge_pop e) (F_EDPDA_RMPOE__pop_components G (edge_src e))")
  apply(subgoal_tac "prefix x (w@v2)")
   apply(rename_tac waa x)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac wa)(*strict*)
   apply (metis longest_common_prefix_contained common_prefixes_prefix2)
  apply(rename_tac waa x)(*strict*)
  apply(subgoal_tac "length w \<le> length x")
   apply(rename_tac waa x)(*strict*)
   apply (metis prefix_append prefix_common_max)
  apply(rename_tac waa x)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa)(*strict*)
  apply(erule_tac
      x="edge_pop e'"
      in ballE)
   apply(rename_tac wa)(*strict*)
   prefer 2
   apply(simp add: restrict_to_extensions_def F_EDPDA_RMPOE__pop_components_def)
   apply(clarsimp)
   apply(rename_tac ea)(*strict*)
   apply(erule disjE)
    apply(rename_tac ea)(*strict*)
    apply(force)
   apply(rename_tac ea)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ea c ca cb)(*strict*)
   apply(subgoal_tac "prefix (longest_common_prefix (edge_pop ea) (w @ v2)) (edge_pop ea)")
    apply(rename_tac ea c ca cb)(*strict*)
    prefer 2
    apply (metis longest_common_prefix_prefix_upper1)
   apply(rename_tac ea c ca cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ea c ca cb cc)(*strict*)
   apply(subgoal_tac "prefix w (longest_common_prefix (edge_pop ea) (w @ v2)) \<or> prefix (longest_common_prefix (edge_pop ea) (w @ v2)) w")
    apply(rename_tac ea c ca cb cc)(*strict*)
    prefer 2
    apply(metis mutual_prefix_prefix)
   apply(rename_tac ea c ca cb cc)(*strict*)
   apply(erule disjE)
    apply(rename_tac ea c ca cb cc)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac ea c ca cb cc "cd")(*strict*)
    apply (metis drop_length_append)
   apply(rename_tac ea c ca cb cc)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ea c ca cb cc "cd")(*strict*)
   apply(case_tac ea)
   apply(rename_tac ea c ca cb cc "cd" edge_srca edge_event edge_popa edge_push edge_trg)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc "cd" edge_event edge_push edge_trg)(*strict*)
   apply(case_tac e)
   apply(rename_tac c ca cb cc "cd" edge_event edge_push edge_trg edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(subgoal_tac "ca=cd@v2")
    apply(rename_tac c ca cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    prefer 2
    apply (metis append_assoc append_linj)
   apply(rename_tac c ca cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(subgoal_tac "prefix w (edge_popa) \<or> prefix (edge_popa) w")
    apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    prefer 2
    apply(metis mutual_prefix_prefix)
   apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(erule disjE)
    apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_pusha edge_trga ca)(*strict*)
   apply(subgoal_tac "prefix w (longest_common_prefix (w @ SSv1) (w @ SSv2))" for SSv1 SSv2)
    apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_pusha edge_trga ca)(*strict*)
    prefer 2
    apply(rule_tac
      ?v1.0="ca@cb"
      and ?v2.0="ca@c"
      in longest_common_prefix_lower_bound)
   apply(rename_tac c cb cc "cd" edge_event edge_push edge_trg edge_eventa edge_pusha edge_trga ca)(*strict*)
   apply(simp add: prefix_def)
   apply (metis drop_length_append)
  apply(rename_tac wa)(*strict*)
  apply(rule_tac
      j="length (longest_common_prefix (edge_pop e') (w @ v2))"
      in le_trans)
   apply(rename_tac wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac wa)(*strict*)
  apply(thin_tac "length (longest_common_prefix (edge_pop e') (w @ v2)) \<le> length (longest_common_prefix wa (w @ v2))")
  apply(rename_tac wa)(*strict*)
  apply(rule_tac
      t="edge_pop e'"
      and s="w@v1"
      in ssubst)
   apply(rename_tac wa)(*strict*)
   apply(force)
  apply(rename_tac wa)(*strict*)
  apply(subgoal_tac "prefix w (longest_common_prefix (w @ SSv1) (w @ SSv2))" for SSv1 SSv2)
   apply(rename_tac wa)(*strict*)
   prefer 2
   apply(rule_tac
      ?v1.0="v1"
      and ?v2.0="v2"
      in longest_common_prefix_lower_bound)
  apply(rename_tac wa)(*strict*)
  apply(simp add: prefix_def)
  apply (metis drop_length_append)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_bound_lower2_prime: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> edge_pop e @ ca @ w' @ [epda_box G] \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> edge_pop e @ ca = w'event @ [x']
  \<Longrightarrow> F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ w' @ [epda_box G]) e = edge_pop e @ ca
  \<Longrightarrow> edge_src ea = edge_src e
  \<Longrightarrow> ea \<in> epda_delta G
  \<Longrightarrow> edge_pop e @ ca @ hd (w' @ [epda_box G]) # caa = edge_pop ea
  \<Longrightarrow> False"
  apply(subgoal_tac "prefix (edge_pop e @ ca @ [hd (w' @ [epda_box G])]) (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ ca @ w' @ [epda_box G]) e)")
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply (metis append_injective2 append_self_conv list.simps(2))
  apply(rule_tac
      ?e'.0="ea"
      and ?v1.0="caa"
      and ?v2.0="tl(w'@[epda_box G])"
      in F_EDPDA_RMPOE_longest_popping_sequence_bound_lower2)
         apply(force)
        apply(force)
       defer
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: prefix_def)
  apply(force)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_mid_derivation: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> epdaS.derivation (F_EDPDA_RMPOE G) (F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c)"
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def)
  apply(simp add: Let_def)
  apply(subgoal_tac "c \<in> epdaS_configurations G")
   prefer 2
   apply (metis)
  apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
   prefer 2
   apply(rule_tac F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
      apply(force)
     apply(force)
    apply (metis)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) (epdaS_conf_stack c)")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
      apply(force)
     apply(force)
    apply (metis)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(subgoal_tac "prefix (edge_pop e) (epdaS_conf_stack c)")
   prefer 2
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca caa cb)(*strict*)
  apply(subgoal_tac "cb=ca@caa")
   apply(rename_tac ca caa cb)(*strict*)
   prefer 2
   apply (metis append_linj concat_asso)
  apply(rename_tac ca caa cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca caa)(*strict*)
  apply(subgoal_tac "\<exists>e' \<in> epda_delta G. edge_src e'=edge_src e \<and> prefix(F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)(edge_pop e')")
   apply(rename_tac ca caa)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_realizer)
      apply(rename_tac ca caa)(*strict*)
      apply(force)
     apply(rename_tac ca caa)(*strict*)
     apply(force)
    apply(rename_tac ca caa)(*strict*)
    apply (metis)
   apply(rename_tac ca caa)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca caa e')(*strict*)
  apply(subgoal_tac "(epdaS_conf_stack c) \<in> must_terminated_by (epda_gamma G) (epda_box G)")
   apply(rename_tac ca caa e')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ca caa e')(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rename_tac ca caa e' a)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac ca caa e' a cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac ca caa e' a cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca caa e' a cb cc)(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(case_tac cb)
    apply(rename_tac ca caa e' a cb cc)(*strict*)
    prefer 2
    apply(rename_tac ca caa e' a cb cc aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
     apply(rename_tac ca caa e' a cb cc aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca caa e' a cb cc aa list)(*strict*)
    apply(thin_tac "cb=aa#list")
    apply(clarsimp)
    apply(rename_tac ca caa e' a cc w' x')(*strict*)
    apply(subgoal_tac "valid_epda_step_label G e'")
     apply(rename_tac ca caa e' a cc w' x')(*strict*)
     apply(simp add: valid_epda_step_label_def may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
     apply(clarsimp)
     apply(rename_tac ca caa e' a cc w' x' aa ab)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac ca caa e' a cc w' x' aa ab)(*strict*)
      apply(force)
     apply(rename_tac ca caa e' a cc w' x' aa ab)(*strict*)
     apply(erule_tac
      P="edge_pop e' = aa @ [epda_box G]"
      in disjE)
      apply(rename_tac ca caa e' a cc w' x' aa ab)(*strict*)
      apply(clarsimp)
     apply(rename_tac ca caa e' a cc w' x' aa ab)(*strict*)
     apply(clarsimp)
    apply(rename_tac ca caa e' a cc w' x')(*strict*)
    apply(simp add: valid_epda_def)
   apply(rename_tac ca caa e' a cb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca caa e' a cc)(*strict*)
   apply(case_tac caa)
    apply(rename_tac ca caa e' a cc)(*strict*)
    prefer 2
    apply(rename_tac ca caa e' a cc aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. caa = w' @ [x']")
     apply(rename_tac ca caa e' a cc aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca caa e' a cc aa list)(*strict*)
    apply(thin_tac "caa=aa#list")
    apply(clarsimp)
    apply(rename_tac ca e' cc w')(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac ca e' cc w')(*strict*)
     apply(force)
    apply(rename_tac ca e' cc w')(*strict*)
    apply(case_tac ca)
     apply(rename_tac ca e' cc w')(*strict*)
     apply(clarsimp)
     apply(rename_tac e' cc w')(*strict*)
     apply (metis not_in_diff set_append2 set_subset_in)
    apply(rename_tac ca e' cc w' a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac ca e' cc w' a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca e' cc w' a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
    apply(rename_tac e' cc w' w'event x')(*strict*)
    apply (metis append1_eq_conv append_Cons butlast_snoc butlast_snoc_2 concat_asso eq_Nil_appendI)
   apply(rename_tac ca caa e' a cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca e' a cc)(*strict*)
   apply(subgoal_tac "a=cc")
    apply(rename_tac ca e' a cc)(*strict*)
    prefer 2
    apply (metis butlast_snoc)
   apply(rename_tac ca e' a cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca e' cc)(*strict*)
   apply(rule_tac
      t="left_quotient_word cc (edge_pop e')"
      and s="Some[epda_box G]"
      in ssubst)
    apply(rename_tac ca e' cc)(*strict*)
    apply (metis left_quotient_word_removes_right_addition_hlp)
   apply(rename_tac ca e' cc)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac ca e' cc)(*strict*)
    prefer 2
    apply(simp add: option_to_list_def)
   apply(rename_tac ca e' cc)(*strict*)
   apply(simp add: F_EDPDA_RMPOE_def)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(rule conjI)
    apply(rename_tac ca e' cc)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def)
    apply(rule disjI1)
    apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
    apply(rule_tac
      x="e'"
      in exI)
    apply(clarsimp)
    apply(simp add: strict_prefix_def)
    apply(force)
   apply(rename_tac ca e' cc)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__states_bottom_on_top_def)
   apply(rule_tac
      x="e'"
      in exI)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(rule conjI)
    apply(rename_tac ca e' cc)(*strict*)
    apply (metis butlast_snoc)
   apply(rename_tac ca e' cc)(*strict*)
   apply(rule_tac
      x="cc"
      in exI)
   apply(force)
  apply(rename_tac ca caa e' a cb)(*strict*)
  apply(clarsimp)
  apply(case_tac caa)
   apply(rename_tac ca caa e' a cb)(*strict*)
   apply(force)
  apply(rename_tac ca caa e' a cb aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. caa = w' @ [x']")
   apply(rename_tac ca caa e' a cb aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac ca caa e' a cb aa list)(*strict*)
  apply(thin_tac "caa=aa#list")
  apply(clarsimp)
  apply(rename_tac ca e' cb w')(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(case_tac "edge_pop e @ ca")
   apply(rename_tac ca e' cb w')(*strict*)
   apply(simp add: epda_no_nil_popping_edges_def)
  apply(rename_tac ca e' cb w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_pop e @ ca = w' @ [x']")
   apply(rename_tac ca e' cb w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(rule_tac
      t="edge_pop e@ca"
      and s="a#list"
      in ssubst)
    apply(rename_tac ca e' cb w' a list)(*strict*)
    apply(force)
   apply(rename_tac ca e' cb w' a list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac ca e' cb w' a list)(*strict*)
  apply(thin_tac "edge_pop e @ ca=a#list")
  apply(clarsimp)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(rule_tac
      t="left_quotient_word w'event (edge_pop e @ ca @ w' @ [epda_box G])"
      and s="Some(x'#w' @ [epda_box G])"
      in ssubst)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply (metis ConsApp left_quotient_word_removes_right_addition_hlp append_Cons concat_asso)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="left_quotient_word (w'event @ [x']) (edge_pop e @ ca @ w' @ [epda_box G])"
      and s="Some(w' @ [epda_box G])"
      in ssubst)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply (metis ConsApp left_quotient_word_removes_right_addition_hlp append_Cons concat_asso)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der3_is_derivation)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply (metis F_EDPDA_RMPOE_preserves_epda)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(rule conjI)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    prefer 2
    apply(simp add: option_to_list_def)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(simp add: F_EDPDA_RMPOE_def)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(rule conjI)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def)
    apply(rule disjI1)
    apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
    apply(rule_tac
      x="e'"
      in exI)
    apply(clarsimp)
    apply(simp add: strict_prefix_def)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(case_tac cb)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(simp add: F_EDPDA_RMPOE__states_last_of_pop_def)
    apply(rule_tac
      x="e'"
      in exI)
    apply(clarsimp)
    apply(rename_tac ca e' w' w'event x')(*strict*)
    apply(simp add: suffix_def)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
    apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
   apply(thin_tac "cb=a#list")
   apply(clarsimp)
   apply(rename_tac ca e' w' w'event x' w'stack x'event)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
   apply(rule_tac
      x="e'"
      in exI)
   apply(clarsimp)
   apply(simp add: strict_prefix_def)
   apply(rule_tac
      x="w'stack@[x'event]"
      in exI)
   apply(force)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(rule conjI)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(rule_tac
      x="tl (w' @ [epda_box G])"
      in exI)
   apply(clarsimp)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(simp add: F_EDPDA_RMPOE_def)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(rule conjI)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(case_tac cb)
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(simp add: F_EDPDA_RMPOE__states_last_of_pop_def)
    apply(rule_tac
      x="e'"
      in exI)
    apply(clarsimp)
    apply(rename_tac ca e' w' w'event x')(*strict*)
    apply(simp add: suffix_def)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
    apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
   apply(thin_tac "cb=a#list")
   apply(clarsimp)
   apply(rename_tac ca e' w' w'event x' w'stack x'event)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
   apply(rule_tac
      x="e'"
      in exI)
   apply(clarsimp)
   apply(simp add: strict_prefix_def)
   apply(rule_tac
      x="w'stack@[x'event]"
      in exI)
   apply(force)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(simp add: F_EDPDA_RMPOE__states_context_of_top_def)
  apply(rule_tac
      x="e'"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(rule conjI)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(rule conjI)
   apply(rename_tac ca e' cb w' w'event x')(*strict*)
   apply(case_tac "w'")
    apply(rename_tac ca e' cb w' w'event x')(*strict*)
    apply(clarsimp)
    apply(rename_tac ca e' cb w'event x')(*strict*)
    apply(simp add: valid_epda_def)
   apply(rename_tac ca e' cb w' w'event x' a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac ca e' cb w' w'event x')(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_closure_def F_EDPDA_RMPOE__pop_components_def)
  apply(clarsimp)
  apply(rename_tac ca e' cb w' w'event x' ea)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
  apply(rule_tac caa="caa" and ea="ea" and ca="ca" and w'="w'" in F_EDPDA_RMPOE_longest_popping_sequence_bound_lower2_prime)
         apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
         apply(force)
        apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
        apply(force)
       apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
      defer
      apply(force)
     apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
     apply(force)
    apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
    apply(force)
   apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
   apply(metis ConsApp concat_asso)
  apply(rename_tac ca e' cb w' w'event x' ea caa)(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  done

lemma F_EDPDA_RMPOE_longest_popping_sequence_not_empty: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e = []
  \<Longrightarrow> False"
  apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: prefix_def)
  apply(simp add: prefix_def)
  apply(simp add: epda_no_nil_popping_edges_def)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation_maximum_of_domain: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> maximum_of_domain (F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c) (length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) - Suc 0)"
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
  apply(simp add: Let_def)
  apply(simp add: maximum_of_domain_def)
  apply(rule conjI)
   apply(clarsimp)
  apply(case_tac "length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
   prefer 2
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rule F_EDPDA_RMPOE_longest_popping_sequence_not_empty)
        apply(force)+
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_derivation_fit: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> n = (length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) - Suc 0)
  \<Longrightarrow> d1 = F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c
  \<Longrightarrow> d2 = F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c
  \<Longrightarrow> derivation_append_fit d1 d2 n"
  apply(simp add: derivation_append_fit_def Let_def)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def Let_def)
  apply(clarsimp)
  apply(case_tac "length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
   apply(clarsimp)
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_not_empty)
         apply(force)+
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def Let_def)
  apply(case_tac "F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e \<sqsupseteq> [epda_box G]")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
   apply(rule conjI)
    apply(rename_tac nat)(*strict*)
    apply (metis butlast_snoc take_nth)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) (epdaS_conf_stack c)")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(simp add: epdaS_step_relation_def prefix_def)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac ca caa)(*strict*)
   apply(rule_tac
      t="left_quotient_word ca (epdaS_conf_stack c)"
      and s="Some(epda_box G # caa)"
      in ssubst)
    apply(rename_tac ca caa)(*strict*)
    apply (metis left_quotient_word_removes_right_addition)
   apply(rename_tac ca caa)(*strict*)
   apply(clarsimp)
   apply (metis dropPrecise)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(simp add: der3_def)
  apply(rule conjI)
   apply(rename_tac nat)(*strict*)
   apply (metis butlast_snoc take_nth)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) (epdaS_conf_stack c)")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac nat ca)(*strict*)
  apply(case_tac "F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e")
   apply(rename_tac nat ca)(*strict*)
   apply(force)
  apply(rename_tac nat ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e = w' @ [x']")
   apply(rename_tac nat ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac nat ca a list)(*strict*)
  apply(thin_tac "F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e=a#list")
  apply(clarsimp)
  apply(rename_tac ca w' x')(*strict*)
  apply(rule_tac
      t="left_quotient_word w' (epdaS_conf_stack c)"
      and s="Some(x'#ca)"
      in ssubst)
   apply(rename_tac ca w' x')(*strict*)
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac ca w' x')(*strict*)
  apply (metis dropPrecise option.sel)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_derivation: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> n = (length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) - Suc 0)
  \<Longrightarrow> d1 = F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c
  \<Longrightarrow> d2 = F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c
  \<Longrightarrow> epdaS.derivation (F_EDPDA_RMPOE G) (derivation_append d1 d2 n)"
  apply(rule epdaS.derivation_append_from_derivation_append_fit)
      apply (metis F_EDPDA_RMPOE_preserves_epda)
     apply (metis F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation)
    apply(clarsimp)
    apply (rule F_EDPDA_RMPOE__relation_LR_step_simulation_mid_derivation)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation_maximum_of_domain)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_derivation_fit)
          apply(force)+
  done

definition F_EDPDA_RMPOE__relation_LR_step_simulation_fin :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation"
  where
    "F_EDPDA_RMPOE__relation_LR_step_simulation_fin G e c1 \<equiv>
  let
    w = F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c1) e
  in
    if suffix w [epda_box G]
    then der2
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) (butlast w) (Some (epda_box G)),
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word (butlast w) (epdaS_conf_stack c1))\<rparr>
            \<lparr>edge_src = cons_tuple3 (epdaS_conf_state c1) (butlast w) (Some (epda_box G)),
            edge_event = edge_event e,
            edge_pop = [epda_box G],
            edge_push = (edge_push e) @ (the (left_quotient_word (edge_pop e) w)),
            edge_trg = cons_tuple3 (edge_trg e) [] None\<rparr>
          \<lparr>epdaS_conf_state = cons_tuple3 (edge_trg e) [] None,
          epdaS_conf_scheduler = drop (length ((option_to_list (edge_event e)))) (epdaS_conf_scheduler c1),
          epdaS_conf_stack = (edge_push e) @ the (left_quotient_word (edge_pop e) (epdaS_conf_stack c1))\<rparr>
    else der2
          \<lparr>epdaS_conf_state = cons_tuple3 (epdaS_conf_state c1) w (Some (hd (the (left_quotient_word w (epdaS_conf_stack c1))))),
          epdaS_conf_scheduler = epdaS_conf_scheduler c1,
          epdaS_conf_stack = the (left_quotient_word w (epdaS_conf_stack c1))\<rparr>
            \<lparr>edge_src = cons_tuple3 (epdaS_conf_state c1) w (Some (hd (the (left_quotient_word w (epdaS_conf_stack c1))))),
            edge_event = edge_event e,
            edge_pop = [hd (the (left_quotient_word w (epdaS_conf_stack c1)))],
            edge_push = (edge_push e) @ (the (left_quotient_word (edge_pop e) (w @ [hd (the (left_quotient_word w (epdaS_conf_stack c1)))]))),
            edge_trg = cons_tuple3 (edge_trg e) [] None\<rparr> \<lparr>epdaS_conf_state = cons_tuple3 (edge_trg e) [] None,
          epdaS_conf_scheduler = drop (length ((option_to_list (edge_event e)))) (epdaS_conf_scheduler c1),
          epdaS_conf_stack = (edge_push e) @ the (left_quotient_word (edge_pop e) (epdaS_conf_stack c1))\<rparr>"

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_fin_derivation: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> epdaS.derivation (F_EDPDA_RMPOE G) (F_EDPDA_RMPOE__relation_LR_step_simulation_fin G e c)"
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def)
  apply(simp add: Let_def)
  apply(subgoal_tac "prefix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) (epdaS_conf_stack c)")
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_bound_upper)
      apply(force)
     apply(force)
    apply (metis)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(subgoal_tac "prefix (edge_pop e) (epdaS_conf_stack c)")
   prefer 2
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(subgoal_tac "prefix (edge_pop e) (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)")
   prefer 2
   apply (metis F_EDPDA_RMPOE_longest_popping_sequence_bound_lower)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca caa cb)(*strict*)
  apply(subgoal_tac "cb@ca=caa")
   apply(rename_tac ca caa cb)(*strict*)
   prefer 2
   apply (metis append_linj concat_asso)
  apply(rename_tac ca caa cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca cb)(*strict*)
  apply(subgoal_tac "\<exists>e' \<in> epda_delta G. edge_src e'=edge_src e \<and> prefix(F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e)(edge_pop e')")
   apply(rename_tac ca cb)(*strict*)
   prefer 2
   apply(rule F_EDPDA_RMPOE_longest_popping_sequence_realizer)
      apply(rename_tac ca cb)(*strict*)
      apply(force)
     apply(rename_tac ca cb)(*strict*)
     apply(force)
    apply(rename_tac ca cb)(*strict*)
    apply (metis)
   apply(rename_tac ca cb)(*strict*)
   apply(simp add: epdaS_step_relation_def prefix_def)
   apply(force)
  apply(rename_tac ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca cb e')(*strict*)
  apply(rule conjI)
   apply(rename_tac ca cb e')(*strict*)
   apply(clarsimp)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac ca cb e' caa cc)(*strict*)
   apply(case_tac caa)
    apply(rename_tac ca cb e' caa cc)(*strict*)
    prefer 2
    apply(rename_tac ca cb e' caa cc a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. caa = w' @ [x']")
     apply(rename_tac ca cb e' caa cc a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca cb e' caa cc a list)(*strict*)
    apply(thin_tac "caa=a#list")
    apply(clarsimp)
    apply(rename_tac ca cb e' cc w' x')(*strict*)
    apply(subgoal_tac "valid_epda_step_label G e'")
     apply(rename_tac ca cb e' cc w' x')(*strict*)
     apply(simp add: valid_epda_step_label_def may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
     apply(clarsimp)
     apply(rename_tac ca cb e' cc w' x' a aa ab)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac ca cb e' cc w' x' a aa ab)(*strict*)
      apply(force)
     apply(rename_tac ca cb e' cc w' x' a aa ab)(*strict*)
     apply(erule_tac
      P="edge_pop e' = aa @ [epda_box G]"
      in disjE)
      apply(rename_tac ca cb e' cc w' x' a aa ab)(*strict*)
      apply(clarsimp)
     apply(rename_tac ca cb e' cc w' x' a aa ab)(*strict*)
     apply(clarsimp)
    apply(rename_tac ca cb e' cc w' x')(*strict*)
    apply(simp add: valid_epda_def)
   apply(rename_tac ca cb e' caa cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca cb e' cc)(*strict*)
   apply(case_tac ca)
    apply(rename_tac ca cb e' cc)(*strict*)
    prefer 2
    apply(rename_tac ca cb e' cc a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac ca cb e' cc a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca cb e' cc a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
    apply(rename_tac cb e' cc w' x')(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac cb e' cc w' x')(*strict*)
     apply(force)
    apply(rename_tac cb e' cc w' x')(*strict*)
    apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac cb e' cc w')(*strict*)
    apply(case_tac e')
    apply(rename_tac cb e' cc w' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac cb cc w' edge_eventa edge_pusha edge_trga)(*strict*)
    apply(case_tac cb)
     apply(rename_tac cb cc w' edge_eventa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac cc w' edge_eventa edge_pusha edge_trga)(*strict*)
     apply (metis List.set_simps(2) not_in_diff set_append2 set_subset_in)
    apply(rename_tac cb cc w' edge_eventa edge_pusha edge_trga a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
     apply(rename_tac cb cc w' edge_eventa edge_pusha edge_trga a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac cb cc w' edge_eventa edge_pusha edge_trga a list)(*strict*)
    apply(thin_tac "cb=a#list")
    apply(clarsimp)
   apply(rename_tac ca cb e' cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac cb e' cc)(*strict*)
   apply(rule_tac
      t="left_quotient_word cc (edge_pop e')"
      and s="Some([epda_box G])"
      in ssubst)
    apply(rename_tac cb e' cc)(*strict*)
    apply (metis left_quotient_word_removes_right_addition)
   apply(rename_tac cb e' cc)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(left_quotient_word (edge_pop e) (edge_pop e'))"
      and s="Some cb"
      in ssubst)
    apply(rename_tac cb e' cc)(*strict*)
    apply (metis left_quotient_word_removes_right_addition)
   apply(rename_tac cb e' cc)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE_def)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(rule disjI1)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(rule_tac
      x="e"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac cb e' cc)(*strict*)
    apply(rule_tac
      t="(left_quotient_word (edge_pop e) (edge_pop e'))"
      and s="Some cb"
      in ssubst)
     apply(rename_tac cb e' cc)(*strict*)
     apply (metis left_quotient_word_removes_right_addition)
    apply(rename_tac cb e' cc)(*strict*)
    apply(force)
   apply(rename_tac cb e' cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac cb e' cc)(*strict*)
    apply(simp add: prefix_def)
    apply(force)
   apply(rename_tac cb e' cc)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_def)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(simp only: F_EDPDA_RMPOE__states_bottom_on_top_def)
   apply(clarsimp)
   apply(rule_tac
      x="e'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac cb e' cc)(*strict*)
    prefer 2
    apply(simp add: suffix_def)
    apply(rule_tac
      x="cc"
      in exI)
    apply(force)
   apply(rename_tac cb e' cc)(*strict*)
   apply (metis butlast_snoc)
  apply(rename_tac ca cb e')(*strict*)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(rule_tac
      t="F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ ca) e"
      and s="edge_pop e @ cb"
      in ssubst)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply(force)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(rule_tac
      t="left_quotient_word (edge_pop e @ cb) (edge_pop e @ cb @ ca)"
      and s="Some ca"
      in ssubst)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply (metis left_quotient_word_removes_right_addition concat_asso)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ ca) e"
      and s="edge_pop e @ cb"
      in ssubst)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply(force)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(rule_tac
      t="left_quotient_word (edge_pop e) ((edge_pop e @ cb) @ [hd ca])"
      and s="Some (cb @ [hd ca])"
      in ssubst)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply (metis left_quotient_word_removes_right_addition concat_asso)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(rule_tac
      t="left_quotient_word (edge_pop e) (edge_pop e @ cb @ ca)"
      and s="Some(cb@ca)"
      in ssubst)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac ca cb e' caa)(*strict*)
  apply(case_tac ca)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac ca cb e' caa)(*strict*)
    apply(force)
   apply(rename_tac ca cb e' caa)(*strict*)
   apply(clarify)
   apply(erule_tac
      x="butlast(edge_pop e@cb)"
      in allE)
   apply(simp only: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
   apply(clarify)
   apply(rename_tac ca cb e' caa a b)(*strict*)
   apply(subgoal_tac "F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ []) e = butlast (F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ []) e) @ [epda_box G]")
    apply(rename_tac ca cb e' caa a b)(*strict*)
    apply(force)
   apply(rename_tac ca cb e' caa a b)(*strict*)
   apply(rule_tac
      t="F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ []) e"
      and s="edge_pop e @ cb"
      in ssubst)
    apply(rename_tac ca cb e' caa a b)(*strict*)
    apply(force)
   apply(rename_tac ca cb e' caa a b)(*strict*)
   apply(rule_tac
      t="edge_pop e @ cb"
      and s="a @ [epda_box G]"
      in ssubst)
    apply(rename_tac ca cb e' caa a b)(*strict*)
    apply(force)
   apply(rename_tac ca cb e' caa a b)(*strict*)
   apply(force)
  apply(rename_tac ca cb e' caa a list)(*strict*)
  apply(rule conjI)
   apply(rename_tac ca cb e' caa a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ca cb e' caa a list)(*strict*)
  apply(rename_tac w)
  apply(rename_tac ca cb e' caa a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE_def)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(rule disjI1)
  apply(simp add: F_EDPDA_RMPOE__edges_final_def)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="F_EDPDA_RMPOE_longest_popping_sequence G (edge_pop e @ cb @ a # w) e"
      and s="edge_pop e @ cb"
      in ssubst)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(force)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(rule conjI)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(rule_tac
      t="left_quotient_word (edge_pop e) ((edge_pop e @ cb) @ [a])"
      and s="Some(cb@[a])"
      in ssubst)
    apply(rename_tac cb e' ca a w)(*strict*)
    apply(rule_tac
      t="(edge_pop e @ cb) @ [a]"
      and s="edge_pop e @ cb @ [a]"
      in ssubst)
     apply(rename_tac cb e' ca a w)(*strict*)
     apply(force)
    apply(rename_tac cb e' ca a w)(*strict*)
    apply (metis left_quotient_word_removes_right_addition)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(force)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(rule conjI)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(simp (no_asm) add: prefix_def)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(simp only: F_EDPDA_RMPOE__states_context_of_top_def)
  apply(clarsimp)
  apply(rule_tac
      x="e'"
      in exI)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(rule conjI)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(rule conjI)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(rule_tac
      A="set (epdaS_conf_stack c)"
      in set_mp)
    apply(rename_tac cb e' ca a w)(*strict*)
    apply(rule epda_stack_in_gamma)
     apply(rename_tac cb e' ca a w)(*strict*)
     apply(force)
    apply(rename_tac cb e' ca a w)(*strict*)
    apply(force)
   apply(rename_tac cb e' ca a w)(*strict*)
   apply(force)
  apply(rename_tac cb e' ca a w)(*strict*)
  apply(simp add: prefix_closure_def F_EDPDA_RMPOE__pop_components_def)
  apply(clarsimp)
  apply(rename_tac cb e' ca a w ea)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac cb e' ca a w ea cc)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e @ cb @ [a]) (F_EDPDA_RMPOE_longest_popping_sequence G ((edge_pop e @ cb @ a # w)) e)")
   apply(rename_tac cb e' ca a w ea cc)(*strict*)
   prefer 2
   apply(rule_tac
      ?v1.0="cc"
      and e'="ea"
      and ?v2.0="w"
      in F_EDPDA_RMPOE_longest_popping_sequence_bound_lower2)
          apply(rename_tac cb e' ca a w ea cc)(*strict*)
          apply(force)
         apply(rename_tac cb e' ca a w ea cc)(*strict*)
         apply(force)
        apply(rename_tac cb e' ca a w ea cc)(*strict*)
        apply(rule_tac
      t="(edge_pop e @ cb @ [a]) @ w"
      and s="edge_pop e @ cb @ a # w"
      in ssubst)
         apply(rename_tac cb e' ca a w ea cc)(*strict*)
         apply(force)
        apply(rename_tac cb e' ca a w ea cc)(*strict*)
        apply(force)
       apply(rename_tac cb e' ca a w ea cc)(*strict*)
       apply(force)
      apply(rename_tac cb e' ca a w ea cc)(*strict*)
      apply(force)
     apply(rename_tac cb e' ca a w ea cc)(*strict*)
     apply (metis ConsApp append_eq_appendI)
    apply(rename_tac cb e' ca a w ea cc)(*strict*)
    apply(force)
   apply(rename_tac cb e' ca a w ea cc)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac cb e' ca a w ea cc)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac cb e' ca a w ea cc cca)(*strict*)
  apply (metis append_injective2 append_self_conv list.simps(2))
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_fin_derivation_maximum_of_domain: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> maximum_of_domain (F_EDPDA_RMPOE__relation_LR_step_simulation_fin G1 e1 c1) 1"
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def)
  apply(simp add: Let_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rule der2_maximum_of_domain)
  apply(clarsimp)
  apply(rule der2_maximum_of_domain)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_fin_derivation: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> c \<in> epdaS_configurations G
  \<Longrightarrow> epdaS_conf_stack c \<in> must_terminated_by (epda_gamma G) (epda_box G)
  \<Longrightarrow> epdaS_step_relation G c e c'
  \<Longrightarrow> n1 = (length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) - Suc 0)
  \<Longrightarrow> n2 = (if (suffix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) ([epda_box G])) then 1 else 2)
  \<Longrightarrow> d1 = F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c
  \<Longrightarrow> d2 = F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c
  \<Longrightarrow> d3 = F_EDPDA_RMPOE__relation_LR_step_simulation_fin G e c
  \<Longrightarrow> epdaS.derivation (F_EDPDA_RMPOE G) (derivation_append (derivation_append d1 d2 n1) d3 (n1 + n2))"
  apply(rule epdaS.derivation_append_preserves_derivation)
    apply (metis F_EDPDA_RMPOE_preserves_epda F_EDPDA_RMPOE__relation_LR_step_simulation_mid_derivation F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation_maximum_of_domain F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_derivation_fit epdaS.derivation_append_from_derivation_append_fit)
   apply(clarsimp)
   apply (metis (full_types) F_EDPDA_RMPOE__relation_LR_step_simulation_fin_derivation)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def Let_def)
   apply(simp add: der2_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def Let_def)
   apply(simp add: der2_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def Let_def)
  apply(simp add: der3_def)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_mid_def F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def Let_def)
  apply(simp add: der2_def)
  done

definition F_EDPDA_RMPOE__relation_LR_step_simulation_combine :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation"
  where
    "F_EDPDA_RMPOE__relation_LR_step_simulation_combine G e c \<equiv>
  let
    d1 = F_EDPDA_RMPOE__relation_LR_step_simulation_pre G e c;
    d2 = F_EDPDA_RMPOE__relation_LR_step_simulation_mid G e c;
    d3 = F_EDPDA_RMPOE__relation_LR_step_simulation_fin G e c;
    n1 = length (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) - Suc 0;
    n2 = if suffix (F_EDPDA_RMPOE_longest_popping_sequence G (epdaS_conf_stack c) e) ([epda_box G])
          then 1
          else 2
  in
    derivation_append (derivation_append d1 d2 n1) d3 (n1 + n2)"

definition F_EDPDA_RMPOE__relation_LR_step_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  d = F_EDPDA_RMPOE__relation_LR_step_simulation_combine G1 e c1"

definition F_EDPDA_RMPOE__relation_LR_initial_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ((('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label, (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LR_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_EDPDA_RMPOE__configuration [] None c1)"

lemma F_EDPDA_RMPOE__configuration_preserves_configurations: "
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration [] None c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__configuration_def)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac q i s)(*strict*)
   apply(simp add: F_EDPDA_RMPOE_def Let_def F_EDPDA_RMPOE__states_def)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(simp add: F_EDPDA_RMPOE__states_basic_def)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EDPDA_RMPOE_def Let_def F_EDPDA_RMPOE__states_def)
  done

lemma F_EDPDA_RMPOE__configuration_preserves_initial_configurations: "
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration [] None c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def)
   apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def Let_def)
  apply(rule F_EDPDA_RMPOE__configuration_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_EDPDA_RMPOE__configuration_preserves_marking_configurations: "
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration [] None c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__configuration_def F_EDPDA_RMPOE_def Let_def)
  apply(rule F_EDPDA_RMPOE__configuration_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma F_EDPDA_RMPOE_initial_simulation_preserves_derivation: "
  F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 (F_EDPDA_RMPOE__configuration [] None c1))"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_EDPDA_RMPOE__configuration_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RMPOE__relation_LR_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_EDPDA_RMPOE_initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def valid_pda_def valid_dpda_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE__relation_LR_step_simulation_maps_to_derivation: "
  F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp only: F_EDPDA_RMPOE__relation_LR_step_simulation_def F_EDPDA_RMPOE__relation_LR_step_simulation_combine_def)
  apply(simp only: Let_def)
  apply(rule_tac
      t="G2"
      and s="F_EDPDA_RMPOE G1"
      in ssubst)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(rule_tac
      c="c1"
      and e="e1"
      in F_EDPDA_RMPOE__relation_LR_step_simulation_pre_mid_fin_derivation)
            apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE__relation_LR_TSstructure_def)
           apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE__relation_LR_TSstructure_def)
          apply(simp add: epdaS_step_relation_def)
         apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE__relation_LR_TSstructure_def)
         apply(clarsimp)
         apply (metis (full_types) epdaS.get_accessible_configurations_are_configurations subsetD)
        apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE__relation_LR_TSstructure_def)
        apply(clarsimp)
        apply (metis epda_stack_is_must_terminated_by)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_def)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply (metis F_EDPDA_RMPOE__relation_LR_step_simulation_def F_EDPDA_RMPOE__relation_LR_step_simulation_maps_to_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G1")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def epda_step_labels_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (metis (full_types) epdaS.get_accessible_configurations_are_configurations subsetD)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      ca="\<lparr>epdaS_conf_state=cons_tuple3 (epdaS_conf_state c1) [] None,epdaS_conf_scheduler=epdaS_conf_scheduler c1,epdaS_conf_stack=epdaS_conf_stack c1\<rparr>"
      in epdaS.derivation_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
      apply(clarsimp)
      apply(rename_tac G1 c1 c2 e1 c1')(*strict*)
      apply (metis F_EDPDA_RMPOE_preserves_epda)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_combine_def derivation_append_def)
     apply(rule conjI)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(clarsimp)
      apply(simp add: Let_def F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
      apply (metis Nil_is_append_conv not_Cons_self suffix_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(clarsimp)
     apply(simp add: Let_def F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def)
     apply(clarsimp)
     apply(rule_tac
      G="G1"
      and e="e1"
      and c="c1"
      in F_EDPDA_RMPOE_longest_popping_sequence_not_empty)
           apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
           apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
          apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
          apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
         apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
         apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def epda_step_labels_def)
        apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
       apply (rule epda_stack_is_must_terminated_by)
        apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
        apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
       apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE_def)
    apply(simp add: Let_def)
    apply(simp add: epdaS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G1 e1 c1' q i s)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_def)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(simp add: F_EDPDA_RMPOE__states_basic_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(thin_tac "epdaS.derivation G2 (F_EDPDA_RMPOE__relation_LR_step_simulation_combine G1 e1 c1)")
   apply(simp add: F_EDPDA_RMPOE__relation_LR_step_simulation_combine_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def Let_def F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def F_EDPDA_RMPOE__relation_LR_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def F_EDPDA_RMPOE__configuration_def)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(rule_tac
      G="G1"
      and e="e1"
      and c="c1"
      in F_EDPDA_RMPOE_longest_popping_sequence_not_empty)
          apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
          apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
         apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
         apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
        apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
        apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def epda_step_labels_def)
       apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply (rule epda_stack_is_must_terminated_by)
       apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
      apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
     apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE_def)
   apply(simp add: Let_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: derivation_append_def Let_def F_EDPDA_RMPOE__relation_LR_step_simulation_pre_def F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def F_EDPDA_RMPOE__configuration_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule_tac
      G="G1"
      and e="e1"
      and c="c1"
      in F_EDPDA_RMPOE_longest_popping_sequence_not_empty)
         apply(rename_tac G1 c1 e1 c1')(*strict*)
         apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
       apply(rename_tac G1 c1 e1 c1')(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def epda_step_labels_def)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply (rule epda_stack_is_must_terminated_by)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def F_EDPDA_RMPOE__relation_LR_configuration_def F_EDPDA_RMPOE_def)
  apply(simp add: Let_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      x=" (length (F_EDPDA_RMPOE_longest_popping_sequence G1 (epdaS_conf_stack c1) e1) - Suc 0) +(if (suffix(F_EDPDA_RMPOE_longest_popping_sequence G1 (epdaS_conf_stack c1) e1)([epda_box G1])) then 1 else 2) +1"
      in exI)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp only: F_EDPDA_RMPOE__relation_LR_step_simulation_combine_def Let_def)
   apply(rule concat_has_max_dom)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(rule F_EDPDA_RMPOE__relation_LR_step_simulation_pre_derivation_maximum_of_domain)
          apply(rename_tac G1 c1 e1 c1')(*strict*)
          apply(force)
         apply(rename_tac G1 c1 e1 c1')(*strict*)
         apply(force)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(simp add: epdaS_step_relation_def)
       apply(rename_tac G1 c1 e1 c1')(*strict*)
       apply(force)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply (rule epda_stack_is_must_terminated_by)
       apply(rename_tac G1 c1 e1 c1')(*strict*)
       apply(force)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(rule F_EDPDA_RMPOE__relation_LR_step_simulation_mid_derivation_maximum_of_domain)
         apply(rename_tac G1 c1 e1 c1')(*strict*)
         apply(force)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(force)
       apply(rename_tac G1 c1 e1 c1')(*strict*)
       apply(simp add: epdaS_step_relation_def)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply (rule epda_stack_is_must_terminated_by)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(rule F_EDPDA_RMPOE__relation_LR_step_simulation_fin_derivation_maximum_of_domain)
        apply(rename_tac G1 c1 e1 c1')(*strict*)
        apply(force)
       apply(rename_tac G1 c1 e1 c1')(*strict*)
       apply(force)
      apply(rename_tac G1 c1 e1 c1')(*strict*)
      apply(simp add: epdaS_step_relation_def)
      apply(force)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply (rule epda_stack_is_must_terminated_by)
     apply(rename_tac G1 c1 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (metis epdaS.der2_is_derivation epdaS.der2_preserves_get_accessible_configurations)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(simp (no_asm) add: F_EDPDA_RMPOE__relation_LR_step_simulation_combine_def get_configuration_def derivation_append_def Let_def der2_def F_EDPDA_RMPOE__configuration_def)
  apply(simp (no_asm) add: Let_def F_EDPDA_RMPOE__relation_LR_step_simulation_fin_def F_EDPDA_RMPOE__configuration_def der2_def)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' w)(*strict*)
  apply(rule_tac
      t="left_quotient_word (edge_pop e1) (edge_pop e1 @ w)"
      and s="Some w"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1' w)(*strict*)
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac G1 c1 e1 c1' w)(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_configuration F_EDPDA_RMPOE__relation_LR_TSstructure F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RMPOE__relation_LR_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RMPOE__relation_LR_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RMPOE__relation_LR_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RMPOE__relation_LR_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RMPOE__relation_LR_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration [] None ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration [] None c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EDPDA_RMPOE__configuration_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration [] None ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_configuration F_EDPDA_RMPOE__relation_LR_TSstructure F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_LR_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_marked_effect: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_LR_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_configuration F_EDPDA_RMPOE__relation_LR_effect F_EDPDA_RMPOE__relation_LR_TSstructure F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_LR_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_LR_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EDPDA_RMPOE__configuration [] None c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    prefer 2
    apply(simp add: F_EDPDA_RMPOE__configuration_def)
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="F_EDPDA_RMPOE__configuration [] None c1'"
      in exI)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE__configuration_def)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c ca)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def get_configuration_def F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(subgoal_tac "F_EDPDA_RMPOE__configuration [] None c=ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(rule_tac
      x="deri2n+n"
      in exI)
  apply(simp add: derivation_append_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_LR_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_LR_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_LR_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_LR_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_configuration_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EDPDA_RMPOE__configuration [] None c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EDPDA_RMPOE__relation_LR_configuration F_EDPDA_RMPOE__relation_LR_initial_configuration F_EDPDA_RMPOE__relation_LR_effect F_EDPDA_RMPOE__relation_LR_TSstructure F_EDPDA_RMPOE__relation_LR_initial_simulation F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RMPOE__relation_LR_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RMPOE__relation_LR_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RMPOE__relation_LR_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RMPOE__relation_LR_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RMPOE__relation_LR_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RMPOE__relation_LR_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms)
  done

lemma F_EDPDA_RMPOE_preserves_lang1: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_EDPDA_RMPOE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EDPDA_RMPOE G)"
      and s="epdaS.finite_marked_language (F_EDPDA_RMPOE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RMPOE__relation_LR_effect SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  done

lemma F_EDPDA_RMPOE_preserves_unmarked_language1: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.unmarked_language G \<subseteq> epdaS.unmarked_language (F_EDPDA_RMPOE G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis  epdaS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EDPDA_RMPOE G)"
      and s="epdaS.finite_unmarked_language (F_EDPDA_RMPOE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply(rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RMPOE__relation_LR_effect SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LR_effect_def)
  done

definition F_EDPDA_RMPOE__relation_RL_TSstructure :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<equiv>
  valid_epda G2
  \<and> G1 = F_EDPDA_RMPOE G2
  \<and> epda_no_nil_popping_edges G2
  \<and> epdaS.is_forward_edge_deterministic_accessible G2"

definition F_EDPDA_RMPOE__configuration_rev :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_EDPDA_RMPOE__configuration_rev c \<equiv>
  case epdaS_conf_state c of
  cons_tuple3 q w X \<Rightarrow>
    \<lparr>epdaS_conf_state = q,
    epdaS_conf_scheduler = epdaS_conf_scheduler c,
    epdaS_conf_stack = w @ (epdaS_conf_stack c)\<rparr>"

definition F_EDPDA_RMPOE__relation_RL_configuration :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_EDPDA_RMPOE__configuration_rev c1"

definition F_EDPDA_RMPOE__relation_RL_initial_configuration :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_EDPDA_RMPOE__configuration_rev c1"

definition F_EDPDA_RMPOE__relation_RL_effect :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_effect G1 G2 w1 w2 \<equiv>
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_EDPDA_RMPOE__relation_RL_TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_EDPDA_RMPOE_preserves_epda)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  done

definition F_EDPDA_RMPOE__relation_RL_step_simulation :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event , 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  case epdaS_conf_state c1 of cons_tuple3 q1 w1 X1 \<Rightarrow>
  (case epdaS_conf_state c1' of cons_tuple3 q2 w2 X2 \<Rightarrow>
  (case X1 of None \<Rightarrow> d = der1 c2
  | Some X1' \<Rightarrow>
    (case X2 of
    None \<Rightarrow> d = der2
                  (F_EDPDA_RMPOE__configuration_rev c1)
                    ((THE e'.
                        e' \<in> epda_delta G2
                        \<and> edge_src e' = q1
                        \<and> edge_trg e' = q2
                        \<and> edge_event e' = edge_event e
                        \<and> (\<exists>x. edge_pop e' @ x = w1 @ [X1']
                        \<and> edge_push e' @ x = edge_push e)))
                  (F_EDPDA_RMPOE__configuration_rev c1')
    | Some X2' \<Rightarrow> d = der1 c2)))"

definition F_EDPDA_RMPOE__relation_RL_initial_simulation :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event , 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event , 'stack) epda_step_label, ('state, 'event , 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_RL_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_EDPDA_RMPOE__configuration_rev c1)"

lemma F_EDPDA_RMPOE__configuration_rev_preserves_configurations: "
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration_rev c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
  apply(case_tac q)
  apply(rename_tac q i s qa list option)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s qa list option)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
   apply(clarsimp)
   apply(rename_tac i s list e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s list e)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(rule_tac
      B="set(edge_pop e)"
      in subset_trans)
     apply(rename_tac i s list e)(*strict*)
     apply(simp add: strict_prefix_def)
     apply (metis set_append1)
    apply(rename_tac i s list e)(*strict*)
    apply(rule valid_epda_pop_in_gamma)
     apply(rename_tac i s list e)(*strict*)
     apply(force)
    apply(rename_tac i s list e)(*strict*)
    apply(force)
   apply(rename_tac i s list e)(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_bottom_on_top_def)
   apply(clarsimp)
   apply(rename_tac i s e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s e)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(rule_tac
      B="set(edge_pop e)"
      in subset_trans)
     apply(rename_tac i s e)(*strict*)
     apply (metis trivButLast)
    apply(rename_tac i s e)(*strict*)
    apply(rule valid_epda_pop_in_gamma)
     apply(rename_tac i s e)(*strict*)
     apply(force)
    apply(rename_tac i s e)(*strict*)
    apply(force)
   apply(rename_tac i s e)(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_last_of_pop_def)
   apply(clarsimp)
   apply(rename_tac i s e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s e)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(rule valid_epda_pop_in_gamma)
     apply(rename_tac i s e)(*strict*)
     apply(force)
    apply(rename_tac i s e)(*strict*)
    apply(force)
   apply(rename_tac i s e)(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_context_of_top_def)
   apply(clarsimp)
   apply(rename_tac i s list e \<gamma>)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s list e \<gamma>)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(rule_tac
      B="set(edge_pop e)"
      in subset_trans)
     apply(rename_tac i s list e \<gamma>)(*strict*)
     apply(simp add: prefix_def)
     apply (metis set_append1)
    apply(rename_tac i s list e \<gamma>)(*strict*)
    apply(rule valid_epda_pop_in_gamma)
     apply(rename_tac i s list e \<gamma>)(*strict*)
     apply(force)
    apply(rename_tac i s list e \<gamma>)(*strict*)
    apply(force)
   apply(rename_tac i s list e \<gamma>)(*strict*)
   apply(simp add: valid_epda_def)
  apply(rename_tac i s qa list option)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_basic_def)
  done

lemma F_EDPDA_RMPOE__configuration_rev_preserves_initial_configurations: "
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration_rev c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def Let_def F_EDPDA_RMPOE__relation_RL_TSstructure_def F_EDPDA_RMPOE_def)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def Let_def F_EDPDA_RMPOE__relation_RL_TSstructure_def F_EDPDA_RMPOE_def)
  apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RMPOE__relation_RL_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
  apply(rule epdaS.initial_configurations_are_get_accessible_configurations)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
   apply(rule F_EDPDA_RMPOE_preserves_epda)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE__configuration_rev_preserves_reachability_hlp: "
  F_EDPDA_RMPOE__relation_RL_TSstructure (F_EDPDA_RMPOE G2) G2
  \<Longrightarrow> epdaS.derivation_initial (F_EDPDA_RMPOE G2) d
  \<Longrightarrow> d i = Some (pair e c1)
  \<Longrightarrow> \<exists>d. epdaS.derivation_initial G2 d \<and> (\<exists>i. get_configuration (d i) = Some (F_EDPDA_RMPOE__configuration_rev c1))"
  apply(induct i arbitrary: e c1)
   apply(rename_tac e c1)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(case_tac "epdaS_conf_state c1")
   apply(rename_tac e c1 q list option)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="der1 \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = epdaS_conf_scheduler c1, epdaS_conf_stack = list @ epdaS_conf_stack c1\<rparr>"
      in exI)
   apply(rename_tac e c1 q list option)(*strict*)
   apply(rule conjI)
    apply(rename_tac e c1 q list option)(*strict*)
    prefer 2
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac e c1 q list option)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c1 q list option)(*strict*)
   apply(rule conjI)
    apply(rename_tac c1 q list option)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac c1 q list option)(*strict*)
   apply(simp add: der1_def)
   apply(subgoal_tac "F_EDPDA_RMPOE__configuration_rev c1 \<in> epdaS_initial_configurations G2")
    apply(rename_tac c1 q list option)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(rename_tac c1 q list option)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_initial_configurations)
    apply(rename_tac c1 q list option)(*strict*)
    apply(force)
   apply(rename_tac c1 q list option)(*strict*)
   apply(force)
  apply(rename_tac i e c1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> epdaS_step_relation (F_EDPDA_RMPOE G2) c1 e2 c2")
   apply(rename_tac i e c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac i e c1)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
    apply(rename_tac i e c1)(*strict*)
    apply(force)
   apply(rename_tac i e c1)(*strict*)
   apply(force)
  apply(rename_tac i e c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c1 e1 e2 c1a)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_EDPDA_RMPOE G2)")
   apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
  apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
   apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def)
  apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(erule disjE)
   apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(clarsimp)
   apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
   apply(rule_tac
      x="derivation_append da (der2 (F_EDPDA_RMPOE__configuration_rev c1a) e (F_EDPDA_RMPOE__configuration_rev c1)) ia"
      in exI)
   apply(rule conjI)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation_initial)
      apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
     apply(force)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
      apply(simp add: epdaS.derivation_initial_def)
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
     apply(clarsimp)
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma> w)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma> w c)(*strict*)
     apply(rule_tac
      t="x @ [\<gamma>]"
      and s="edge_pop e @ c"
      in ssubst)
      apply(rename_tac i c1 e1 c1a da ia x e \<gamma> w c)(*strict*)
      apply(force)
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma> w c)(*strict*)
     apply (metis left_quotient_word_removes_right_addition_hlp option.sel)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "da ia")
     apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
     apply(clarsimp)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma> a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma> a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac i c1 e1 c1a da ia x e \<gamma> option)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac i c1 e1 c1a da ia x e \<gamma>)(*strict*)
   apply(rule_tac
      x="Suc ia"
      in exI)
   apply(simp add: get_configuration_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
  apply(erule disjE)
   apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(clarsimp)
   apply(rename_tac i c1 e1 c1a da ia q w a)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="ia"
      in exI)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def epdaS_step_relation_def)
   apply(simp add: option_to_list_def)
  apply(rename_tac i c1 e1 e2 c1a da ia)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(clarsimp)
  apply(rename_tac i c1 e1 c1a da ia q w a)(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="ia"
      in exI)
  apply(clarsimp)
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def epdaS_step_relation_def)
  apply(simp add: option_to_list_def)
  apply(clarsimp)
  done

lemma F_EDPDA_RMPOE__configuration_rev_preserves_reachability: "
  F_EDPDA_RMPOE__relation_RL_TSstructure (F_EDPDA_RMPOE G2) G2
  \<Longrightarrow> c1 \<in> ATS.get_accessible_configurations epdaS_initial_configurations epdaS_step_relation (F_EDPDA_RMPOE G2)
  \<Longrightarrow> F_EDPDA_RMPOE__configuration_rev c1 \<in> ATS.get_accessible_configurations epdaS_initial_configurations epdaS_step_relation G2"
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e. d i = Some (pair e c1)")
   apply(rename_tac d i a)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(force)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e)(*strict*)
  apply(thin_tac "get_configuration (Some (pair e c1)) = Some c1")
  apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_reachability_hlp)
    apply(rename_tac d i e)(*strict*)
    apply(force)
   apply(rename_tac d i e)(*strict*)
   apply(force)
  apply(rename_tac d i e)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE__relation_RL_step_simulation_maps_to_derivation: "
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<Longrightarrow> F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_EDPDA_RMPOE__relation_RL_step_simulation_def)
  apply(case_tac "epdaS_conf_state c1")
  apply(rename_tac q list option)(*strict*)
  apply(case_tac "epdaS_conf_state c1'")
  apply(rename_tac q list option qa lista optiona)(*strict*)
  apply(clarsimp)
  apply(case_tac "option")
   apply(rename_tac q list option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(rename_tac q list qa lista optiona)(*strict*)
   apply(rename_tac q1 w1 q2 w2 e)
   apply(rename_tac q1 w1 q2 w2 e)(*strict*)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac q list option qa lista optiona a)(*strict*)
  apply(clarsimp)
  apply(rename_tac q list qa lista optiona a)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac q list qa lista optiona a)(*strict*)
   apply(clarsimp)
   apply(rename_tac q list qa lista a)(*strict*)
   prefer 2
   apply(rename_tac q list qa lista optiona a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac q list qa lista a aa)(*strict*)
   apply(rule epdaS.der1_is_derivation)
  apply(rename_tac q list qa lista a)(*strict*)
  apply(rule epdaS.der2_is_derivation)
  apply(rename_tac q1 w1 q2 w2 X)
  apply(rename_tac q1 w1 q2 w2 X)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta G1")
   apply(rename_tac q1 w1 q2 w2 X)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac q1 w1 q2 w2 X)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
   apply(rename_tac q1 w1 q2 w2 X)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def)
  apply(rename_tac q1 w1 q2 w2 X)(*strict*)
  apply(simp add: Let_def)
  apply(thin_tac "e1 \<in> epda_delta (F_EDPDA_RMPOE G2)")
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(erule disjE)
   apply(rename_tac q1 w1 q2 w2 X)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac q1 w1 q2 w2 X)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def epdaS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac q1 w1 q2 w2 X)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def)
   apply(clarsimp)
  apply(rename_tac q1 w1 q2 w2 X)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_final_def)
  apply(clarsimp)
  apply(rename_tac q1 w1 q2 w2 X x e \<gamma>)(*strict*)
  apply(subgoal_tac "X=\<gamma>")
   apply(rename_tac q1 w1 q2 w2 X x e \<gamma>)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac q1 w1 q2 w2 X x e \<gamma>)(*strict*)
  apply(clarsimp)
  apply(rename_tac q1 w1 q2 w2 x e \<gamma>)(*strict*)
  apply(subgoal_tac "q1 = edge_src e \<and> w1 = x \<and> q2 = edge_trg e \<and> w2 = []")
   apply(rename_tac q1 w1 q2 w2 x e \<gamma>)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac q1 w1 q2 w2 x e \<gamma>)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e \<gamma>)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(erule disjE)
   apply(rename_tac x e \<gamma>)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_before_pop_def)
  apply(rename_tac x e \<gamma>)(*strict*)
  apply(erule disjE)
   apply(rename_tac x e \<gamma>)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac x e \<gamma>)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__states_last_of_pop_def)
   apply(rename_tac x e \<gamma>)(*strict*)
   apply(erule disjE)
    apply(rename_tac x e \<gamma>)(*strict*)
    prefer 2
    apply(simp add: F_EDPDA_RMPOE__states_basic_def)
   apply(rename_tac x e \<gamma>)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__states_context_of_top_def)
   apply(clarsimp)
   apply(rename_tac x e \<gamma> ea)(*strict*)
   apply(rule_tac
      a="e"
      in HOL.theI2)
     apply(rename_tac x e \<gamma> ea)(*strict*)
     apply(clarsimp)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac x e \<gamma> ea c ca)(*strict*)
     apply(rule_tac
      t="left_quotient_word (edge_pop e) (x @ [\<gamma>])"
      and s="Some c"
      in ssubst)
      apply(rename_tac x e \<gamma> ea c ca)(*strict*)
      apply (metis left_quotient_word_removes_right_addition)
     apply(rename_tac x e \<gamma> ea c ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac x e \<gamma> ea xa)(*strict*)
    prefer 2
    apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x e \<gamma> ea xa c ca w xb)(*strict*)
    apply(subgoal_tac "left_quotient_word (edge_pop e) (x @ [\<gamma>]) = Some c")
     apply(rename_tac x e \<gamma> ea xa c ca w xb)(*strict*)
     prefer 2
     apply (metis left_quotient_word_removes_right_addition)
    apply(rename_tac x e \<gamma> ea xa c ca w xb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="xb@w"
      in exI)
    apply(clarsimp)
   apply(rename_tac x e \<gamma> ea xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x e \<gamma> ea xa xb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x e \<gamma> ea xa xb c ca)(*strict*)
   apply(subgoal_tac "left_quotient_word (edge_pop e) (x @ [\<gamma>]) = Some c")
    apply(rename_tac x e \<gamma> ea xa xb c ca)(*strict*)
    prefer 2
    apply (metis left_quotient_word_removes_right_addition)
   apply(rename_tac x e \<gamma> ea xa xb c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "xb=c")
    apply(rename_tac x e \<gamma> ea xa xb c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x e \<gamma> ea xa c ca)(*strict*)
    apply(case_tac xa)
    apply(rename_tac x e \<gamma> ea xa c ca edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac e)
    apply(rename_tac x e \<gamma> ea xa c ca edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x \<gamma> ea c ca edge_popa edge_eventa edge_popaa edge_pusha edge_trga)(*strict*)
    apply (metis append_injective1)
   apply(rename_tac x e \<gamma> ea xa xb c ca)(*strict*)
   apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)
   apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac " (F_EDPDA_RMPOE__configuration_rev c1) \<in> epdaS.get_accessible_configurations G2 \<and> (case (Some \<gamma>) of None \<Rightarrow> True | Some x \<Rightarrow> prefix [x] (epdaS_conf_stack c1)) ")
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    apply(case_tac "x2=x3")
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
     apply(force)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "e1=e3")
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
     apply(case_tac e1)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(case_tac e3)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    apply(rule_tac
      c="F_EDPDA_RMPOE__configuration_rev c1"
      and G="G2"
      in epdaS.apply_is_forward_edge_deterministic_accessible)
        apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
        apply(force)
       apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
       apply(force)
      apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
      apply(force)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
     apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
     apply(clarsimp)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
     apply(rule_tac
      t="x1@\<gamma>#w"
      and s="edge_pop e1@x3@w"
      in ssubst)
      apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
      apply(force)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
     apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e1,epdaS_conf_scheduler=epdaS_conf_scheduler c1',epdaS_conf_stack=edge_push e1@x3@w\<rparr>"
      in exI)
     apply(clarsimp)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
    apply(clarsimp)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
    apply(rule_tac
      t="x1@\<gamma>#w"
      and s="edge_pop e3@x2@w"
      in ssubst)
     apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
     apply(force)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4 w)(*strict*)
    apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e1,epdaS_conf_scheduler=epdaS_conf_scheduler c1',epdaS_conf_stack=edge_push e3@x2@w\<rparr>"
      in exI)
    apply(clarsimp)
   apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
   apply(rule conjI)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(simp add: prefix_def epdaS_step_relation_def)
    apply(force)
   apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_reachability)
    apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
    apply(force)
   apply(rename_tac x1 e1 \<gamma> e2 e3 x2 x3 x4)(*strict*)
   apply(force)
  apply(rename_tac x e \<gamma>)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__states_bottom_on_top_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(subgoal_tac "butlast (edge_pop ea) @ [epda_box G2]= edge_pop ea")
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(simp add: suffix_def)
   apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e ea c)(*strict*)
  apply(subgoal_tac "left_quotient_word (edge_pop e) (edge_pop ea)=Some c")
   apply(rename_tac e ea c)(*strict*)
   prefer 2
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac e ea c)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      a="e"
      in HOL.theI2)
    apply(rename_tac e ea c)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ea c x)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def prefix_def)
   apply(clarsimp)
   apply(rename_tac e ea c x w xa)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac e ea c x w xa ca)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack c1 \<in> must_terminated_by (epda_gamma (F_EDPDA_RMPOE G2)) (epda_box (F_EDPDA_RMPOE G2))")
    apply(rename_tac e ea c x w xa ca)(*strict*)
    apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac e ea c x w xa ca a)(*strict*)
    apply(case_tac w)
     apply(rename_tac e ea c x w xa ca a)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ea c x w xa ca a aa list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
     apply(rename_tac e ea c x w xa ca a aa list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac e ea c x w xa ca a aa list)(*strict*)
    apply(thin_tac "w=aa#list")
    apply(clarsimp)
    apply(rename_tac e ea c x xa ca w')(*strict*)
    apply(simp add: F_EDPDA_RMPOE_def Let_def)
   apply(rename_tac e ea c x w xa ca)(*strict*)
   apply(rule epda_stack_is_must_terminated_by)
    apply(rename_tac e ea c x w xa ca)(*strict*)
    apply(rule F_EDPDA_RMPOE_preserves_epda)
    apply(rename_tac e ea c x w xa ca)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(rename_tac e ea c x w xa ca)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
  apply(rename_tac e ea c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea c x xa)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac e ea c x xa ca)(*strict*)
  apply(thin_tac "left_quotient_word (edge_pop e) (ca @ [epda_box G2]) = Some c")
  apply(rename_tac e2 e w2 e1 w1 w)
  apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
  apply(clarsimp)
  apply(case_tac "w1=w2")
   apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
   apply(clarsimp)
   apply(rename_tac e2 e w2 e1 w)(*strict*)
   apply(case_tac e1)
   apply(rename_tac e2 e w2 e1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e2)
   apply(rename_tac e2 e w2 e1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w2 w edge_popa edge_eventa edge_popaa edge_pusha edge_trga)(*strict*)
   apply (metis append_injr)
  apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
  apply(rule_tac
      c="F_EDPDA_RMPOE__configuration_rev c1"
      and G="G2"
      in epdaS.apply_is_forward_edge_deterministic_accessible)
      apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
      apply(force)
     apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
     apply(force)
    apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
    apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_reachability)
     apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
     apply(force)
    apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
    apply(force)
   apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
   apply(clarsimp)
   apply(rename_tac e2 e w2 e1 w1 w wa)(*strict*)
   apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e2,epdaS_conf_scheduler=epdaS_conf_scheduler c1',epdaS_conf_stack=edge_push e1@w1@wa\<rparr>"
      in exI)
   apply(clarsimp)
  apply(rename_tac e2 e w2 e1 w1 w)(*strict*)
  apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
  apply(clarsimp)
  apply(rename_tac e2 e w2 e1 w1 w wa)(*strict*)
  apply(rule_tac
      x="\<lparr>epdaS_conf_state=edge_trg e2,epdaS_conf_scheduler=epdaS_conf_scheduler c1',epdaS_conf_stack=edge_push e2@w2@wa\<rparr>"
      in exI)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="(case epdaS_conf_state c1 of cons_tuple3 q1 w1 X1 \<Rightarrow> case epdaS_conf_state c1' of cons_tuple3 q2 w2 X2 \<Rightarrow> (case X1 of None \<Rightarrow> der1 c2 | Some X1' \<Rightarrow> (case X2 of None \<Rightarrow> der2 (F_EDPDA_RMPOE__configuration_rev c1) ((THE e'. e' \<in> epda_delta G2 \<and> edge_src e'=q1 \<and> edge_trg e'=q2 \<and> edge_event e'=edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = w1@[X1'] \<and> edge_push e' @ x = edge_push e1))) (F_EDPDA_RMPOE__configuration_rev c1') | Some X2' \<Rightarrow> der1 c2)))"
      in exI)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule_tac
      ?G1.0="G1"
      and ?c2.0="c2"
      and ?c1.0="c1"
      and ?e1.0="e1"
      and ?c1'.0="c1'"
      in F_EDPDA_RMPOE__relation_RL_step_simulation_maps_to_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_RL_step_simulation_def)
     apply(case_tac "epdaS_conf_state c1")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option)(*strict*)
     apply(clarsimp)
     apply(case_tac "epdaS_conf_state c1'")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
     apply(clarsimp)
     apply(case_tac "option")
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona a)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
     apply(case_tac "optiona")
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(subgoal_tac "(get_configuration (case_DT_tuple3 (\<lambda>q1 w1 X1. case epdaS_conf_state c1' of cons_tuple3 q2 w2 X2 \<Rightarrow> (case X1 of None \<Rightarrow> der1 c2 | Some X1' \<Rightarrow> (case X2 of None \<Rightarrow> (der2 (F_EDPDA_RMPOE__configuration_rev c1) (THE e'. e' \<in> epda_delta G2 \<and> edge_src e' = q1 \<and> edge_trg e' = q2 \<and> edge_event e' = edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = w1 @ [X1'] \<and> edge_push e' @ x = edge_push e1)) (F_EDPDA_RMPOE__configuration_rev c1')) | Some X2' \<Rightarrow> der1 c2))) (epdaS_conf_state c1) 0)) = Some c2")
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
   apply(case_tac "epdaS_conf_state c1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list option)(*strict*)
   apply(clarsimp)
   apply(case_tac "epdaS_conf_state c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(case_tac "optiona")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista)(*strict*)
    apply(case_tac "option")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
    apply(simp add: der2_def)
    apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
    prefer 2
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
    apply(case_tac "option")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a aa)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule_tac
      ca="c2"
      in epdaS.derivation_belongs)
       apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: get_configuration_def)
      apply(case_tac "epdaS_conf_state c1")
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option)(*strict*)
      apply(clarsimp)
      apply(case_tac "epdaS_conf_state c1'")
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
      apply(clarsimp)
      apply(case_tac "optiona")
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
       apply(clarsimp)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista)(*strict*)
       apply(case_tac "option")
        apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista)(*strict*)
        apply(clarsimp)
        apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista)(*strict*)
        apply(simp add: der1_def)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
       apply(clarsimp)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona a)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
      apply(case_tac "option")
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a)(*strict*)
       apply(clarsimp)
       apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
       apply(simp add: der1_def)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista a aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a aa)(*strict*)
      apply(simp add: der1_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
     apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(rule_tac
      A="epdaS.get_accessible_configurations G1"
      in set_mp)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply (rule epdaS.get_accessible_configurations_are_configurations)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rule F_EDPDA_RMPOE_preserves_epda)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_RL_step_simulation_def)
    apply(case_tac "epdaS_conf_state c1")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option)(*strict*)
    apply(clarsimp)
    apply(case_tac "epdaS_conf_state c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
    apply(clarsimp)
    apply(case_tac "option")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
    apply(case_tac "optiona")
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    prefer 2
    apply(simp add: F_EDPDA_RMPOE_def epda_step_labels_def F_EDPDA_RMPOE__relation_RL_TSstructure_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(case_tac "epdaS_conf_state c1")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list option)(*strict*)
   apply(clarsimp)
   apply(case_tac "epdaS_conf_state c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(case_tac "option")
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(clarsimp)
    apply(thin_tac "epdaS.derivation G2 (der1 c2)")
    apply(thin_tac "get_configuration (der1 c2 0) = Some c2")
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply(rule epdaS.der2_preserves_get_accessible_configurations)
       apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
       apply(rule F_EDPDA_RMPOE_preserves_epda)
       apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
      apply(rule epdaS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
    apply(simp add: Let_def)
    apply(simp add: F_EDPDA_RMPOE__edges_def)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply(simp add: F_EDPDA_RMPOE__edges_final_def epdaS_step_relation_def)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(erule disjE)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply(simp add: F_EDPDA_RMPOE__edges_append_list_def epdaS_step_relation_def option_to_list_def)
     apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def option_to_list_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list option qa lista optiona a)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
    apply(simp add: der2_def get_configuration_def)
    apply(rule epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rule F_EDPDA_RMPOE_preserves_epda)
      apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista optiona a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a aa)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a aa)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a aa)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
    apply(rule epdaS.der2_preserves_get_accessible_configurations)
      apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rule F_EDPDA_RMPOE_preserves_epda)
      apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
      apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
     apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def epdaS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def epdaS_step_relation_def option_to_list_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def option_to_list_def)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def epda_step_labels_def F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(fold der2_def)
  apply(subgoal_tac "\<exists>e1X e2X c1X c2X. (der2 (F_EDPDA_RMPOE__configuration_rev c1) (THE e'. e' \<in> epda_delta G2 \<and> edge_src e' = q \<and> edge_trg e' = qa \<and> edge_event e' = edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = list @ [a] \<and> edge_push e' @ x = edge_push e1)) (F_EDPDA_RMPOE__configuration_rev c1')) 0 = Some (pair e1X c1X) \<and> (der2 (F_EDPDA_RMPOE__configuration_rev c1) (THE e'. e' \<in> epda_delta G2 \<and> edge_src e' = q \<and> edge_trg e' = qa \<and> edge_event e' = edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = list @ [a] \<and> edge_push e' @ x = edge_push e1)) (F_EDPDA_RMPOE__configuration_rev c1')) (Suc 0) = Some (pair (Some e2X) c2X) \<and> epdaS_step_relation G2 c1X e2X c2X")
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc 0"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a e1X e2X c1X c2X)(*strict*)
  apply(simp add: der2_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
  apply(fold der2_def)
  apply(thin_tac "epdaS.derivation G2 (der2 (F_EDPDA_RMPOE__configuration_rev c1) (THE e'. e' \<in> epda_delta G2 \<and> edge_src e' = q \<and> edge_trg e' = qa \<and> edge_event e' = edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = list @ [a] \<and> edge_push e' @ x = edge_push e1)) (F_EDPDA_RMPOE__configuration_rev c1'))")
  apply(rename_tac G1 G2 c1 c2 e1 c1' q list qa lista a)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a)(*strict*)
  apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__configuration_rev_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a w wa)(*strict*)
  apply(erule disjE)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a w wa)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a w wa)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def epdaS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a w wa)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' q list qa lista a w wa)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_final_def epdaS_step_relation_def)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_configuration F_EDPDA_RMPOE__relation_RL_TSstructure F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_step_relation_step_simulation epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RMPOE__relation_RL_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RMPOE__relation_RL_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RMPOE__relation_RL_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RMPOE__relation_RL_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RMPOE__relation_RL_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_EDPDA_RMPOE__configuration_rev_preserves_marking_configurations: "
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> F_EDPDA_RMPOE__configuration_rev c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def F_EDPDA_RMPOE_def)
   apply(case_tac "epdaS_conf_state c1")
   apply(rename_tac q list option)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def F_EDPDA_RMPOE_def)
   apply(case_tac "epdaS_conf_state c1")
   apply(rename_tac q list option)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def F_EDPDA_RMPOE_def Let_def)
   apply(clarsimp)
  apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      t="ca"
      and s="the (get_configuration (derivation_append deri1 (der2 c1 e1 c1') deri1n i))"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration_rev c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_marking_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(simp add: epdaS.get_accessible_configurations_def)
    apply(rule_tac
      x="derivation_append deri1 (der2 c1 e1 c1') deri1n "
      in exI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation_initial)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
       apply (rule F_EDPDA_RMPOE_preserves_epda)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
       apply (metis epdaS.derivation_initial_is_derivation)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(rule epdaS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c option b)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      x="Suc deri1n"
      in exI)
    apply(simp add: get_configuration_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_EDPDA_RMPOE__configuration_rev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__configuration_rev_def derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_configuration F_EDPDA_RMPOE__relation_RL_TSstructure F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_RL_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(case_tac "epdaS_conf_state c")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca q list option)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_RL_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(case_tac "epdaS_conf_state c")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca q list option)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_configuration F_EDPDA_RMPOE__relation_RL_effect F_EDPDA_RMPOE__relation_RL_TSstructure F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_RL_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_RL_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EDPDA_RMPOE__configuration_rev c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(case_tac "epdaS_conf_state c'")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c q list option)(*strict*)
   apply(clarsimp)
   apply(case_tac "epdaS_conf_state c")
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c q list option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(subgoal_tac "c'=c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x="F_EDPDA_RMPOE__configuration_rev c1'"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c ca)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_LR_initial_configuration_def get_configuration_def F_EDPDA_RMPOE__configuration_def)
   apply(case_tac "epdaS_conf_state c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c ca q list option)(*strict*)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def F_EDPDA_RMPOE__configuration_rev_def)
   apply(case_tac "epdaS_conf_state c")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c ca q list option qa lista optiona)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(subgoal_tac "F_EDPDA_RMPOE__configuration_rev c=ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_EDPDA_RMPOE__configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(rule_tac
      x="deri2n+n"
      in exI)
  apply(simp add: derivation_append_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_EDPDA_RMPOE__relation_RL_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_EDPDA_RMPOE__relation_RL_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c')")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea caa e)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x="F_EDPDA_RMPOE__configuration_rev c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x="f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def F_EDPDA_RMPOE__configuration_rev_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(case_tac "epdaS_conf_state c'")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e q list option)(*strict*)
   apply(clarsimp)
   apply(case_tac "epdaS_conf_state ca")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e q list option qa lista optiona)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_EDPDA_RMPOE__relation_RL_configuration F_EDPDA_RMPOE__relation_RL_initial_configuration F_EDPDA_RMPOE__relation_RL_effect F_EDPDA_RMPOE__relation_RL_TSstructure F_EDPDA_RMPOE__relation_RL_initial_simulation F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_epda"
  (* configurations1 *)
  "epdaS_configurations"
  (* initial_configurations1 *)
  "epdaS_initial_configurations"
  (* step_labels1 *)
  "epda_step_labels"
  (* step_relation1 *)
  "epdaS_step_relation"
  (* effects1 *)
  "epda_effects"
  (* marking_condition1 *)
  "epdaS_marking_condition"
  (* marked_effect1 *)
  "epdaS_marked_effect"
  (* unmarked_effect1 *)
  "epdaS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_EDPDA_RMPOE__relation_RL_configuration"
  (* relation_initial_configuration *)
  "F_EDPDA_RMPOE__relation_RL_initial_configuration"
  (* relation_effect *)
  "F_EDPDA_RMPOE__relation_RL_effect"
  (* relation_TSstructure *)
  "F_EDPDA_RMPOE__relation_RL_TSstructure"
  (* relation_initial_simulation *)
  "F_EDPDA_RMPOE__relation_RL_initial_simulation"
  (* relation_step_simulation *)
  "F_EDPDA_RMPOE__relation_RL_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms)
  done

lemma F_EDPDA_RMPOE_preserves_lang2: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_EDPDA_RMPOE G)"
  apply(rule_tac
      t="epdaS.marked_language G"
      and s="epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_EDPDA_RMPOE G)"
      and s="epdaS.finite_marked_language (F_EDPDA_RMPOE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RMPOE__relation_RL_effect SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="F_EDPDA_RMPOE G"
      in epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  done

lemma F_EDPDA_RMPOE_preserves_unmarked_language2: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.unmarked_language G \<supseteq> epdaS.unmarked_language (F_EDPDA_RMPOE G)"
  apply(rule_tac
      t="epdaS.unmarked_language G"
      and s="epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis (full_types)  epdaS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_EDPDA_RMPOE G)"
      and s="epdaS.finite_unmarked_language (F_EDPDA_RMPOE G)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply(rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(subgoal_tac "left_total_on (F_EDPDA_RMPOE__relation_RL_effect SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="F_EDPDA_RMPOE G"
      in epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_effect_def)
  done

theorem F_EDPDA_RMPOE_preserves_unmarked_language: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_EDPDA_RMPOE G)"
  apply(rule order_antisym)
   apply (metis F_EDPDA_RMPOE_preserves_unmarked_language1)
  apply (metis F_EDPDA_RMPOE_preserves_unmarked_language2)
  done

theorem F_EDPDA_RMPOE_preserves_lang: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_EDPDA_RMPOE G)"
  apply(rule order_antisym)
   apply (metis F_EDPDA_RMPOE_preserves_lang1)
  apply (metis F_EDPDA_RMPOE_preserves_lang2)
  done

definition F_EDPDA_RMPOE__relation_LRB_initial_simulation :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LRB_initial_simulation G1 G2 c1 c' d \<equiv>
  d = der1 (F_EDPDA_RMPOE__configuration_rev c1)"

definition F_EDPDA_RMPOE__relation_LRB_step_simulation :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda_step_label
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event , 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LRB_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  case epdaS_conf_state c1 of cons_tuple3 q1 w1 X1 \<Rightarrow>
  (case epdaS_conf_state c1' of cons_tuple3 q2 w2 X2 \<Rightarrow>
  (case X1 of
      None \<Rightarrow> d = der1 c2
      | Some X1' \<Rightarrow>
          (case X2 of
            None \<Rightarrow> d = der2
                (F_EDPDA_RMPOE__configuration_rev c1)
                ((SOME e'. e' \<in> epda_delta G2
                    \<and> edge_src e' = q1
                    \<and> edge_trg e' = q2
                    \<and> edge_event e' = edge_event e
                    \<and> (\<exists>x. edge_pop e' @ x = w1 @ [X1']
                    \<and> edge_push e' @ x = edge_push e))) (F_EDPDA_RMPOE__configuration_rev c1')
            | Some X2' \<Rightarrow> d = der1 c2)))"

definition F_EDPDA_RMPOE__relation_LRB_configuration :: "
  (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> (('state, 'stack list, 'stack option) DT_tuple3, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__relation_LRB_configuration G1 G2 c1 c2 \<equiv>
  F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2
  \<and> c1 \<in> epdaS_configurations G1
  \<and> c2 = F_EDPDA_RMPOE__configuration_rev c1"

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRLB_inst_AX_initial_contained: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 c1 c2 \<longrightarrow> F_EDPDA_RMPOE__relation_LRB_configuration G1 G2 c1 c2))"
  apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def F_EDPDA_RMPOE__relation_LRB_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.AX_TSstructure_relation_TSstructure1_belongs epdaS_inst_AX_initial_configuration_belongs subsetD)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRLB_inst_AX_relation_initial_simulationB: "
  (\<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>c2. F_EDPDA_RMPOE__relation_LRB_configuration G1 G2 c1 c2 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_EDPDA_RMPOE__relation_RL_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_EDPDA_RMPOE__relation_LRB_initial_simulation G1 G2 c1 c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> get_configuration (d2 n) = Some c2)))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_RL_initial_configuration_def F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LRB_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G2 c1 c2)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply (metis F_EDPDA_RMPOE__configuration_rev_preserves_initial_configurations F_EDPDA_RMPOE__relation_LRB_configuration_def)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 c2)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_EDPDA_RMPOE__relation_LRB_configuration_def)
  done

lemma F_EDPDA_RMPOE__configuration_rev_preserves_configurations2: "
  valid_epda G2
  \<Longrightarrow> c1' \<in> epdaS_configurations (F_EDPDA_RMPOE G2)
  \<Longrightarrow> F_EDPDA_RMPOE__configuration_rev c1' \<in> epdaS_configurations G2"
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def epdaS_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(case_tac q)
  apply(rename_tac q i s qa list option)(*strict*)
  apply(clarsimp)
  apply(rename_tac i s qa list option)(*strict*)
  apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s list e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s list e)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s list e)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac i s list e x c a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G2]"
      in disjE)
    apply(rename_tac i s list e x c a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s list e x c a aa ab)(*strict*)
    apply(rule_tac
      A="set list"
      in set_mp)
     apply(rename_tac i s list e x c a aa ab)(*strict*)
     apply(rule_tac
      B="set (a @ [epda_box G2])"
      in subset_trans)
      apply(rename_tac i s list e x c a aa ab)(*strict*)
      apply (metis set_app_subset)
     apply(rename_tac i s list e x c a aa ab)(*strict*)
     apply(rule set_concat_subset)
      apply(rename_tac i s list e x c a aa ab)(*strict*)
      apply(force)
     apply(rename_tac i s list e x c a aa ab)(*strict*)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i s list e x c a aa ab)(*strict*)
    apply(force)
   apply(rename_tac i s list e x c a aa)(*strict*)
   apply(rule_tac
      A="set (a @ [epda_box G2])"
      in set_mp)
    apply(rename_tac i s list e x c a aa)(*strict*)
    apply(rule set_concat_subset)
     apply(rename_tac i s list e x c a aa)(*strict*)
     apply(force)
    apply(rename_tac i s list e x c a aa)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s list e x c a aa)(*strict*)
   apply (metis set_append_contra1)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s e)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s e)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac i s e x a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G2]"
      in disjE)
    apply(rename_tac i s e x a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s e x a aa ab)(*strict*)
    apply(rule_tac
      A="set a"
      in set_mp)
     apply(rename_tac i s e x a aa ab)(*strict*)
     apply(force)
    apply(rename_tac i s e x a aa ab)(*strict*)
    apply(force)
   apply(rename_tac i s e x a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s e x aa)(*strict*)
   apply (metis Diff_subset in_set_butlastD subsetD)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s e)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s e)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s e)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac i s e x a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G2]"
      in disjE)
    apply(rename_tac i s e x a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s e x a aa ab)(*strict*)
    apply(rule_tac
      A="set a"
      in set_mp)
     apply(rename_tac i s e x a aa ab)(*strict*)
     apply(force)
    apply(rename_tac i s e x a aa ab)(*strict*)
    apply(erule_tac
      P="x = epda_box G2"
      in disjE)
     apply(rename_tac i s e x a aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac i s e a aa ab)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac i s e x a aa ab)(*strict*)
    apply(force)
   apply(rename_tac i s e x a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s e x aa)(*strict*)
   apply (metis Diff_subset subsetD)
  apply(rename_tac i s qa list option)(*strict*)
  apply(erule disjE)
   apply(rename_tac i s qa list option)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s list e \<gamma>)(*strict*)
   apply(subgoal_tac "valid_epda_step_label G2 e")
    apply(rename_tac i s list e \<gamma>)(*strict*)
    prefer 2
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i s list e \<gamma>)(*strict*)
   apply(simp add: valid_epda_step_label_def)
   apply(simp add: may_terminated_by_def must_terminated_by_def kleene_star_def append_language_def strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac i s list e \<gamma> x a aa)(*strict*)
   apply(erule_tac
      P="edge_pop e = a @ [epda_box G2]"
      in disjE)
    apply(rename_tac i s list e \<gamma> x a aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s list e \<gamma> x a aa ab)(*strict*)
    apply(rule_tac
      A="set a"
      in set_mp)
     apply(rename_tac i s list e \<gamma> x a aa ab)(*strict*)
     apply(force)
    apply(rename_tac i s list e \<gamma> x a aa ab)(*strict*)
    apply(erule disjE)
     apply(rename_tac i s list e \<gamma> x a aa ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac i s list e \<gamma> x a aa)(*strict*)
     apply(simp add: suffix_def prefix_def)
     apply(clarsimp)
     apply(rename_tac i s list e \<gamma> x a aa c)(*strict*)
     apply(case_tac c)
      apply(rename_tac i s list e \<gamma> x a aa c)(*strict*)
      apply(force)
     apply(rename_tac i s list e \<gamma> x a aa c ab lista)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac i s list e \<gamma> x a aa c ab lista)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac i s list e \<gamma> x a aa c ab lista)(*strict*)
     apply(thin_tac "c=ab#lista")
     apply(clarsimp)
    apply(rename_tac i s list e \<gamma> x a aa ab)(*strict*)
    apply(clarsimp)
    apply(rename_tac i s list e \<gamma> x a ab)(*strict*)
    apply(simp add: suffix_def prefix_def)
    apply(clarsimp)
    apply(rename_tac i s list e \<gamma> x a ab c)(*strict*)
    apply(case_tac c)
     apply(rename_tac i s list e \<gamma> x a ab c)(*strict*)
     apply(force)
    apply(rename_tac i s list e \<gamma> x a ab c aa lista)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac i s list e \<gamma> x a ab c aa lista)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac i s list e \<gamma> x a ab c aa lista)(*strict*)
    apply(thin_tac "c=aa#lista")
    apply(clarsimp)
   apply(rename_tac i s list e \<gamma> x a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i s list e \<gamma> x aa)(*strict*)
   apply(simp add: suffix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac i s list e \<gamma> x aa c)(*strict*)
   apply (metis Diff_subset set_app_subset subsetD)
  apply(rename_tac i s qa list option)(*strict*)
  apply(clarsimp)
  done

lemma epdaS_epdaS_F_EDPDA_RMPOE_StateSimRLB_inst_AX_relation_step_simulationB: "
  \<forall>G1 G2. F_EDPDA_RMPOE__relation_RL_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_EDPDA_RMPOE__relation_LRB_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. c1' \<in> epdaS_configurations G1 \<longrightarrow> epdaS_step_relation G1 c1' e1 c1 \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> (\<exists>n. the (get_configuration (d2 n)) = c2 \<and> F_EDPDA_RMPOE__relation_LRB_step_simulation G1 G2 c1' e1 c1 c2 d2 \<and> maximum_of_domain d2 n \<and> F_EDPDA_RMPOE__relation_LRB_configuration G1 G2 c1' (the (get_configuration (d2 0))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LRB_configuration_def F_EDPDA_RMPOE__relation_RL_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__relation_LRB_step_simulation_def)
  apply(case_tac "epdaS_conf_state c1'")
  apply(rename_tac G2 c1 e1 c1' q list option)(*strict*)
  apply(clarsimp)
  apply(case_tac "epdaS_conf_state c1")
  apply(rename_tac G2 c1 e1 c1' q list option qa lista optiona)(*strict*)
  apply(clarsimp)
  apply(case_tac option)
   apply(rename_tac G2 c1 e1 c1' q list option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(rule_tac
      x="der1 (F_EDPDA_RMPOE__configuration_rev c1)"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
      apply(simp add: der1_def)
     apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations2)
      apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
     apply (metis)
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(simp add: get_configuration_def der1_def)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    apply(simp add: maximum_of_domain_def get_configuration_def der1_def)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(simp add: maximum_of_domain_def get_configuration_def der1_def)
   apply(simp add: epda_step_labels_def)
   apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
    apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
    prefer 2
    apply(simp add: F_EDPDA_RMPOE_def)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona)(*strict*)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def F_EDPDA_RMPOE__configuration_rev_def epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona w)(*strict*)
   apply(case_tac "edge_trg e1")
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona w qb listb option)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list w qb listb option)(*strict*)
   apply(case_tac "edge_src e1")
   apply(rename_tac G2 c1 e1 c1' q list w qb listb option qa lista optiona)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w qb listb option qa lista)(*strict*)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' w qb listb option qa lista)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w qb listb option qa lista)(*strict*)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' w qb listb option qa lista)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
    apply(rename_tac G2 c1 c1' qa lista a)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac G2 c1 e1 c1' w qb listb option qa lista)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 c1' w qa lista a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac G2 c1 e1 c1' q list option qa lista optiona a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' q list qa lista optiona a)(*strict*)
  apply(case_tac "optiona")
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona a)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
   prefer 2
   apply(rename_tac G2 c1 e1 c1' q list qa lista optiona a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
    apply(rename_tac G2 c1 e1 c1' q list qa lista a aa)(*strict*)
    prefer 2
    apply(simp add: epda_step_labels_def F_EDPDA_RMPOE_def)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a aa)(*strict*)
   apply(simp add: Let_def)
   apply(simp add: F_EDPDA_RMPOE__edges_def F_EDPDA_RMPOE__configuration_rev_def epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a aa w)(*strict*)
   apply(case_tac "edge_trg e1")
   apply(rename_tac G2 c1 e1 c1' q list qa lista a aa w qb listb option)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' q list a aa w qb listb)(*strict*)
   apply(case_tac "edge_src e1")
   apply(rename_tac G2 c1 e1 c1' q list a aa w qb listb qa lista option)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' a aa w qb listb qa lista)(*strict*)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' a aa w qb listb qa lista)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' a aa w qb listb qa lista)(*strict*)
   apply(erule disjE)
    apply(rename_tac G2 c1 e1 c1' a aa w qb listb qa lista)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' a aa w qb listb qa lista)(*strict*)
   apply(simp add: option_to_list_def)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
  apply(rule_tac
      x="der2 (F_EDPDA_RMPOE__configuration_rev c1') (SOME e'. e' \<in> epda_delta G2 \<and> edge_src e' = q \<and> edge_trg e' = qa \<and> edge_event e' = edge_event e1 \<and> (\<exists>x. edge_pop e' @ x = list @ [a] \<and> edge_push e' @ x = edge_push e1)) (F_EDPDA_RMPOE__configuration_rev c1)"
      in exI)
  apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
    prefer 2
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(simp add: der2_def maximum_of_domain_def)
    apply(simp add: get_configuration_def)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
    apply (rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations2)
     apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' q list qa lista a)(*strict*)
  apply(case_tac c1)
  apply(rename_tac G2 c1 e1 c1' q list qa lista a epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(case_tac c1')
  apply(rename_tac G2 c1 e1 c1' q list qa lista a epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack epdaS_conf_stateaa epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 e1 q list qa lista a epdaS_conf_scheduler epdaS_conf_stack epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(rename_tac w s w' s')
  apply(rename_tac G2 e1 q list qa lista a w s w' s')(*strict*)
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
  apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G2 in \<lparr>epda_states = STATES, epda_events = epda_events G2, epda_gamma = epda_gamma G2, epda_delta = F_EDPDA_RMPOE__edges G2 STATES, epda_initial = cons_tuple3 (epda_initial G2) [] None, epda_box = epda_box G2, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G2\<rparr>)")
   apply(rename_tac G2 e1 q list qa lista a w s w' s')(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def epda_step_labels_def)
  apply(rename_tac G2 e1 q list qa lista a w s w' s')(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def F_EDPDA_RMPOE__configuration_rev_def epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G2 e1 q list qa lista a w wa)(*strict*)
  apply(erule disjE)
   apply(rename_tac G2 e1 q list qa lista a w wa)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def F_EDPDA_RMPOE__edges_append_option_def)
   apply(erule disjE)
    apply(rename_tac G2 e1 q list qa lista a w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 e1 q list qa lista a w wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G2 e1 q list qa lista a w wa)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_final_def)
  apply(clarsimp)
  apply(rename_tac G2 w wa x e \<gamma>)(*strict*)
  apply(rule_tac
      P="\<lambda> e'. e' \<in> epda_delta G2 \<and> edge_src e' = edge_src e \<and> edge_trg e' = edge_trg e \<and> edge_event e' = edge_event e \<and> (\<exists>xa. edge_pop e' @ xa = x @ [\<gamma>] \<and> edge_push e' @ xa = edge_push e @ the (left_quotient_word (edge_pop e) (x @ [\<gamma>])))"
      and a="e"
      in someI2)
   apply(rename_tac G2 w wa x e \<gamma>)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G2 w wa x e \<gamma> c)(*strict*)
   apply (metis left_quotient_word_removes_right_addition option.sel)
  apply(rename_tac G2 w wa x e \<gamma> xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 w wa x e \<gamma> xa xaa)(*strict*)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: epdaS_step_relation_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G2 w wa x e \<gamma> xa xaa c)(*strict*)
  apply(subgoal_tac "left_quotient_word (edge_pop e) (x @ [\<gamma>]) = Some c")
   apply(rename_tac G2 w wa x e \<gamma> xa xaa c)(*strict*)
   prefer 2
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac G2 w wa x e \<gamma> xa xaa c)(*strict*)
  apply(clarsimp)
  apply(thin_tac "left_quotient_word (edge_pop e) (x @ [\<gamma>]) = Some c")
  apply(rule_tac
      t="x@\<gamma>#wa"
      and s="edge_pop xa @ xaa@wa"
      in ssubst)
   apply(rename_tac G2 w wa x e \<gamma> xa xaa c)(*strict*)
   apply(force)
  apply(rename_tac G2 w wa x e \<gamma> xa xaa c)(*strict*)
  apply(rule_tac
      x="xaa@wa"
      in exI)
  apply(clarsimp)
  done

lemma F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_final_final: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations (F_EDPDA_RMPOE G)
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e1 c1
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e2 c2
  \<Longrightarrow> \<forall>e1 e2. epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e1 (F_EDPDA_RMPOE__configuration_rev c1) \<and> epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e2 (F_EDPDA_RMPOE__configuration_rev c2) \<longrightarrow> e1 = e2
  \<Longrightarrow> e1 \<in> F_EDPDA_RMPOE__edges_final G (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e2 \<in> F_EDPDA_RMPOE__edges_final G (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_EDPDA_RMPOE__edges_final_def epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa e ea \<gamma>' w)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="ea"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac xa e ea \<gamma>' w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa e ea \<gamma>' w)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa e ea \<gamma>' w epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e ea \<gamma>' w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa e ea \<gamma>' w c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa e ea \<gamma>' w c ca)(*strict*)
   apply (metis left_quotient_word_removes_right_addition_hlp option.sel)
  apply(rename_tac xa e ea \<gamma>' w c ca)(*strict*)
  apply (metis left_quotient_word_removes_right_addition_hlp option.sel)
  done

lemma F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app1: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations (F_EDPDA_RMPOE G)
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e1 c1
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e2 c2
  \<Longrightarrow> \<forall>e1 e2. epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e1 (F_EDPDA_RMPOE__configuration_rev c1) \<and>epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e2 (F_EDPDA_RMPOE__configuration_rev c2) \<longrightarrow>e1 = e2
  \<Longrightarrow> e1 \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e2 \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_EDPDA_RMPOE__edges_append_list_def epdaS_step_relation_def)
  apply(clarsimp)
  done

lemma F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app2_hlp: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> cons_tuple3 q (w @ [a]) None \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> cons_tuple3 q w None \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> cons_tuple3 q w (Some a) \<in> F_EDPDA_RMPOE__states G
  \<Longrightarrow> False"
  apply(simp add: F_EDPDA_RMPOE__states_def)
  apply(simp add: F_EDPDA_RMPOE__states_before_pop_def F_EDPDA_RMPOE__states_bottom_on_top_def F_EDPDA_RMPOE__states_last_of_pop_def F_EDPDA_RMPOE__states_context_of_top_def F_EDPDA_RMPOE__states_basic_def)
  apply(erule_tac
      P="\<exists>e. q = edge_src e \<and> e \<in> epda_delta G \<and> strict_prefix (w @ [a]) (edge_pop e)"
      in disjE)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      P="\<exists>ea. edge_src e = edge_src ea \<and> ea \<in> epda_delta G \<and> strict_prefix w (edge_pop ea)"
      in disjE)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea)(*strict*)
    apply(erule disjE)
     apply(rename_tac e ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea eb)(*strict*)
     apply(simp add: strict_prefix_def suffix_def)
     apply(clarsimp)
     apply(rename_tac e ea eb c ca cb)(*strict*)
     apply(subgoal_tac "valid_epda_step_label G e")
      apply(rename_tac e ea eb c ca cb)(*strict*)
      prefer 2
      apply(simp add: valid_epda_def)
     apply(rename_tac e ea eb c ca cb)(*strict*)
     apply(simp add: valid_epda_step_label_def)
     apply(clarsimp)
     apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
     apply(clarsimp)
     apply(rename_tac e ea eb c ca cb a aa)(*strict*)
     apply(case_tac c)
      apply(rename_tac e ea eb c ca cb a aa)(*strict*)
      apply(force)
     apply(rename_tac e ea eb c ca cb a aa ab list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac e ea eb c ca cb a aa ab list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac e ea eb c ca cb a aa ab list)(*strict*)
     apply(thin_tac "c=ab#list")
     apply(erule_tac
      P="edge_pop e = a @ [epda_box G]"
      in disjE)
      apply(rename_tac e ea eb c ca cb a aa ab list)(*strict*)
      apply(force)
     apply(rename_tac e ea eb c ca cb a aa ab list)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea eb)(*strict*)
    apply(simp add: prefix_def strict_prefix_def suffix_def)
    apply(clarsimp)
    apply(rename_tac e ea eb c ca cb)(*strict*)
    apply(subgoal_tac "w @ [a] \<in> prefix_closure (F_EDPDA_RMPOE__pop_components G (edge_src eb))")
     apply(rename_tac e ea eb c ca cb)(*strict*)
     apply(force)
    apply(rename_tac e ea eb c ca cb)(*strict*)
    apply(unfold F_EDPDA_RMPOE__pop_components_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rule_tac
      x="edge_pop e"
      in exI)
    apply(rule conjI)
     apply(rename_tac e ea eb c ca cb)(*strict*)
     apply(rule_tac
      x="e"
      in exI)
     apply(clarsimp)
    apply(rename_tac e ea eb c ca cb)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      P="\<exists>ea. edge_src e = edge_src ea \<and> w = butlast (edge_pop ea) \<and> a = epda_box G \<and> ea \<in> epda_delta G \<and> edge_pop ea \<sqsupseteq> [epda_box G]"
      in disjE)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea)(*strict*)
    apply(simp add: prefix_def strict_prefix_def suffix_def)
    apply(clarsimp)
    apply(rename_tac e ea c ca)(*strict*)
    apply(erule disjE)
     apply(rename_tac e ea c ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea c eb)(*strict*)
     apply(subgoal_tac "valid_epda_step_label G e")
      apply(rename_tac e ea c eb)(*strict*)
      prefer 2
      apply(simp add: valid_epda_def)
     apply(rename_tac e ea c eb)(*strict*)
     apply(simp add: valid_epda_step_label_def)
     apply(clarsimp)
     apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
     apply(clarsimp)
     apply(rename_tac e ea c eb a aa)(*strict*)
     apply(case_tac c)
      apply(rename_tac e ea c eb a aa)(*strict*)
      apply(force)
     apply(rename_tac e ea c eb a aa ab list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac e ea c eb a aa ab list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac e ea c eb a aa ab list)(*strict*)
     apply(thin_tac "c=ab#list")
     apply(erule_tac
      P="edge_pop e = a @ [epda_box G]"
      in disjE)
      apply(rename_tac e ea c eb a aa ab list)(*strict*)
      apply(force)
     apply(rename_tac e ea c eb a aa ab list)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ea c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea c)(*strict*)
    apply(subgoal_tac "valid_epda_step_label G e")
     apply(rename_tac e ea c)(*strict*)
     prefer 2
     apply(simp add: valid_epda_def)
    apply(rename_tac e ea c)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(clarsimp)
    apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
    apply(clarsimp)
    apply(rename_tac e ea c a aa)(*strict*)
    apply(case_tac c)
     apply(rename_tac e ea c a aa)(*strict*)
     apply(force)
    apply(rename_tac e ea c a aa ab list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac e ea c a aa ab list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac e ea c a aa ab list)(*strict*)
    apply(thin_tac "c=ab#list")
    apply(erule_tac
      P="edge_pop e = a @ [epda_box G]"
      in disjE)
     apply(rename_tac e ea c a aa ab list)(*strict*)
     apply(force)
    apply(rename_tac e ea c a aa ab list)(*strict*)
    apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea c)(*strict*)
   apply(simp add: prefix_def strict_prefix_def suffix_def)
   apply(erule disjE)
    apply(rename_tac e ea c)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea c ca eb)(*strict*)
    apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>v. (\<forall>e. edge_src e = edge_src eb \<longrightarrow> v = edge_pop e \<longrightarrow> e \<notin> epda_delta G) \<or> (\<forall>c. edge_pop eb @ a # c \<noteq> v)"
      in allE)
    apply(rename_tac e ea c ca eb)(*strict*)
    apply(erule disjE)
     apply(rename_tac e ea c ca eb)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca eb)(*strict*)
    apply(erule_tac
      x="ca"
      and P="\<lambda>c. edge_pop eb \<noteq> c @ [epda_box G]"
      in allE)
    apply(force)
   apply(rename_tac e ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea ca)(*strict*)
   apply(erule_tac
      x="edge_pop e"
      in allE)
   apply(erule disjE)
    apply(rename_tac e ea ca)(*strict*)
    apply(force)
   apply(rename_tac e ea ca)(*strict*)
   apply(erule_tac
      x="ca"
      in allE)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      P="\<exists>ea. edge_src e = edge_src ea \<and> ea \<in> epda_delta G \<and> strict_prefix w (edge_pop ea)"
      in disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: prefix_def strict_prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac e ea c)(*strict*)
   apply(erule disjE)
    apply(rename_tac e ea c)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea c eb ca)(*strict*)
    apply(erule_tac
      x="ca"
      in allE)
    apply(force)
   apply(rename_tac e ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea c eb ca)(*strict*)
   apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>x. (\<forall>ea. edge_src ea = edge_src eb \<longrightarrow> x = edge_pop ea \<longrightarrow> ea \<notin> epda_delta G) \<or> (\<forall>c. w @ a # c \<noteq> x)"
      in allE)
   apply(rename_tac e ea c eb ca)(*strict*)
   apply(erule disjE)
    apply(rename_tac e ea c eb ca)(*strict*)
    apply(force)
   apply(rename_tac e ea c eb ca)(*strict*)
   apply(erule_tac
      x="ca"
      and P="\<lambda>c. edge_pop e \<noteq> c @ [epda_box G]"
      in allE)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      P="\<exists>ea. edge_src e = edge_src ea \<and> w = butlast (edge_pop ea) \<and> a = epda_box G \<and> ea \<in> epda_delta G \<and> edge_pop ea \<sqsupseteq> [epda_box G]"
      in disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: prefix_def strict_prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac e ea c)(*strict*)
   apply(erule disjE)
    apply(rename_tac e ea c)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea c eb)(*strict*)
    apply(erule_tac
      x="c"
      and P="\<lambda>c. edge_pop e \<noteq> c @ [epda_box G]"
      in allE)
    apply(force)
   apply(rename_tac e ea c)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="c"
      in allE)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea eb c)(*strict*)
   apply(simp add: prefix_def strict_prefix_def suffix_def)
   apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>x. (\<forall>eb. edge_src eb = edge_src ea \<longrightarrow> x = edge_pop eb \<longrightarrow> eb \<notin> epda_delta G) \<or> (\<forall>c. edge_pop eb @ a # c \<noteq> x)"
      in allE)
   apply(rename_tac e ea eb c)(*strict*)
   apply(erule disjE)
    apply(rename_tac e ea eb c)(*strict*)
    apply(force)
   apply(rename_tac e ea eb c)(*strict*)
   apply(erule_tac
      x="[]"
      and P="\<lambda>c. edge_pop eb @ a # c \<noteq> edge_pop e"
      in allE)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(simp add: prefix_def strict_prefix_def suffix_def)
  apply(erule_tac
      x="edge_pop e"
      and P="\<lambda>x. (\<forall>eb. edge_src eb = edge_src ea \<longrightarrow> x = edge_pop eb \<longrightarrow> eb \<notin> epda_delta G) \<or> (\<forall>c. a # c \<noteq> x)"
      in allE)
  apply(rename_tac e ea)(*strict*)
  apply(erule disjE)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(erule_tac
      x="[]"
      and P="\<lambda>c. edge_pop e \<noteq> c @ [epda_box G]"
      in allE)
  apply(force)
  done

lemma F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app2: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> c \<in> ATS.get_accessible_configurations epdaS_initial_configurations epdaS_step_relation (F_EDPDA_RMPOE G)
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e1 c1
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e2 c2
  \<Longrightarrow> \<forall>e1 e2. epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e1 (F_EDPDA_RMPOE__configuration_rev c1) \<and> epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e2 (F_EDPDA_RMPOE__configuration_rev c2) \<longrightarrow> e1 = e2
  \<Longrightarrow> e1 \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e2 \<in> F_EDPDA_RMPOE__edges_append_option (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_EDPDA_RMPOE__edges_append_list_def F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac qa wa a)(*strict*)
  apply(case_tac c)
  apply(rename_tac qa wa a epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac qa wa a epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stackaa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac qa wa a epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stackaa epdaS_conf_stateb epdaS_conf_schedulerb epdaS_conf_stackb)(*strict*)
  apply(clarsimp)
  apply(rename_tac qa wa a epdaS_conf_stacka epdaS_conf_schedulerb)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__configuration_rev_def)
  apply(rename_tac q w a s i)
  apply(rename_tac q w a s i)(*strict*)
  apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app2_hlp)
      apply(rename_tac q w a s i)(*strict*)
      apply(force)+
  done

lemma F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app2_app2: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> c \<in> ATS.get_accessible_configurations epdaS_initial_configurations epdaS_step_relation (F_EDPDA_RMPOE G)
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e1 c1
  \<Longrightarrow> epdaS_step_relation (F_EDPDA_RMPOE G) c e2 c2
  \<Longrightarrow> \<forall>e1 e2. epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e1 (F_EDPDA_RMPOE__configuration_rev c1) \<and> epdaS_step_relation G (F_EDPDA_RMPOE__configuration_rev c) e2 (F_EDPDA_RMPOE__configuration_rev c2) \<longrightarrow> e1 = e2
  \<Longrightarrow> e1 \<in> F_EDPDA_RMPOE__edges_append_option (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e2 \<in> F_EDPDA_RMPOE__edges_append_option (F_EDPDA_RMPOE__states G)
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_EDPDA_RMPOE__edges_append_list_def F_EDPDA_RMPOE__edges_append_option_def epdaS_step_relation_def)
  apply(clarsimp)
  done

theorem F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible: "
  valid_epda G
  \<Longrightarrow> epda_no_nil_popping_edges G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (F_EDPDA_RMPOE G)"
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e2 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e1)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e2)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e1) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e2) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta (F_EDPDA_RMPOE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_EDPDA_RMPOE G)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "epdaS.is_forward_edge_deterministic_accessible G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="F_EDPDA_RMPOE__configuration_rev c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="F_EDPDA_RMPOE__configuration_rev c1"
      in allE)
   apply(erule_tac
      x="F_EDPDA_RMPOE__configuration_rev c2"
      in allE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(subgoal_tac "F_EDPDA_RMPOE__configuration_rev c \<in> epdaS.get_accessible_configurations G")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(thin_tac "F_EDPDA_RMPOE__configuration_rev c \<notin> epdaS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(rule_tac
      ?c1.0="c"
      in epdaS_epdaS_F_EDPDA_RMPOE_StateSimRL.get_accessible_configurations_transfer)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(rule F_EDPDA_RMPOE__configuration_rev_preserves_configurations)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply (metis F_EDPDA_RMPOE_preserves_epda epdaS.get_accessible_configurations_are_configurations2)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
     apply(simp add: F_EDPDA_RMPOE__relation_RL_TSstructure_def)
    apply(rename_tac c c1 c2 e1 e2 cA cB)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__relation_RL_configuration_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1=edge_src e2")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "e1 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G in \<lparr>epda_states = STATES, epda_events = epda_events G, epda_gamma = epda_gamma G, epda_delta = F_EDPDA_RMPOE__edges G STATES, epda_initial = cons_tuple3 (epda_initial G) [] None, epda_box = epda_box G, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G\<rparr>)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE_def epda_step_labels_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (let STATES = F_EDPDA_RMPOE__states G in \<lparr>epda_states = STATES, epda_events = epda_events G, epda_gamma = epda_gamma G, epda_delta = F_EDPDA_RMPOE__edges G STATES, epda_initial = cons_tuple3 (epda_initial G) [] None, epda_box = epda_box G, epda_marking = (\<lambda>q. cons_tuple3 q [] None) ` epda_marking G\<rparr>)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE_def epda_step_labels_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: Let_def)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(thin_tac "epdaS.is_forward_edge_deterministic_accessible G")
  apply(thin_tac "edge_src e2 = epdaS_conf_state c")
  apply(thin_tac "option_to_list (edge_event e1) \<sqsubseteq> epdaS_conf_scheduler c")
  apply(thin_tac "option_to_list (edge_event e2) \<sqsubseteq> epdaS_conf_scheduler c")
  apply(thin_tac "edge_pop e1 \<sqsubseteq> epdaS_conf_stack c")
  apply(thin_tac "edge_pop e2 \<sqsubseteq> epdaS_conf_stack c")
  apply(thin_tac "e1 \<in> epda_delta (F_EDPDA_RMPOE G)")
  apply(thin_tac "e2 \<in> epda_delta (F_EDPDA_RMPOE G)")
  apply(thin_tac "edge_src e1 = epdaS_conf_state c")
  apply(erule_tac
      P="e1 \<in> F_EDPDA_RMPOE__edges_final G (F_EDPDA_RMPOE__states G)"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_final_final)
           apply(rename_tac c c1 c2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__edges_final_def F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__edges_final_def F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_EDPDA_RMPOE__edges_final G (F_EDPDA_RMPOE__states G)"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__edges_final_def F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(simp add: epdaS_step_relation_def F_EDPDA_RMPOE__edges_final_def F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      P="e1 \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states G)"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app1)
           apply(rename_tac c c1 c2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app2)
          apply(rename_tac c c1 c2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule disjE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(rule sym)
   apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app1_app2)
          apply(rename_tac c c1 c2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible_app2_app2)
         apply(rename_tac c c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE_annotation_increases_on_internal_part: "
  valid_epda M
  \<Longrightarrow> G = F_EDPDA_RMPOE M
  \<Longrightarrow> epdaH_step_relation G c1 e c2
  \<Longrightarrow> epdaH_conf_state c1 = cons_tuple3 q1 w1 opt1
  \<Longrightarrow> epdaH_conf_state c2 = cons_tuple3 q2 w2 opt2
  \<Longrightarrow> 0 < length (w1 @ option_to_list opt1)
  \<Longrightarrow> 0 < length (w2 @ option_to_list opt2)
  \<Longrightarrow> length (w1 @ option_to_list opt1) < length (w2 @ option_to_list opt2) \<and> q1 = q2"
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "e \<in> F_EDPDA_RMPOE__edges M (F_EDPDA_RMPOE__states M)")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(clarsimp)
   apply(rename_tac w e \<gamma>)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac w)(*strict*)
  apply(erule disjE)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
   apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
  apply(clarsimp)
  apply(rename_tac w a)(*strict*)
  apply(simp add: option_to_list_def)
  done

lemma F_EDPDA_RMPOE_annotation_increases_on_internal_part_mult: "
  valid_epda M
  \<Longrightarrow> G = F_EDPDA_RMPOE M
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> (\<forall>y. y\<ge>n + m \<and> y \<le> n + m + Suc x \<longrightarrow> (\<exists>e c q w opt. d y = Some (pair e c) \<and> epdaH_conf_state c = cons_tuple3 q w opt \<and> 0 < length (w @ option_to_list opt)))
  \<Longrightarrow> d (n + m) = Some (pair e1 c1)
  \<Longrightarrow> d (n + m + Suc x) = Some (pair e2 c2)
  \<Longrightarrow> epdaH_conf_state c1 = cons_tuple3 q1 w1 opt1
  \<Longrightarrow> epdaH_conf_state c2 = cons_tuple3 q2 w2 opt2
  \<Longrightarrow> length (w1 @ option_to_list opt1) < length (w2 @ option_to_list opt2) \<and> q1 = q2"
  apply(induct x arbitrary: e2 c2 q2 w2 opt2)
   apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
    prefer 2
    apply(rule_tac
      n="n+m"
      and m="Suc (n+m)"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
     apply(force)
    apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
    apply(force)
   apply(rename_tac e2 c2 q2 w2 opt2)(*strict*)
   apply(erule exE)+
   apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
   apply(rule_tac
      ?c1.0="c1a"
      and ?c2.0="c2a"
      in F_EDPDA_RMPOE_annotation_increases_on_internal_part)
         apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
         apply(force)
        apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
        apply(force)
       apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
    apply(erule_tac
      x="n+m"
      in allE)
    apply(clarsimp)
   apply(rename_tac e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
   apply(erule_tac
      x="n+m+Suc 0"
      in allE)
   apply(clarsimp)
  apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc(n+m+x)"
      and m="Suc (Suc(n+m+x))"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
    apply(force)
   apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
   apply(force)
  apply(rename_tac x e2 c2 q2 w2 opt2)(*strict*)
  apply(erule exE)+
  apply(rename_tac x e2 c2 q2 w2 opt2 e1a e2a c1a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a c1a)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac c1a)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a c1a epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac qx ix sx)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a qx ix sx)(*strict*)
  apply(case_tac qx)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a qx ix sx q list option)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx q list option)(*strict*)
  apply(rename_tac qy wy opty)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx qy wy opty)(*strict*)
  apply(erule_tac
      x="qy"
      in meta_allE)
  apply(erule_tac
      x="wy"
      in meta_allE)
  apply(erule_tac
      x="opty"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
  apply(subgoal_tac "length wy + length (option_to_list opty)<length w2 + length (option_to_list opt2) \<and> q1=q2")
   apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
   apply(force)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
   prefer 2
   apply(rule_tac
      e="e2a"
      and ?c1.0="\<lparr>epdaH_conf_state = cons_tuple3 q1 wy opty, epdaH_conf_history = ix, epdaH_conf_stack = sx\<rparr>"
      and ?c2.0="c2"
      in F_EDPDA_RMPOE_annotation_increases_on_internal_part)
         apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
         apply(force)
        apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
        apply(force)
       apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
       apply(force)
      apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
      apply(force)
     apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
     apply(force)
    apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
    apply(force)
   apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
   apply(erule_tac
      x="Suc (Suc (n + m + x))"
      in allE)
   apply(clarsimp)
  apply(rename_tac x c2 q2 w2 opt2 e1a e2a ix sx wy opty)(*strict*)
  apply(force)
  done

lemma F_EDPDA_RMPOE_no_infinite_derivation_within_annotated_states: "
  valid_epda M
  \<Longrightarrow> G = F_EDPDA_RMPOE M
  \<Longrightarrow> valid_epda (F_EDPDA_RMPOE M)
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> (\<forall>m\<ge>n. \<exists>e c q w opt. d m = Some (pair e c) \<and> epdaH_conf_state c = cons_tuple3 q w opt \<and> 0 < length (w @ option_to_list opt))
  \<Longrightarrow> Q"
  apply(subgoal_tac "finite {epdaH_conf_state c | c. \<exists>m\<ge>n. \<exists>e. d m = Some (pair e c)}")
   apply(subgoal_tac "\<not> finite {epdaH_conf_state c | c. \<exists>m\<ge>n. \<exists>e. d m = Some (pair e c)}")
    apply(force)
   apply(rule_tac
      f="\<lambda>m. epdaH_conf_state (the(get_configuration (d m)))"
      and B="{x. x\<ge>n}"
      in inj_on_preserves_inifinteness)
     prefer 2
     apply(thin_tac "\<forall>m\<ge>n. \<exists>e c q w opt. d m = Some (pair e c) \<and> epdaH_conf_state c = cons_tuple3 q w opt \<and> 0 < length (w @ option_to_list opt)")
     apply(thin_tac "finite {epdaH_conf_state c |c. \<exists>m\<ge>n. \<exists>e. d m = Some (pair e c)}")
     apply(rule not_finite_nat_UNIV)
    apply(simp add: inj_on_def)
    apply(clarsimp)
    apply(rename_tac x y)(*strict*)
    apply(case_tac "x=y")
     apply(rename_tac x y)(*strict*)
     apply(force)
    apply(rename_tac x y)(*strict*)
    apply(case_tac "x<y")
     apply(rename_tac x y)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>k. x+Suc k=y")
      apply(rename_tac x y)(*strict*)
      apply(clarsimp)
      apply(rename_tac x k)(*strict*)
      apply(subgoal_tac "\<exists>k. n+k=x")
       apply(rename_tac x k)(*strict*)
       apply(clarsimp)
       apply(rename_tac k ka)(*strict*)
       apply(erule_tac x="n+ka" in allE')
       apply(erule_tac x="n+ka+Suc k" in allE')
       apply(erule_tac
      P="n \<le> n + ka"
      in impE)
        apply(rename_tac k ka)(*strict*)
        apply(force)
       apply(rename_tac k ka)(*strict*)
       apply(erule impE)
        apply(rename_tac k ka)(*strict*)
        apply(force)
       apply(rename_tac k ka)(*strict*)
       apply(erule exE)+
       apply(rename_tac k ka e ea c ca)(*strict*)
       apply(erule conjE)+
       apply(erule exE)+
       apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
       apply(subgoal_tac "X" for X)
        apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
        prefer 2
        apply(rule_tac
      n="n"
      and m="ka"
      and x="k"
      in F_EDPDA_RMPOE_annotation_increases_on_internal_part_mult)
               apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
               apply(force)
              apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
              apply(force)
             apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
             apply(force)
            apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
            apply(force)
           apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
           apply(force)
          apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
          apply(force)
         apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
         apply(force)
        apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
        apply(force)
       apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
       apply(clarsimp)
       apply(rename_tac k ka e ea c ca qa w wa opt opta)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac x k)(*strict*)
      apply (metis le_iff_add)
     apply(rename_tac x y)(*strict*)
     apply (metis add_Suc_right less_iff_Suc_add)
    apply(rename_tac x y)(*strict*)
    apply(case_tac "y<x")
     apply(rename_tac x y)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>k. y+Suc k=x")
      apply(rename_tac x y)(*strict*)
      apply(clarsimp)
      apply(rename_tac y k)(*strict*)
      apply(subgoal_tac "\<exists>k. n+k=y")
       apply(rename_tac y k)(*strict*)
       apply(clarsimp)
       apply(rename_tac k ka)(*strict*)
       apply(erule_tac x="n+ka" in allE')
       apply(erule_tac x="n+ka+Suc k" in allE')
       apply(erule_tac
      P="n \<le> n + ka"
      in impE)
        apply(rename_tac k ka)(*strict*)
        apply(force)
       apply(rename_tac k ka)(*strict*)
       apply(erule impE)
        apply(rename_tac k ka)(*strict*)
        apply(force)
       apply(rename_tac k ka)(*strict*)
       apply(erule exE)+
       apply(rename_tac k ka e ea c ca)(*strict*)
       apply(erule conjE)+
       apply(erule exE)+
       apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
       apply(subgoal_tac "X" for X)
        apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
        prefer 2
        apply(rule_tac
      n="n"
      and m="ka"
      and x="k"
      in F_EDPDA_RMPOE_annotation_increases_on_internal_part_mult)
               apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
               apply(force)
              apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
              apply(force)
             apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
             apply(force)
            apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
            apply(force)
           apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
           apply(force)
          apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
          apply(force)
         apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
         apply(force)
        apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
        apply(force)
       apply(rename_tac k ka e ea c ca q qa w wa opt opta)(*strict*)
       apply(clarsimp)
       apply(rename_tac k ka e ea c ca qa w wa opt opta)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac y k)(*strict*)
      apply (metis le_iff_add)
     apply(rename_tac x y)(*strict*)
     apply (metis add_Suc_right less_iff_Suc_add)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rename_tac m)(*strict*)
   apply(erule_tac
      x="m"
      in allE)
   apply(clarsimp)
   apply(rename_tac m e c q w opt)(*strict*)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rule_tac
      B="epda_states (F_EDPDA_RMPOE M)"
      in finite_subset)
   apply(clarsimp)
   apply(rename_tac c m e)(*strict*)
   apply(erule_tac
      x="m"
      in allE)
   apply(clarsimp)
   apply(rename_tac c m e q w opt)(*strict*)
   apply(subgoal_tac "c \<in> epdaH_configurations (F_EDPDA_RMPOE M)")
    apply(rename_tac c m e q w opt)(*strict*)
    apply(simp add: epdaH_configurations_def)
    apply(clarsimp)
   apply(rename_tac c m e q w opt)(*strict*)
   apply(rule epdaH.belongs_configurations)
    apply(rename_tac c m e q w opt)(*strict*)
    apply(rule epdaH.derivation_initial_belongs)
     apply(rename_tac c m e q w opt)(*strict*)
     apply(force)
    apply(rename_tac c m e q w opt)(*strict*)
    apply(force)
   apply(rename_tac c m e q w opt)(*strict*)
   apply(force)
  apply(simp add: valid_epda_def)
  done

lemma F_EDPDA_RMPOE_enforces_epdaH_no_livelocks_from_marking_states: "
  valid_epda M
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible M
  \<Longrightarrow> epda_no_empty_steps_from_marking_states M
  \<Longrightarrow> G = F_EDPDA_RMPOE M
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states G"
  apply(subgoal_tac "valid_epda G")
   prefer 2
   apply(clarsimp)
   apply(rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(simp add: epdaH_no_livelocks_from_marking_states_def)
  apply(clarsimp)
  apply(rename_tac d n e c)(*strict*)
  apply(case_tac n)
   apply(rename_tac d n e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e c)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d e c)(*strict*)
    prefer 2
    apply(rule epdaH.some_position_has_details_at_0)
    apply(rule epdaH.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac d e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n e c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d e c n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d e c n)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      and m="Suc n"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d e c n)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d e c n)(*strict*)
    apply(force)
   apply(rename_tac d e c n)(*strict*)
   apply(force)
  apply(rename_tac d e c n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n e1 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d e c n e1 c1 w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d e c n e1 c1 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e c n e1 w epdaH_conf_historya)(*strict*)
  apply(case_tac c)
  apply(rename_tac d e c n e1 w epdaH_conf_historya epdaH_conf_statea epdaH_conf_historyaa epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w epdaH_conf_history)(*strict*)
  apply(rename_tac h)
  apply(rename_tac d e n e1 w h)(*strict*)
  apply(case_tac "(\<forall>m\<ge>Suc n. \<exists>e c q w opt. d m = Some (pair e c) \<and> epdaH_conf_state c = cons_tuple3 q w opt \<and> 0<length(w@option_to_list opt))")
   apply(rename_tac d e n e1 w h)(*strict*)
   apply(rule F_EDPDA_RMPOE_no_infinite_derivation_within_annotated_states)
       apply(rename_tac d e n e1 w h)(*strict*)
       apply(force)
      apply(rename_tac d e n e1 w h)(*strict*)
      apply(force)
     apply(rename_tac d e n e1 w h)(*strict*)
     apply(force)
    apply(rename_tac d e n e1 w h)(*strict*)
    apply(force)
   apply(rename_tac d e n e1 w h)(*strict*)
   apply(force)
  apply(rename_tac d e n e1 w h)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w h m)(*strict*)
  apply(case_tac "d m")
   apply(rename_tac d e n e1 w h m)(*strict*)
   apply(clarsimp)
   apply(case_tac "Suc n=m")
    apply(rename_tac d e n e1 w h m)(*strict*)
    apply(force)
   apply(rename_tac d e n e1 w h m)(*strict*)
   apply(rule_tac
      x="m"
      in exI)
   apply(force)
  apply(rename_tac d e n e1 w h m a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d e n e1 w h m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w h m option b)(*strict*)
  apply(case_tac b)
  apply(rename_tac d e n e1 w h m option b epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w h m option epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
  apply(rename_tac q h s)
  apply(rename_tac d e n e1 w ha m option q h s)(*strict*)
  apply(case_tac q)
  apply(rename_tac d e n e1 w ha m option q h s qa list optiona)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w ha m option h s qa optiona)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac d e n e1 w ha m option h s qa optiona)(*strict*)
   prefer 2
   apply(rename_tac d e n e1 w ha m option h s qa optiona a)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac d e n e1 w ha m option h s qa optiona)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n e1 w ha m option h s qa)(*strict*)
  apply(simp add: option_to_list_def)
  apply(rename_tac e h s q)
  apply(rename_tac d ea n e1 w ha m e h s q)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ea n e1 w ha m e h s q)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>m. Suc n\<le>m \<and> (\<exists>e q h s. d m = Some (pair e \<lparr>epdaH_conf_state = cons_tuple3 q [] None, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>))"
      and n="m"
      in ex_least_nat_le_prime)
   apply(rename_tac d ea n e1 w ha m e h s q)(*strict*)
   apply(force)
  apply(rename_tac d ea n e1 w ha m e h s q)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha m e h s q k eb qa hb sa)(*strict*)
  apply(thin_tac "d m = Some (pair e \<lparr>epdaH_conf_state = cons_tuple3 q [] None, epdaH_conf_history = h, epdaH_conf_stack = s\<rparr>)")
  apply(rename_tac d ea n e1 w ha m e h s q k eb qa hb sa)(*strict*)
  apply(thin_tac "k\<le>m")
  apply(subgoal_tac "edge_src ea \<in> (\<lambda>q. cons_tuple3 q [] None) ` epda_marking M")
   apply(rename_tac d ea n e1 w ha m e h s q k eb qa hb sa)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(rename_tac d ea n e1 w ha m e h s q k eb qa hb sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
  apply(subgoal_tac "ea \<in> F_EDPDA_RMPOE__edges M (F_EDPDA_RMPOE__states M)")
   apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
  apply(case_tac "Suc n=k")
   apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ea n e1 w ha qa q)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(erule disjE)
    apply(rename_tac d ea n e1 w ha qa q)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def)
    apply(clarsimp)
   apply(rename_tac d ea n e1 w ha qa q)(*strict*)
   apply(erule disjE)
    apply(rename_tac d ea n e1 w ha qa q)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac d ea n e1 w ha qa q)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
  apply(subgoal_tac "Suc n <k")
   apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
  apply(clarsimp)
  apply(case_tac k)
   apply(rename_tac d ea n e1 w ha k eb qa hb sa q)(*strict*)
   apply(clarsimp)
  apply(rename_tac d ea n e1 w ha k eb qa hb sa q nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha eb qa hb sa q nat)(*strict*)
  apply(rename_tac m)
  apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
   prefer 2
   apply(rule_tac
      n="m"
      and m="Suc m"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
     apply(simp add: epdaH.derivation_initial_def)
     apply(force)
    apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
    apply(force)
   apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
   apply(force)
  apply(rename_tac d ea n e1 w ha eb qa hb sa q m)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha qa hb sa q m e1a e2 c1)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 c1 wa)(*strict*)
  apply(erule_tac x="m" in allE')
  apply(clarsimp)
  apply(subgoal_tac "e2 \<in> F_EDPDA_RMPOE__edges M (F_EDPDA_RMPOE__states M)")
   apply(rename_tac d ea n e1 w ha qa q m e1a e2 c1 wa)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE_def Let_def)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 c1 wa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 c1 wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa epdaH_conf_history)(*strict*)
  apply(rename_tac h)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
  apply(subgoal_tac "e2 \<in> F_EDPDA_RMPOE__edges_final M (F_EDPDA_RMPOE__states M) \<or> e2 \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states M) \<or> e2 \<in> F_EDPDA_RMPOE__edges_append_option (F_EDPDA_RMPOE__states M)")
   apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
   prefer 2
   apply(simp add: F_EDPDA_RMPOE__edges_def)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
  apply(erule disjE)
   apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac d ea n e1 w ha qa q m e1a e2 wa h)(*strict*)
  apply(simp add: F_EDPDA_RMPOE__edges_final_def)
  apply(clarsimp)
  apply(rename_tac d ea n e1 w ha q m e1a wa h x e \<gamma>)(*strict*)
  apply(subgoal_tac "\<exists>k. n+Suc k=m")
   apply(rename_tac d ea n e1 w ha q m e1a wa h x e \<gamma>)(*strict*)
   apply(clarsimp)
   apply(rename_tac d ea n e1 w ha q e1a wa h x e \<gamma> k)(*strict*)
   apply(subgoal_tac "edge_src e = q")
    apply(rename_tac d ea n e1 w ha q e1a wa h x e \<gamma> k)(*strict*)
    apply(clarsimp)
    apply(rename_tac d ea n e1 w ha e1a wa h x e \<gamma> k)(*strict*)
    apply(subgoal_tac "(\<exists>y. edge_event e = Some y)")
     apply(rename_tac d ea n e1 w ha e1a wa h x e \<gamma> k)(*strict*)
     prefer 2
     apply(simp add: epda_no_empty_steps_from_marking_states_def)
    apply(rename_tac d ea n e1 w ha e1a wa h x e \<gamma> k)(*strict*)
    apply(clarsimp)
    apply(rename_tac d ea n e1 w ha e1a wa h x e \<gamma> k y)(*strict*)
    apply(rule_tac
      x="Suc (Suc (n + k))"
      in exI)
    apply(force)
   apply(rename_tac d ea n e1 w ha q e1a wa h x e \<gamma> k)(*strict*)
   prefer 2
   apply(rename_tac d ea n e1 w ha q m e1a wa h x e \<gamma>)(*strict*)
   apply (metis add_Suc_right less_iff_Suc_add)
  apply(rename_tac d ea n e1 w ha q e1a wa h x e \<gamma> k)(*strict*)
  apply(case_tac "ea")
  apply(rename_tac d ea n e1 w ha q e1a wa h x e \<gamma> k edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e1 w ha q e1a wa h x e \<gamma> k edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac po pu trg)
  apply(rename_tac d n e1 w ha q e1a wa h x e \<gamma> k po pu trg)(*strict*)
  apply(case_tac trg)
  apply(rename_tac d n e1 w ha q e1a wa h x e \<gamma> k po pu trg qa list option)(*strict*)
  apply(rename_tac q w opt)
  apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu trg q w opt)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
  apply(subgoal_tac "qa = q")
   apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
   prefer 2
   apply(subgoal_tac "\<lparr>edge_src = cons_tuple3 qa [] None, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_tuple3 q w opt\<rparr> \<in> F_EDPDA_RMPOE__edges_final M (F_EDPDA_RMPOE__states M) \<or> \<lparr>edge_src = cons_tuple3 qa [] None, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_tuple3 q w opt\<rparr> \<in> F_EDPDA_RMPOE__edges_append_list (F_EDPDA_RMPOE__states M) \<or> \<lparr>edge_src = cons_tuple3 qa [] None, edge_event = None, edge_pop = po, edge_push = pu, edge_trg = cons_tuple3 q w opt\<rparr> \<in> F_EDPDA_RMPOE__edges_append_option (F_EDPDA_RMPOE__states M) ")
    apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
    prefer 2
    apply(simp add: F_EDPDA_RMPOE__edges_def)
   apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
   apply(erule disjE)
    apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_final_def)
   apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
   apply(erule disjE)
    apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
    apply(simp add: F_EDPDA_RMPOE__edges_append_list_def)
    apply(clarsimp)
   apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
   apply(simp add: F_EDPDA_RMPOE__edges_append_option_def)
   apply(clarsimp)
  apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
  apply(case_tac k)
   apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n e1 wa ha qa e1a waa h x e \<gamma> k po pu q w opt nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt nat)(*strict*)
  apply(rename_tac k)
  apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc n"
      and m="0"
      and x="k"
      in F_EDPDA_RMPOE_annotation_increases_on_internal_part_mult)
          apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
          apply(force)
         apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
         apply(force)
        apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
        apply(force)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
       apply(rule allI)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
       apply(rule impI)
       apply(erule_tac
      x="y"
      in allE)
       apply(erule impE)
        apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
        apply(force)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
       apply(erule impE)
        apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
        apply(force)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
       apply(subgoal_tac "X" for X)
        apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
        prefer 2
        apply(rule_tac
      n="y"
      and m="Suc(Suc (n+k))"
      in epdaH.pre_some_position_is_some_position)
          apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
          apply(rule epdaH.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
         apply(force)
        apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
        apply(force)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y)(*strict*)
       apply(clarsimp)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y ea c)(*strict*)
       apply(case_tac c)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y ea c epdaH_conf_statea epdaH_conf_history epdaH_conf_stack)(*strict*)
       apply(clarsimp)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y ea epdaH_conf_state epdaH_conf_history epdaH_conf_stack)(*strict*)
       apply(case_tac "epdaH_conf_state")
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y ea epdaH_conf_state epdaH_conf_history epdaH_conf_stack qa list option)(*strict*)
       apply(clarsimp)
       apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k y ea epdaH_conf_history epdaH_conf_stack qa option)(*strict*)
       apply(simp add: option_to_list_def)
      apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
      apply(force)
     apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
     apply(force)
    apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
    apply(force)
   apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
   apply(force)
  apply(rename_tac d n e1 wa ha e1a waa h x e \<gamma> po pu q w opt k)(*strict*)
  apply(clarsimp)
  done

definition F_EDPDA_RMPOE__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__SpecInput G \<equiv>
  valid_epda G
  \<and> epdaS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epda_no_empty_steps_from_marking_states G
  \<and> epda_no_nil_popping_edges G"

definition F_EDPDA_RMPOE__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_RMPOE__SpecOutput Gi Go \<equiv>
  valid_epda Go
  \<and> epdaS.is_forward_edge_deterministic_accessible Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epda_no_nil_popping_edges Go
  \<and> epdaH_no_livelocks_from_marking_states Go
  \<and> epda_no_mass_popping_edges Go"

theorem F_EDPDA_RMPOE__SOUND: "
  F_EDPDA_RMPOE__SpecInput G
  \<Longrightarrow> F_EDPDA_RMPOE__SpecOutput G (F_EDPDA_RMPOE G)"
  apply(simp add: F_EDPDA_RMPOE__SpecOutput_def F_EDPDA_RMPOE__SpecInput_def)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RMPOE_preserves_epda)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RMPOE_preserves_lang)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(metis F_EDPDA_RMPOE_preserves_unmarked_language)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RMPOE_preserves_epda_no_nil_popping_edges)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EDPDA_RMPOE_enforces_epdaH_no_livelocks_from_marking_states)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_EDPDA_RMPOE_enforces_epda_no_mass_popping_edges)
  apply(force)
  done

end

