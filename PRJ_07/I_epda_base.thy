section {*I\_epda\_base*}
theory
  I_epda_base

imports
  PRJ_07__ENTRY

begin

record ('state, 'event, 'stack) epda_step_label =
  edge_src :: "'state"
  edge_event :: "'event option"
  edge_pop :: "'stack list"
  edge_push :: "'stack list"
  edge_trg :: "'state"

record ('state, 'event, 'stack) epda =
  epda_states :: "'state set"
  epda_events :: "'event set"
  epda_gamma :: "'stack set"
  epda_delta :: "('state, 'event, 'stack) epda_step_label set"
  epda_initial :: "'state"
  epda_box :: "'stack"
  epda_marking :: "'state set"

definition epda_effects :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list set"
  where
    "epda_effects G \<equiv>
  {w. set w \<subseteq> epda_events G}"

definition valid_epda_step_label :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "valid_epda_step_label G e \<equiv>
  edge_src e \<in> epda_states G
  \<and> edge_trg e \<in> epda_states G
  \<and> option_to_set (edge_event e) \<subseteq> epda_events G
  \<and> edge_pop e \<in> may_terminated_by (epda_gamma G) (epda_box G)
  \<and> edge_push e \<in> may_terminated_by (epda_gamma G) (epda_box G)
  \<and> (edge_pop e \<in> must_terminated_by (epda_gamma G) (epda_box G)
     \<longleftrightarrow> edge_push e \<in> must_terminated_by (epda_gamma G) (epda_box G))"

definition valid_epda :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_epda G \<equiv>
  finite (epda_states G)
  \<and> finite (epda_events G)
  \<and> finite (epda_gamma G)
  \<and> finite (epda_delta G)
  \<and> epda_initial G \<in> epda_states G
  \<and> epda_box G \<in> epda_gamma G
  \<and> epda_marking G \<subseteq> epda_states G
  \<and> (\<forall>e\<in> epda_delta G. valid_epda_step_label G e)"

lemma valid_epda_step_label_not_terminated_by_eq: "
  valid_epda_step_label M e
  \<Longrightarrow> (edge_pop e \<in> not_terminated_by (epda_gamma M) (epda_box M)
  \<longleftrightarrow> edge_push e \<in> not_terminated_by (epda_gamma M) (epda_box M))"
  apply(simp add: valid_epda_step_label_def)
  apply(simp add: may_terminated_by_def must_terminated_by_def not_terminated_by_def append_language_def kleene_star_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac a aa x)(*strict*)
   apply(force)
  apply(force)
  done

datatype ('state, 'event, 'stack) epda_destinations =
  state "'state"
  | edge "('state, 'event, 'stack)epda_step_label"

definition epda_destinations :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_destinations set"
  where
    "epda_destinations G \<equiv>
  state ` (epda_states G) \<union> edge ` (epda_delta G)"

definition epda_step_labels :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set"
  where
    "epda_step_labels G \<equiv>
  epda_delta G"

definition epda_no_empty_steps_from_marking_states :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epda_no_empty_steps_from_marking_states G \<equiv>
  \<forall>e.
    e \<in> epda_delta G
    \<longrightarrow> edge_src e \<in> epda_marking G
    \<longrightarrow> edge_event e \<noteq> None"

definition epda_empty_history :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_history G \<equiv>
  []"
declare epda_empty_history_def [simp add]

definition epda_empty_history_fragment :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_history_fragment G \<equiv>
  []"
declare epda_empty_history_fragment_def [simp add]

definition epda_empty_scheduler :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_scheduler G \<equiv>
  []"
declare epda_empty_scheduler_def [simp add]

definition epda_empty_scheduler_fragment :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_scheduler_fragment G \<equiv>
  []"
declare epda_empty_scheduler_fragment_def [simp add]

definition epda_fixed_schedulers :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list set"
  where
    "epda_fixed_schedulers G \<equiv>
  {[]}"
declare epda_fixed_schedulers_def [simp add]

definition epda_empty_fixed_scheduler :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_fixed_scheduler G \<equiv>
  []"
declare epda_empty_fixed_scheduler_def [simp add]

definition epda_empty_unfixed_scheduler :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list"
  where
    "epda_empty_unfixed_scheduler G \<equiv>
  []"
declare epda_empty_unfixed_scheduler_def [simp add]

definition epda_fixed_scheduler_extendable :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "epda_fixed_scheduler_extendable G w \<equiv>
  True"
declare epda_fixed_scheduler_extendable_def [simp add]

definition epda_unfixed_scheduler_extendable :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "epda_unfixed_scheduler_extendable G w \<equiv>
  True"
declare epda_unfixed_scheduler_extendable_def [simp add]

definition epda_sub :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "epda_sub G1 G2 \<equiv>
  epda_states G1 \<subseteq> epda_states G2
  \<and> epda_marking G1 \<subseteq> epda_marking G2
  \<and> epda_delta G1 \<subseteq> epda_delta G2
  \<and> epda_gamma G1 \<subseteq> epda_gamma G2
  \<and> epda_events G1 \<subseteq> epda_events G2
  \<and> epda_initial G1 = epda_initial G2
  \<and> epda_box G1 = epda_box G2"

end
