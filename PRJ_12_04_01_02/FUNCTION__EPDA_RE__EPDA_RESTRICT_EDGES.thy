section {*FUNCTION\_\_EPDA\_RE\_\_EPDA\_RESTRICT\_EDGES*}
theory
  FUNCTION__EPDA_RE__EPDA_RESTRICT_EDGES

imports
  PRJ_12_04_01_02__ENTRY

begin

definition F_ALT_EPDA_RE :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label set
  \<Rightarrow> ('state, 'event, 'stack) epda"
  where
    "F_ALT_EPDA_RE G E \<equiv>
  let
    Q = {epda_initial G}
        \<union> {q \<in> epda_states G.
            \<exists>e \<in> epda_delta G \<inter> E.
              edge_src e = q \<or> edge_trg e = q}
  in
    \<lparr>epda_states = Q,
     epda_events = epda_events G,
     epda_gamma = epda_gamma G,
     epda_delta = epda_delta G \<inter> E,
     epda_initial = epda_initial G,
     epda_box = epda_box G,
     epda_marking = Q \<inter> epda_marking G\<rparr>"

lemma PDA_to_epda: "
  valid_pda G
  \<Longrightarrow> valid_epda G"
  apply(simp add: valid_pda_def)
  done

lemma F_EPDA_R__vs_F_ALT_EPDA_RE: "
  valid_epda G
  \<Longrightarrow> F_EPDA_R G ({epda_initial G} \<union> {q \<in> epda_states G. \<exists>e \<in> epda_delta G \<inter> E. edge_src e = q \<or> edge_trg e = q}) E = F_ALT_EPDA_RE G E"
  apply(simp add: F_EPDA_R_def F_ALT_EPDA_RE_def Let_def)
  apply(rule conjI)
   apply(rule antisym)
    apply(force)
   apply(clarsimp)
   apply(simp add: valid_epda_def)
   apply(force)
  apply(rule conjI)
   apply(rule antisym)
    apply(force)
   apply(clarsimp)
   apply(simp add: valid_epda_def)
   apply(clarsimp)
   apply(erule_tac x="x" in ballE)
    prefer 2
    apply(force)
   apply(simp add: valid_epda_step_label_def)
   apply(force)
  apply(force)
  done

lemma F_EPDA_RE__vs_F_ALT_EPDA_RE: "
  valid_epda G
  \<Longrightarrow> F_EPDA_RE G E = F_ALT_EPDA_RE G E"
  apply(simp add: F_EPDA_RE_def)
  apply(rule_tac t="F_EPDA_R G
     (insert (epda_initial G)
       {q \<in> epda_states G. \<exists>e\<in>epda_delta G \<inter> E. edge_src e = q \<or> edge_trg e = q})
     E" and s="F_EPDA_R G ({epda_initial G} \<union> {q \<in> epda_states G. \<exists>e \<in> epda_delta G \<inter> E. edge_src e = q \<or> edge_trg e = q}) E" in ssubst)
   apply(force)
  apply (rule F_EPDA_R__vs_F_ALT_EPDA_RE)
  apply(force)
  done

lemma F_ALT_EPDA_RE_preserves_epda: "
  valid_epda G
  \<Longrightarrow> valid_epda (F_ALT_EPDA_RE G E)"
  apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(erule_tac
      x = "x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_ALT_EPDA_RE_preserves_PDA: "
  valid_pda G
  \<Longrightarrow> valid_pda (F_ALT_EPDA_RE G E)"
  apply(subgoal_tac "valid_epda (F_ALT_EPDA_RE G E)")
   prefer 2
   apply(rule F_ALT_EPDA_RE_preserves_epda)
   apply(simp add: valid_pda_def)
  apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(simp add: valid_pda_def)
  done

definition F_ALT_EPDA_REE :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_ALT_EPDA_REE e \<equiv>
  e"

definition F_ALT_EPDA_REERev :: "
  ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label"
  where
    "F_ALT_EPDA_REERev e \<equiv>
  e"

lemma F_ALT_EPDA_REERev_preserves_edges: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta (F_ALT_EPDA_RE G E)
  \<Longrightarrow> F_ALT_EPDA_REERev e \<in> epda_delta G"
  apply(simp add: F_ALT_EPDA_REERev_def)
  apply(simp add: F_ALT_EPDA_RE_def Let_def)
  done

definition F_ALT_EPDA_REC :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_ALT_EPDA_REC c \<equiv>
  c"

definition F_ALT_EPDA_RECRev :: "
  ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf"
  where
    "F_ALT_EPDA_RECRev c \<equiv>
  c"

lemma epdaToSymbolE_preserves_valid_epda_step_label: "
  valid_epda G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> valid_epda_step_label G e
  \<Longrightarrow> e \<in> E
  \<Longrightarrow> G' = F_ALT_EPDA_RE G E
  \<Longrightarrow> e' = F_ALT_EPDA_REE e
  \<Longrightarrow> valid_epda_step_label G' e'"
  apply(simp add: F_ALT_EPDA_RE_def Let_def F_ALT_EPDA_REE_def valid_epda_def valid_epda_step_label_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(case_tac "edge_src e = epda_initial G")
    apply(clarsimp)
   apply(clarsimp)
   apply(rule_tac
      x = "e"
      in bexI)
    apply(force)
   apply(force)
  apply(case_tac "edge_trg e = epda_initial G")
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      x = "e"
      in bexI)
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RE_preserves_configuration: "
  valid_pda G
  \<Longrightarrow> q \<in> epda_states G
  \<Longrightarrow> set i \<subseteq> epda_events G
  \<Longrightarrow> set s \<subseteq> epda_gamma G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d ia = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = i, epdaS_conf_stack = s\<rparr>)
  \<Longrightarrow> q \<in> epda_states (F_ALT_EPDA_RE G (epdaS_accessible_edges G)) \<and> set i \<subseteq> epda_events (F_ALT_EPDA_RE G (epdaS_accessible_edges G)) \<and> set s \<subseteq> epda_gamma (F_ALT_EPDA_RE G (epdaS_accessible_edges G))"
  apply(induct ia arbitrary: q i s e)
   apply(rename_tac q i s e)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(rename_tac ia q i s e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac ia q i s e)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc ia"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac ia q i s e)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac ia q i s e)(*strict*)
    apply(force)
   apply(rename_tac ia q i s e)(*strict*)
   apply(force)
  apply(rename_tac ia q i s e)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia q i s e1 e2 c1)(*strict*)
  apply(subgoal_tac "c1 \<in> epdaS_configurations G")
   apply(rename_tac ia q i s e1 e2 c1)(*strict*)
   apply(case_tac c1)
   apply(rename_tac ia q i s e1 e2 c1 epdaS_conf_state epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
   apply(rename_tac q' i' s')
   apply(rename_tac ia q i s e1 e2 c1 q' i' s')(*strict*)
   apply(clarsimp)
   apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
   apply(erule_tac
      x = "q'"
      in meta_allE)
   apply(erule_tac
      x = "i'"
      in meta_allE)
   apply(erule_tac
      x = "s'"
      in meta_allE)
   apply(erule_tac
      x = "e1"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac meta_impE)
    apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
    apply(simp add: epdaS_configurations_def)
   apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
   apply(erule_tac meta_impE)
    apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
    apply(simp add: epdaS_configurations_def)
   apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
   apply(erule_tac meta_impE)
    apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
    apply(simp add: epdaS_configurations_def)
   apply(rename_tac ia q i s e1 e2 q' i' s')(*strict*)
   apply(clarsimp)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ia i e1 e2 w)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac ia i e1 e2 w)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x = "e2"
      in ballE)
     apply(rename_tac ia i e1 e2 w)(*strict*)
     prefer 2
     apply(simp add: epdaS_accessible_edges_def)
    apply(rename_tac ia i e1 e2 w)(*strict*)
    apply(clarsimp)
   apply(rename_tac ia i e1 e2 w)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia i e1 e2 w e)(*strict*)
   apply(erule disjE)
    apply(rename_tac ia i e1 e2 w e)(*strict*)
    apply(erule_tac
      x = "e2"
      in ballE)
     apply(rename_tac ia i e1 e2 w e)(*strict*)
     prefer 2
     apply(simp add: epdaS_accessible_edges_def)
    apply(rename_tac ia i e1 e2 w e)(*strict*)
    apply(clarsimp)
   apply(rename_tac ia i e1 e2 w e)(*strict*)
   apply(erule_tac
      x = "e2"
      in ballE)
    apply(rename_tac ia i e1 e2 w e)(*strict*)
    apply(force)
   apply(rename_tac ia i e1 e2 w e)(*strict*)
   apply(simp add: epdaS_accessible_edges_def)
  apply(rename_tac ia q i s e1 e2 c1)(*strict*)
  apply(rule epdaS.belongs_configurations)
   apply(rename_tac ia q i s e1 e2 c1)(*strict*)
   apply(rule epdaS.derivation_initial_belongs)
    apply(rename_tac ia q i s e1 e2 c1)(*strict*)
    apply(simp add: valid_pda_def)
   apply(rename_tac ia q i s e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac ia q i s e1 e2 c1)(*strict*)
  apply(force)
  done

lemma F_ALT_EPDA_REC_preserves_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> F_ALT_EPDA_REC c \<in> epdaS_configurations (F_ALT_EPDA_RE G E)"
  apply(subgoal_tac "c \<in> epdaS_configurations G")
   prefer 2
   apply (metis (full_types) valid_pda_to_valid_epda contra_subsetD epdaS.get_accessible_configurations_are_configurations)
  apply(simp add: epdaS_configurations_def)
  apply(simp add: F_ALT_EPDA_REC_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac q i s d ia)(*strict*)
  apply(case_tac "d ia")
   apply(rename_tac q i s d ia)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac q i s d ia a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac q i s d ia a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac q i s d ia option)(*strict*)
  apply(rule F_ALT_EPDA_RE_preserves_configuration)
       apply(rename_tac q i s d ia option)(*strict*)
       apply(force)
      apply(rename_tac q i s d ia option)(*strict*)
      apply(force)
     apply(rename_tac q i s d ia option)(*strict*)
     apply(force)
    apply(rename_tac q i s d ia option)(*strict*)
    apply(force)
   apply(rename_tac q i s d ia option)(*strict*)
   apply(force)
  apply(rename_tac q i s d ia option)(*strict*)
  apply(force)
  done

lemma F_ALT_EPDA_REC_preserves_initial_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS_initial_configurations G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> F_ALT_EPDA_REC c \<in> epdaS_initial_configurations (F_ALT_EPDA_RE G E)"
  apply(simp (no_asm) add: epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: epdaS_initial_configurations_def)
   apply(simp add: F_ALT_EPDA_REC_def)
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(rule conjI)
   apply(simp add: epdaS_initial_configurations_def)
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
   apply(simp add: F_ALT_EPDA_REC_def)
  apply(rule F_ALT_EPDA_REC_preserves_configurations)
    apply(force)
   apply (metis PDA_to_epda epdaS.initial_configurations_are_get_accessible_configurations)
  apply(force)
  done

lemma F_ALT_EPDA_REC_preserves_marking_configurations: "
  valid_pda G
  \<Longrightarrow> c \<in> epdaS_marking_configurations G
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> F_ALT_EPDA_REC c \<in> epdaS_marking_configurations (F_ALT_EPDA_RE G E)"
  apply(subgoal_tac "F_ALT_EPDA_REC c \<in> epdaS_configurations (F_ALT_EPDA_RE G E)")
   apply(simp add: epdaS_marking_configurations_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(simp add: F_ALT_EPDA_REC_def)
   apply(simp add: F_ALT_EPDA_RE_def Let_def F_ALT_EPDA_REC_def epdaS_configurations_def)
   apply(clarsimp)
  apply(rule F_ALT_EPDA_REC_preserves_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

definition F_ALT_EPDA_RE_relation_TSstructureLR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<equiv>
  valid_pda G1
  \<and> G2 = F_ALT_EPDA_RE G1 (epdaS_accessible_edges G1)"

definition F_ALT_EPDA_RE_relation_configurationLR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> c2 = F_ALT_EPDA_REC c1"

definition F_ALT_EPDA_RE_relation_initial_configurationLR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 c1 c2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_ALT_EPDA_REC c1"

definition F_ALT_EPDA_RE_relation_effectLR :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_effectLR G1 G2 w1 w2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_ALT_EPDA_RE_relation_TSstructureLR G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply(simp add: valid_dpda_def valid_pda_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  done

definition F_ALT_EPDA_RE_relation_step_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_ALT_EPDA_REC c1) (F_ALT_EPDA_REE e) (F_ALT_EPDA_REC c1')"

definition F_ALT_EPDA_RE_relation_initial_simulation :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_ALT_EPDA_REC c1)"

lemma F_ALT_EPDA_RE_C_preserves_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> F_ALT_EPDA_REC c1 \<in> epdaS_configurations G2"
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_REC_preserves_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RE_C_preserves_initial_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_ALT_EPDA_REC c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_REC_preserves_initial_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RE_C_preserves_marking_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> F_ALT_EPDA_REC c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_REC_preserves_marking_configurations)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RE_initial_simulation_preserves_derivation: "
  F_ALT_EPDA_RE_relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> epdaS.derivation_initial G2 (der1 (F_ALT_EPDA_REC c1))"
  apply(rule epdaS.derivation_initialI)
   apply(rule epdaS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_RE_C_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_ALT_EPDA_RE_relation_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_ALT_EPDA_RE_initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x = "0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def valid_pda_def valid_dpda_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply (metis epdaS.initial_configurations_are_get_accessible_configurations)
  done

lemma F_ALT_EPDA_RE_preserves_step_relation: "
  valid_epda G1
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> E = epdaS_accessible_edges G1
  \<Longrightarrow> c1 \<in> epdaS.get_accessible_configurations G1
  \<Longrightarrow> epdaS_step_relation (F_ALT_EPDA_RE G1 E) (F_ALT_EPDA_REC c1) (F_ALT_EPDA_REE e1) (F_ALT_EPDA_REC c1')"
  apply(subgoal_tac "c1' \<in> epdaS.get_accessible_configurations G1")
   prefer 2
   apply(rule epdaS.der2_preserves_get_accessible_configurations)
     apply(force)
    apply(rule epdaS.der2_is_derivation)
    apply(force)
   apply(force)
  apply(simp (no_asm) add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_ALT_EPDA_RE_def F_ALT_EPDA_REE_def Let_def)
   apply(simp add: epdaS_accessible_edges_def)
   apply(simp add: epdaS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac d da i ia)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i ia)(*strict*)
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac d da i ia)(*strict*)
   apply(rule_tac
      x = "derivation_append (derivation_take d i) (der2 c1 e1 c1') i"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da i ia)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation_initial)
      apply(rename_tac d da i ia)(*strict*)
      apply(force)
     apply(rename_tac d da i ia)(*strict*)
     apply(rule epdaS.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac d da i ia)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac d da i ia)(*strict*)
      apply(rule epdaS.derivation_take_preserves_derivation)
      apply(simp add: epdaS.derivation_initial_def)
     apply(rename_tac d da i ia)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac d da i ia)(*strict*)
    apply(simp add: derivation_take_def)
    apply(case_tac "d i")
     apply(rename_tac d da i ia)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac d da i ia a)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac a)
    apply(rename_tac d da i ia a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da i ia option)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac d da i ia)(*strict*)
   apply(rule_tac
      x = "Suc i"
      in exI)
   apply(simp add: der2_def derivation_append_def)
  apply(rule conjI)
   apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_REE_def epdaS_step_relation_def)
  apply(rule conjI)
   apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_REE_def epdaS_step_relation_def)
  apply(rule conjI)
   apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_REE_def epdaS_step_relation_def)
  apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_REE_def epdaS_step_relation_def)
  done

lemma F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation: "
  F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.derivation G2 d2"
  apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
  apply(subgoal_tac "c1 \<in> epdaS.get_accessible_configurations G1")
   prefer 2
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(clarsimp)
  apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(clarsimp)
  apply(rule epdaS.der2_is_derivation)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_RE_preserves_step_relation)
     apply(simp add: valid_pda_def)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation_belongs: "
  F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS.belongs G2 d2"
  apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
  apply(rule epdaS.der2_belongs_prime)
    prefer 3
    apply(rule F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation)
      apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
     apply(force)
    apply(force)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def F_ALT_EPDA_RE_relation_TSstructureLR_def)
   apply(clarsimp)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(clarsimp)
  apply(rule F_ALT_EPDA_RE_C_preserves_configurations)
   apply(force)
  apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS.get_accessible_configurations_are_configurations subsetD)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_ALT_EPDA_RE_relation_step_simulation_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: der2_def get_configuration_def F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x = "Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: der2_def get_configuration_def F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule epdaS.der2_preserves_get_accessible_configurations)
    apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
    apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def valid_pda_def)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_configurationLR F_ALT_EPDA_RE_relation_TSstructureLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs)
  done

interpretation "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR" : ATS_Simulation_Configuration_Weak
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
  "F_ALT_EPDA_RE_relation_configurationLR"
  (* relation_initial_configuration *)
  "F_ALT_EPDA_RE_relation_initial_configurationLR"
  (* relation_effect *)
  "F_ALT_EPDA_RE_relation_effectLR"
  (* relation_TSstructure *)
  "F_ALT_EPDA_RE_relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_ALT_EPDA_RE_relation_initial_simulation"
  (* relation_step_simulation *)
  "F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marking_condition: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x = "i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x = "f i"
      in exI)
   apply(rule_tac
      x = "e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(rule F_ALT_EPDA_RE_C_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i = Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c = c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x = "Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x = "deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t = "c"
      and s = "F_ALT_EPDA_REC c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_ALT_EPDA_RE_C_preserves_marking_configurations)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def get_configuration_def)
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

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marking_condition: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x = "i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x = "f i"
      in exI)
   apply(rule_tac
      x = "e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t = "c"
      and s = "F_ALT_EPDA_REC ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_ALT_EPDA_RE_C_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i = deri1n")
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

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_configurationLR F_ALT_EPDA_RE_relation_TSstructureLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marking_condition)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectLR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x = "a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_ALT_EPDA_REC_def F_ALT_EPDA_REC_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marked_effect: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectLR G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x = "a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_REC_def get_configuration_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_configurationLR F_ALT_EPDA_RE_relation_effectLR F_ALT_EPDA_RE_relation_TSstructureLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marked_effect)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectLR G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
  apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x = "ca"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x = "i"
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
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M = "G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x = "F_ALT_EPDA_REC c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x = "f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_REC_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i = Suc deri1n")
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
  apply(subgoal_tac "c' = c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x = "F_ALT_EPDA_REC c1'"
      in exI)
  apply(subgoal_tac "F_ALT_EPDA_REC c = ca")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def)
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
  apply(clarsimp)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x = "Suc deri1n"
      in allE)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e option b)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
   apply(rule_tac
      x = "deri2n+n"
      in exI)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
  apply(simp add: F_ALT_EPDA_REC_def get_configuration_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectLR G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
  apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x = "ca"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationLR_def)
   apply(erule_tac
      x = "i"
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
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M = "G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x = "F_ALT_EPDA_REC c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x = "f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_REC_def F_ALT_EPDA_REC_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_ALT_EPDA_RE_relation_configurationLR F_ALT_EPDA_RE_relation_initial_configurationLR F_ALT_EPDA_RE_relation_effectLR F_ALT_EPDA_RE_relation_TSstructureLR F_ALT_EPDA_RE_relation_initial_simulation F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
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
  "F_ALT_EPDA_RE_relation_configurationLR"
  (* relation_initial_configuration *)
  "F_ALT_EPDA_RE_relation_initial_configurationLR"
  (* relation_effect *)
  "F_ALT_EPDA_RE_relation_effectLR"
  (* relation_TSstructure *)
  "F_ALT_EPDA_RE_relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_ALT_EPDA_RE_relation_initial_simulation"
  (* relation_step_simulation *)
  "F_ALT_EPDA_RE_relation_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms )
  done

lemma F_ALT_EPDA_RE_preserves_lang1: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_ALT_EPDA_RE G E)"
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_ALT_EPDA_RE_relation_TSstructureLR_def Suc_n_not_n epdaS.AX_marked_language_finite)
  apply(rule_tac
      t = "epdaS.marked_language (F_ALT_EPDA_RE G E)"
      and s = "epdaS.finite_marked_language (F_ALT_EPDA_RE G E)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  apply(subgoal_tac "left_total_on (F_ALT_EPDA_RE_relation_effectLR SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0 = "G"
      in epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  done

lemma F_ALT_EPDA_RE_preserves_unmarked_language1: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.unmarked_language G \<subseteq> epdaS.unmarked_language (F_ALT_EPDA_RE G E)"
  apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_ALT_EPDA_RE_relation_TSstructureLR_def Suc_n_not_n epdaS.AX_unmarked_language_finite)
  apply(rule_tac
      t = "epdaS.unmarked_language (F_ALT_EPDA_RE G E)"
      and s = "epdaS.finite_unmarked_language (F_ALT_EPDA_RE G E)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda epdaS_inst_AX_unmarked_language_finite)
  apply(subgoal_tac "left_total_on (F_ALT_EPDA_RE_relation_effectLR SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0 = "G"
      in epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_ALT_EPDA_RE_relation_TSstructureLR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_effectLR_def)
  done

definition F_ALT_EPDA_RE_relation_TSstructureRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_TSstructureRL G2 G1 \<equiv>
  valid_pda G1
  \<and> G2 = F_ALT_EPDA_RE G1 (epdaS_accessible_edges G1)"

definition F_ALT_EPDA_RE_relation_configurationRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 c2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<and> c1 \<in> epdaS_configurations G1
  \<and> c2 = F_ALT_EPDA_RECRev c1"

definition F_ALT_EPDA_RE_relation_initial_configurationRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 c1 c2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> c2 = F_ALT_EPDA_RECRev c1"

definition F_ALT_EPDA_RE_relation_effectRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_effectRL G1 G2 w1 w2 \<equiv>
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<and> w1 = w2"

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_ALT_EPDA_RE_relation_TSstructureRL G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> valid_epda G2)"
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply (metis valid_dpda_def valid_pda_def)
  done

definition F_ALT_EPDA_RE_relation_step_simulationRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epda_step_label
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_step_simulationRL G2 G1 c1 e c1' c2 d \<equiv>
  d = der2 (F_ALT_EPDA_RECRev c1) (F_ALT_EPDA_REERev e) (F_ALT_EPDA_RECRev c1')"

definition F_ALT_EPDA_RE_relation_initial_simulationRL :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_ALT_EPDA_RE_relation_initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 (F_ALT_EPDA_RECRev c1)"

lemma F_ALT_EPDA_RE_C_rev_preserves_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_configurations G1
  \<Longrightarrow> F_ALT_EPDA_RECRev c1 \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac q i s)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_def Let_def)
  apply(erule disjE)
   apply(rename_tac q i s)(*strict*)
   apply(simp add: valid_pda_def valid_epda_def)
  apply(rename_tac q i s)(*strict*)
  apply(clarsimp)
  done

lemma F_ALT_EPDA_RE_C_rev_preserves_initial_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_initial_configurations G1
  \<Longrightarrow> F_ALT_EPDA_RECRev c1 \<in> epdaS_initial_configurations G2"
  apply(simp add: F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_relation_TSstructureRL_def F_ALT_EPDA_RE_def epdaS_initial_configurations_def Let_def epdaS_configurations_def valid_pda_def valid_epda_def)
  apply(force)
  done

lemma F_ALT_EPDA_REC_reverse: "
  c1 = F_ALT_EPDA_REC (F_ALT_EPDA_RECRev c1)"
  apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_def epdaS_initial_configurations_def epdaS_configurations_def)
  done

lemma F_ALT_EPDA_REC_reverse2: "
  c1 = F_ALT_EPDA_RECRev (F_ALT_EPDA_REC c1)"
  apply(simp add: F_ALT_EPDA_REC_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_def epdaS_initial_configurations_def epdaS_configurations_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_ALT_EPDA_RE_relation_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_initial_simulationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_ALT_EPDA_RE_C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationRL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x = "0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
  apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2 c1)(*strict*)
  apply(simp add: epdaS_initial_configurations_def)
  done

lemma F_ALT_EPDA_RERev_preserves_step_relation: "
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<Longrightarrow> epdaS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> epdaS_step_relation G2 (F_ALT_EPDA_RECRev c1) (F_ALT_EPDA_REERev e1) (F_ALT_EPDA_RECRev c1')"
  apply(simp add: epdaS_step_relation_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_relation_TSstructureRL_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_REERev_def F_ALT_EPDA_RE_def Let_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_step_simulationRL_def)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(rule F_ALT_EPDA_RERev_preserves_step_relation)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule epdaS.derivation_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
      apply(simp add: valid_pda_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_ALT_EPDA_RE_C_rev_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_ALT_EPDA_RE_relation_configurationRL_def F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x = "Suc 0"
      in exI)
  apply(simp add: maximum_of_domain_def der2_def)
  apply(simp add: get_configuration_def F_ALT_EPDA_RE_relation_configurationRL_def F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(rule epdaS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G2 c1 e1 c1')(*strict*)
    apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
   apply(rename_tac G2 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1')(*strict*)
  apply(force)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_configurationRL F_ALT_EPDA_RE_relation_TSstructureRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_step_relation_step_simulation epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs)
  done

interpretation "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL" : ATS_Simulation_Configuration_Weak
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
  "F_ALT_EPDA_RE_relation_configurationRL"
  (* relation_initial_configuration *)
  "F_ALT_EPDA_RE_relation_initial_configurationRL"
  (* relation_effect *)
  "F_ALT_EPDA_RE_relation_effectRL"
  (* relation_TSstructure *)
  "F_ALT_EPDA_RE_relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_ALT_EPDA_RE_relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_ALT_EPDA_RE_C_rev_preserves_marking_configurations: "
  F_ALT_EPDA_RE_relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> epdaS_marking_configurations G1
  \<Longrightarrow> F_ALT_EPDA_RECRev c1 \<in> epdaS_marking_configurations G2"
  apply(simp add: epdaS_marking_configurations_def F_ALT_EPDA_RECRev_def F_ALT_EPDA_RE_relation_TSstructureRL_def F_ALT_EPDA_RE_def F_ALT_EPDA_RECRev_def Let_def epdaS_configurations_def valid_pda_def valid_epda_def)
  apply(force)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x = "i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x = "f i"
      in exI)
   apply(rule_tac
      x = "e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t = "c"
      and s = "F_ALT_EPDA_RECRev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_ALT_EPDA_RE_C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i = Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c = c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
    apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x = "Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x = "deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t = "c"
      and s = "F_ALT_EPDA_RECRev c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def derivation_append_def get_configuration_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_ALT_EPDA_RE_C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def derivation_append_def get_configuration_def F_ALT_EPDA_RE_relation_initial_configurationRL_def der2_def)
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

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x = "i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x = "f i"
      in exI)
   apply(rule_tac
      x = "e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t = "c"
      and s = "F_ALT_EPDA_RECRev ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_ALT_EPDA_RE_C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i = deri1n")
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

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_configurationRL F_ALT_EPDA_RE_relation_TSstructureRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectRL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x = "a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_RE_relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_ALT_EPDA_RECRev_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectRL G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x = "a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_RE_relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_ALT_EPDA_RECRev_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
  apply (metis epdaS.derivation_initial_is_derivation)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_configurationRL F_ALT_EPDA_RE_relation_effectRL F_ALT_EPDA_RE_relation_TSstructureRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_ALT_EPDA_RE_relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectRL G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
  apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x = "ca"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
   apply(erule_tac
      x = "i"
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
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M = "G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: F_ALT_EPDA_RECRev_def)
   apply(rule_tac
      x = "c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x = "f i"
      in exI)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(subgoal_tac "i = Suc deri1n")
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
  apply(subgoal_tac "c' = c1'")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c c' e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e ca)(*strict*)
  apply(rule_tac
      x = "F_ALT_EPDA_RECRev c1'"
      in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationRL_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
   apply(rule_tac
      x = "deri2n+n"
      in exI)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x = "Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
   apply(case_tac n)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f a ca ea e nat)(*strict*)
   apply(simp add: F_ALT_EPDA_RECRev_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a c e)(*strict*)
  apply(simp add: F_ALT_EPDA_RECRev_def F_ALT_EPDA_REC_def F_ALT_EPDA_REC_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_ALT_EPDA_RE_relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_ALT_EPDA_RE_relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_ALT_EPDA_RE_relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_ALT_EPDA_RE_relation_effectRL G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
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
  apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
   prefer 2
   apply(rule_tac
      M = "G2"
      in epdaS.some_position_has_details_at_0)
   apply (metis epdaS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(rule_tac
      x = "ca"
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
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RE_relation_configurationRL_def)
   apply(erule_tac
      x = "i"
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
   apply(simp add: F_ALT_EPDA_RE_relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
    prefer 2
    apply(rule_tac
      M = "G1"
      in epdaS.some_position_has_details_at_0)
    apply (metis epdaS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(rule_tac
      x = "c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
    apply(rule_tac
      x = "f i"
      in exI)
    apply(clarsimp)
    apply(simp add: derivation_append_def F_ALT_EPDA_RECRev_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a ca c' i ea e c)(*strict*)
   apply(simp add: derivation_append_def F_ALT_EPDA_RECRev_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a c c' i e ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_ALT_EPDA_RE_relation_configurationRL F_ALT_EPDA_RE_relation_initial_configurationRL F_ALT_EPDA_RE_relation_effectRL F_ALT_EPDA_RE_relation_TSstructureRL F_ALT_EPDA_RE_relation_initial_simulationRL F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
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
  "F_ALT_EPDA_RE_relation_configurationRL"
  (* relation_initial_configuration *)
  "F_ALT_EPDA_RE_relation_initial_configurationRL"
  (* relation_effect *)
  "F_ALT_EPDA_RE_relation_effectRL"
  (* relation_TSstructure *)
  "F_ALT_EPDA_RE_relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_ALT_EPDA_RE_relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_ALT_EPDA_RE_relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations)
  apply(simp add:  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_ALT_EPDA_RE_preserves_lang2: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.marked_language G \<supseteq> epdaS.marked_language (F_ALT_EPDA_RE G E)"
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaS.finite_marked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_ALT_EPDA_RE_relation_TSstructureLR_def epdaS_inst_lang_finite)
  apply(rule_tac
      t = "epdaS.marked_language (F_ALT_EPDA_RE G E)"
      and s = "epdaS.finite_marked_language (F_ALT_EPDA_RE G E)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_marked_language_finite)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  apply(subgoal_tac "left_total_on (F_ALT_EPDA_RE_relation_effectRL SSG1 SSG2) (epdaS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0 = "G"
      in epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  done

lemma F_ALT_EPDA_RE_preserves_unmarked_language2: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.unmarked_language G \<supseteq> epdaS.unmarked_language (F_ALT_EPDA_RE G E)"
  apply(rule_tac
      t = "epdaS.unmarked_language G"
      and s = "epdaS.finite_unmarked_language G"
      in ssubst)
   apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_ALT_EPDA_RE_relation_TSstructureLR_def epdaS_inst_AX_unmarked_language_finite n_not_Suc_n)
  apply(rule_tac
      t = "epdaS.unmarked_language (F_ALT_EPDA_RE G E)"
      and s = "epdaS.finite_unmarked_language (F_ALT_EPDA_RE G E)"
      in ssubst)
   apply(rule sym)
   apply(rule epdaS.AX_unmarked_language_finite)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  apply(subgoal_tac "left_total_on (F_ALT_EPDA_RE_relation_effectRL SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0 = "G"
      in epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_ALT_EPDA_RE_relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_relation_effectRL_def)
  done

lemma F_ALT_EPDA_RE_preserves_lang: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_ALT_EPDA_RE G E)"
  apply(rule order_antisym)
   apply (metis F_ALT_EPDA_RE_preserves_lang1)
  apply (metis F_ALT_EPDA_RE_preserves_lang2)
  done

lemma F_ALT_EPDA_RE_preserves_unmarked_language: "
  valid_pda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_ALT_EPDA_RE G E)"
  apply(rule order_antisym)
   apply (metis F_ALT_EPDA_RE_preserves_unmarked_language1)
  apply (metis F_ALT_EPDA_RE_preserves_unmarked_language2)
  done

lemma F_ALT_EPDA_RE_preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> E \<subseteq> epda_delta G
  \<Longrightarrow> valid_dpda (F_ALT_EPDA_RE G E)"
  apply(simp add: valid_dpda_def)
  apply(clarsimp)
  apply(rule conjI)
   apply (metis F_ALT_EPDA_RE_preserves_PDA)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule_tac
      x="c2"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(erule_tac
      x="e2"
      in allE)
   apply(erule impE)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    apply(simp add: F_ALT_EPDA_RE_def epdaS_step_relation_def Let_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "c \<in> epdaS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(thin_tac "c \<notin> A" for A)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   prefer 2
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(rule epdaS.derivation_initialI)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(simp (no_asm) add: epdaS.derivation_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i ia)(*strict*)
   apply(case_tac ia)
    apply(rename_tac c c1 c2 e1 e2 d i ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
    apply(simp add: epdaS.derivation_initial_def epdaS.derivation_def)
    apply(case_tac "d 0")
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac c c1 c2 e1 e2 d i a option conf)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d i ia nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat)(*strict*)
   apply(simp add: epdaS.derivation_initial_def epdaS.derivation_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac c c1 c2 e1 e2 d i nat)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d i nat a)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac c c1 c2 e1 e2 d i nat a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac c c1 c2 e1 e2 d i nat a option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat a aa)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c c1 c2 e1 e2 d i nat a aa option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat aa option conf)(*strict*)
   apply(case_tac aa)
   apply(rename_tac c c1 c2 e1 e2 d i nat aa option conf optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat option conf optiona confa)(*strict*)
   apply(case_tac option)
    apply(rename_tac c c1 c2 e1 e2 d i nat option conf optiona confa)(*strict*)
    apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat option conf optiona confa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 d i nat conf optiona confa a)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def epdaS_step_relation_def Let_def)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(simp add: epdaS.derivation_initial_def epdaS.derivation_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i ca)(*strict*)
  apply(simp add: epdaS_configurations_def epdaS_initial_configurations_def F_ALT_EPDA_RE_def epdaS_step_relation_def Let_def valid_pda_def valid_epda_def)
  apply(clarsimp)
  done

lemma F_ALT_EPDA_RE_preserves_derivation: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> epdaS.derivation_initial (F_ALT_EPDA_RE G E) d"
  apply(simp add: epdaS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def Let_def epdaS_initial_configurations_def F_ALT_EPDA_RE_relation_TSstructureLR_def valid_dpda_def valid_pda_def valid_epda_def epdaS_configurations_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_def Let_def epdaS_initial_configurations_def F_ALT_EPDA_RE_relation_TSstructureLR_def valid_dpda_def valid_pda_def valid_epda_def epdaS_configurations_def epdaS_step_relation_def epdaS_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(simp add: epdaS.derivation_initial_def)
  apply(force)
  done

lemma F_ALT_EPDA_RE_establishes_coblockbreeness: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_accessible_edges G
  \<Longrightarrow> epdaS.accessible (F_ALT_EPDA_RE G E)"
  apply(simp add: epdaS.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaS.get_accessible_destinations_def epda_destinations_def)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: epdaS_get_destinations_def)
   apply(case_tac "xa = epda_initial G")
    apply(rename_tac xa)(*strict*)
    apply(rule_tac
      x = "der1 \<lparr>epdaS_conf_state = epda_initial G, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac xa)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(rule conjI)
      apply(rename_tac xa)(*strict*)
      apply(rule epdaS.der1_is_derivation)
     apply(rename_tac xa)(*strict*)
     apply(simp add: der1_def)
     apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
     apply(simp add: der1_def)
     apply(clarsimp)
     apply(simp add: epdaS_accessible_edges_def)
     apply(simp add: F_ALT_EPDA_RE_def Let_def)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x = "0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac "xa \<in> epda_states G \<and> (\<exists>e\<in> epda_delta G \<inter> epdaS_accessible_edges G. edge_src e = xa \<or> edge_trg e = xa)")
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(simp add: F_ALT_EPDA_RE_def Let_def)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e)(*strict*)
   apply(subgoal_tac "\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>n c. d n = Some (pair (Some e) c))")
    apply(rename_tac xa e)(*strict*)
    prefer 2
    apply(simp add: epdaS_accessible_edges_def)
   apply(rename_tac xa e)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e d n c)(*strict*)
   apply(rule_tac
      x = "d"
      in exI)
   apply(rule conjI)
    apply(rename_tac xa e d n c)(*strict*)
    apply(rule F_ALT_EPDA_RE_preserves_derivation)
      apply(rename_tac xa e d n c)(*strict*)
      apply(force)
     apply(rename_tac xa e d n c)(*strict*)
     apply(force)
    apply(rename_tac xa e d n c)(*strict*)
    apply(force)
   apply(rename_tac xa e d n c)(*strict*)
   apply(case_tac n)
    apply(rename_tac xa e d n c)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e d c)(*strict*)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply (metis epdaS.derivation_initial_is_derivation epdaS.initialNotEdgeSome)
   apply(rename_tac xa e d n c nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
    apply(rename_tac xa e d n c nat)(*strict*)
    prefer 2
    apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
      apply(rename_tac xa e d n c nat)(*strict*)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac xa e d n c nat)(*strict*)
     apply(force)
    apply(rename_tac xa e d n c nat)(*strict*)
    apply(force)
   apply(rename_tac xa e d n c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e d c nat e1 c1)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(erule disjE)
    apply(rename_tac xa e d c nat e1 c1)(*strict*)
    apply(rule_tac
      x = "nat"
      in exI)
    apply(rule_tac
      x = "e1"
      in exI)
    apply(rule_tac
      x = "c1"
      in exI)
    apply(clarsimp)
   apply(rename_tac xa e d c nat e1 c1)(*strict*)
   apply(rule_tac
      x = "Suc nat"
      in exI)
   apply(rule_tac
      x = "Some e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(simp add: epdaS_get_destinations_def)
  apply(subgoal_tac "xa \<in> epdaS_accessible_edges G")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(rename_tac xa)(*strict*)
  apply(subgoal_tac "(\<exists>d. epdaS.derivation_initial G d \<and> (\<exists>n c. d n = Some (pair (Some xa) c)))")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(simp add: epdaS_accessible_edges_def)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d n c)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa d n c)(*strict*)
   apply(rule F_ALT_EPDA_RE_preserves_derivation)
     apply(rename_tac xa d n c)(*strict*)
     apply(force)
    apply(rename_tac xa d n c)(*strict*)
    apply(force)
   apply(rename_tac xa d n c)(*strict*)
   apply(force)
  apply(rename_tac xa d n c)(*strict*)
  apply(rule_tac
      x = "n"
      in exI)
  apply(rule_tac
      x = "Some xa"
      in exI)
  apply(clarsimp)
  done

definition F_EPDA_RE__SpecInput :: "
  (('state, 'event, 'stack) epda \<times> ('state, 'event, 'stack) epda_step_label set)
  \<Rightarrow> bool"
  where
    "F_EPDA_RE__SpecInput X \<equiv>
  case X of (G, E)
    \<Rightarrow> valid_dpda G
    \<and> E = epdaS_accessible_edges G"

definition F_EPDA_RE__SpecOutput :: "
  (('state, 'event, 'stack) epda \<times> ('state, 'event, 'stack) epda_step_label set)
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_RE__SpecOutput X Go \<equiv>
  case X of (Gi, E) \<Rightarrow>
    valid_dpda Go
    \<and> epdaS.accessible Go
    \<and> epdaS.marked_language Gi = epdaS.marked_language Go
    \<and> epdaS.unmarked_language Gi = epdaS.unmarked_language Go"

lemma F_ALT_EPDA_RE__SOUND: "
  F_EPDA_RE__SpecInput (G, E)
  \<Longrightarrow> F_EPDA_RE__SpecOutput (G, E) (F_ALT_EPDA_RE G E)"
  apply(simp add: F_EPDA_RE__SpecInput_def F_EPDA_RE__SpecOutput_def)
  apply(rule context_conjI)
   apply(rule F_ALT_EPDA_RE_preserves_DPDA)
    apply(force)
   apply(simp add: epdaS_accessible_edges_def)
   apply(force)
  apply(rule conjI)
   apply(rule F_ALT_EPDA_RE_establishes_coblockbreeness)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule F_ALT_EPDA_RE_preserves_lang)
    apply(simp add: valid_dpda_def)
   apply(force)
  apply(rule F_ALT_EPDA_RE_preserves_unmarked_language)
   apply(simp add: valid_dpda_def)
  apply(force)
  done

theorem F_EPDA_RE__SOUND: "
  F_EPDA_RE__SpecInput (G, E)
  \<Longrightarrow> F_EPDA_RE__SpecOutput (G, E) (F_EPDA_RE G E)"
  apply(rule_tac t="F_EPDA_RE G E" and s="F_ALT_EPDA_RE G E" in ssubst)
   apply(rule F_EPDA_RE__vs_F_ALT_EPDA_RE)
   apply(simp add: F_EPDA_RE__SpecInput_def F_EPDA_RE__SpecOutput_def)
   apply(simp add:  valid_dpda_def valid_pda_def)
  apply(rule F_ALT_EPDA_RE__SOUND)
  apply(force)
  done

definition F_EPDA_RE__SpecInput2 :: "
  (('state, 'event, 'stack) epda \<times> ('state, 'event, 'stack) epda_step_label set)
  \<Rightarrow> bool"
  where
    "F_EPDA_RE__SpecInput2 X \<equiv>
  case X of (G, E)
    \<Rightarrow> valid_dpda G
    \<and> E = epdaS_required_edges G"

definition F_EPDA_RE__SpecOutput2 :: "
  (('state, 'event, 'stack) epda \<times> ('state, 'event, 'stack) epda_step_label set)
  \<Rightarrow> ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_RE__SpecOutput2 X Go \<equiv>
  case X of (Gi, E) \<Rightarrow>
    valid_dpda Go
    \<and> epdaS.accessible Go
    \<and> epdaS.marked_language Gi = epdaS.marked_language Go
    \<and> epdaS.unmarked_language Go \<subseteq> epdaS.unmarked_language Gi
    \<and> (epdaH.Nonblockingness_branching Gi
        \<longrightarrow>
          (epdaS.unmarked_language Gi \<subseteq> epdaS.unmarked_language Go
          \<and> epdaH.Nonblockingness_branching Go))"

lemma F_ALT_EPDA_RE_preserves_derivation__epdaS_required_edges: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaS.derivation_initial G d
  \<Longrightarrow> d k = Some (pair ea ca)
  \<Longrightarrow> ca \<in> epdaS_marking_configurations G
  \<Longrightarrow> epdaS.derivation_initial (F_ALT_EPDA_RE G E) (derivation_take d k)"
  apply(simp add: epdaS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def Let_def epdaS_initial_configurations_def F_ALT_EPDA_RE_relation_TSstructureLR_def valid_dpda_def valid_pda_def valid_epda_def epdaS_configurations_def derivation_take_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp (no_asm) add: epdaS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nat a)(*strict*)
  apply(simp add: derivation_take_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_def Let_def epdaS_initial_configurations_def F_ALT_EPDA_RE_relation_TSstructureLR_def valid_dpda_def valid_pda_def valid_epda_def epdaS_configurations_def epdaS_step_relation_def epdaS_accessible_edges_def)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(simp add: epdaS_step_relation_def F_ALT_EPDA_RE_def Let_def epdaS_required_edges_def)
  apply(rename_tac nat e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      x = "d"
      in exI)
  apply(simp add: epdaS.derivation_initial_def)
  apply(force)
  done

lemma F_ALT_EPDA_RE_establishes_coblockbreeness__epdaS_required_edges: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaS.accessible (F_ALT_EPDA_RE G E)"
  apply(simp add: epdaS.accessible_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: epdaS.get_accessible_destinations_def epda_destinations_def)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(simp add: epdaS_get_destinations_def)
   apply(case_tac "xa = epda_initial G")
    apply(rename_tac xa)(*strict*)
    apply(rule_tac
      x = "der1 \<lparr>epdaS_conf_state = epda_initial G, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac xa)(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     apply(rule conjI)
      apply(rename_tac xa)(*strict*)
      apply(rule epdaS.der1_is_derivation)
     apply(rename_tac xa)(*strict*)
     apply(simp add: der1_def)
     apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
     apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
     apply(simp add: der1_def)
     apply(clarsimp)
     apply(simp add: epdaS_required_edges_def)
     apply(simp add: F_ALT_EPDA_RE_def Let_def)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x = "0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac "xa \<in> epda_states G \<and> (\<exists>e\<in> epda_delta G \<inter> epdaS_required_edges G. edge_src e = xa \<or> edge_trg e = xa)")
    apply(rename_tac xa)(*strict*)
    prefer 2
    apply(simp add: F_ALT_EPDA_RE_def Let_def)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e)(*strict*)
   apply(subgoal_tac "\<exists>d. epdaS.derivation_initial G d \<and>
                (\<exists>n. (\<exists>c. d n = Some (pair (Some e) c)) \<and>
                     (\<exists>k\<ge>n. \<exists>e c. d k = Some (pair e c) \<and>
                                   c \<in> epdaS_marking_configurations G))")
    apply(rename_tac xa e)(*strict*)
    prefer 2
    apply(simp add: epdaS_required_edges_def)
   apply(rename_tac xa e)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "derivation_take d k"
      in exI)
   apply(rule conjI)
    apply(rule F_ALT_EPDA_RE_preserves_derivation__epdaS_required_edges)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(case_tac n)
    apply(clarsimp)
    apply(simp add: valid_dpda_def valid_pda_def)
    apply(clarsimp)
    apply (metis epdaS.derivation_initial_is_derivation epdaS.initialNotEdgeSome)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> epdaS_step_relation G c1 e2 c2")
    prefer 2
    apply(rule_tac
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
      apply(rule epdaS.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: epdaS_step_relation_def)
   apply(erule disjE)
    apply(rule_tac
      x = "nat"
      in exI)
    apply(rule_tac
      x = "e1"
      in exI)
    apply(rule_tac
      x = "c1"
      in exI)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rule_tac
      x = "Suc nat"
      in exI)
   apply(rule_tac
      x = "Some e"
      in exI)
   apply(rule_tac
      x = "c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(simp add: epdaS_get_destinations_def)
  apply(subgoal_tac "xa \<in> epdaS_required_edges G")
   prefer 2
   apply(simp add: F_ALT_EPDA_RE_def Let_def)
  apply(rename_tac xa)(*strict*)
  apply(subgoal_tac "xa \<in> epda_delta G \<and>
          (\<exists>d. epdaS.derivation_initial G d \<and>
               (\<exists>n. (\<exists>c. d n = Some (pair (Some xa) c)) \<and>
                    (\<exists>k\<ge>n. \<exists>e c. d k = Some (pair e c) \<and>
                                  c \<in> epdaS_marking_configurations G)))")
   prefer 2
   apply(simp add: epdaS_required_edges_def)
  apply(clarsimp)
  apply(rule_tac
      x = "derivation_take d k"
      in exI)
  apply(rule conjI)
   apply(rule F_ALT_EPDA_RE_preserves_derivation__epdaS_required_edges)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      x = "n"
      in exI)
  apply(rule_tac
      x = "Some xa"
      in exI)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  done

lemma F_ALT_EPDA_RE_preserves_lang2__epdaS_required_edges: "
  valid_epda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaH.marked_language (F_ALT_EPDA_RE G E) \<subseteq> epdaH.marked_language G"
  apply(rule epda_sub_preserves_epdaH_marked_language)
    apply(force)
   apply(rule F_ALT_EPDA_RE_preserves_epda)
   apply(force)
  apply(simp add: epda_sub_def F_ALT_EPDA_RE_def Let_def valid_epda_def)
  apply(force)
  done

lemma F_ALT_EPDA_RE_preserves_unmarked_lang2__epdaS_required_edges: "
  valid_epda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaH.unmarked_language (F_ALT_EPDA_RE G E) \<subseteq> epdaH.unmarked_language G"
  apply(rule epda_sub_preserves_epdaH_unmarked_language)
    apply(force)
   apply(rule F_ALT_EPDA_RE_preserves_epda)
   apply(force)
  apply(simp add: epda_sub_def F_ALT_EPDA_RE_def Let_def valid_epda_def)
  apply(force)
  done

lemma F_ALT_EPDA_RE_preserves_lang1__epdaS_required_edges: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaS.marked_language G \<subseteq> epdaS.marked_language (F_ALT_EPDA_RE G E)"
  apply(rule_tac
      t = "epdaS.marked_language G"
      and s = "epdaS.finite_marked_language G"
      in ssubst)
   apply(simp add: valid_dpda_def)
   apply (metis epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_ALT_EPDA_RE_relation_TSstructureLR_def epdaS.AX_marked_language_finite)
  apply(rule_tac
      t = "epdaS.marked_language (F_ALT_EPDA_RE G E)"
      and s = "epdaS.finite_marked_language (F_ALT_EPDA_RE G E)"
      in ssubst)
   apply(rule sym)
   apply(simp add: valid_dpda_def)
   apply(rule epdaS.AX_marked_language_finite)
   apply (metis F_ALT_EPDA_RE_preserves_epda PDA_to_epda)
  apply(clarsimp)
  apply(simp add: epdaS.finite_marked_language_def)
  apply(clarsimp)
  apply(simp add: epdaS_marking_condition_def)
  apply(clarsimp)
  apply(thin_tac "maximum_of_domain d xa")
  apply(rule_tac x="derivation_take d i" in exI)
  apply(rule conjI)
   apply(rule F_ALT_EPDA_RE_preserves_derivation__epdaS_required_edges)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: derivation_take_def epdaS_marked_effect_def)
  apply(rule conjI)
   apply(rule_tac x="i" in exI)
   apply(simp add: derivation_take_def epdaS_marked_effect_def)
   apply(clarsimp)
   apply(simp add: derivation_take_def epdaS_marked_effect_def epdaS_marking_configurations_def F_ALT_EPDA_RE_def Let_def epdaS_configurations_def)
   apply(erule conjE)+
   apply(erule exE)+
   apply(erule conjE)+
   apply(rule conjI)
    apply(case_tac i)
     apply(rule disjI1)
     apply(clarsimp)
     apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
    apply(rule disjI2)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac
      n="nat" and
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rule_tac x="e2" in bexI)
     apply(simp add: epdaS_step_relation_def)
    apply(simp add: epdaS_step_relation_def)
    apply(simp add: epdaS_required_edges_def)
    apply(rule_tac x="d" in exI)
    apply(clarsimp)
    apply(rule_tac x="Suc nat" in exI)
    apply(clarsimp)
    apply(rule_tac x="Suc nat" in exI)
    apply(clarsimp)
    apply(simp add: epdaS_marking_configurations_def epdaS_configurations_def)
   apply(rule_tac x="epdaS_conf_state c" in exI)
   apply(rule_tac x="epdaS_conf_scheduler c" in exI)
   apply(rule_tac x="epdaS_conf_stack c" in exI)
   apply(rule conjI)
    apply(clarsimp)
   apply(rule conjI)
    apply(case_tac i)
     apply(rule disjI1)
     apply(clarsimp)
     apply(simp add: epdaS.derivation_initial_def epdaS_initial_configurations_def)
    apply(rule disjI2)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac
      n="nat" and
      m = "Suc nat"
      in epdaS.step_detail_before_some_position)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rule_tac x="e2" in bexI)
     apply(simp add: epdaS_step_relation_def)
    apply(simp add: epdaS_step_relation_def)
    apply(simp add: epdaS_required_edges_def)
    apply(rule_tac x="d" in exI)
    apply(clarsimp)
    apply(rule_tac x="Suc nat" in exI)
    apply(clarsimp)
    apply(rule_tac x="Suc nat" in exI)
    apply(clarsimp)
    apply(simp add: epdaS_marking_configurations_def epdaS_configurations_def)
   apply(force)
  apply(rule_tac x="i" in exI)
  apply (metis maximum_of_domain_derivation_take not_None_eq)
  done

lemma F_ALT_EPDA_RE_preserves_lang__epdaS_required_edges: "
  valid_dpda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_ALT_EPDA_RE G E)"
  apply(rule order_antisym)
   apply (metis F_ALT_EPDA_RE_preserves_lang1__epdaS_required_edges)
  apply(simp add: valid_dpda_def valid_pda_def)
  apply(erule conjE)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply (rule F_ALT_EPDA_RE_preserves_lang2__epdaS_required_edges)
    apply(force)
   apply(force)
  apply (metis F_ALT_EPDA_RE_preserves_epda epdaS_to_epdaH_mlang)
  done

lemma F_ALT_EPDA_RE_preserves_epdaH_initial_marking_derivations_at_end: "
 valid_epda G \<Longrightarrow>
    epdaH_initial_marking_derivations_at_end G
    \<subseteq> epdaH_initial_marking_derivations_at_end (F_ALT_EPDA_RE G (epdaH_required_edges G))"
  apply(simp add:  epdaH_initial_marking_derivations_at_end_def)
  apply(clarsimp)
  apply(rename_tac d n e c)
  apply(rule context_conjI)
   apply(simp (no_asm) add: epdaH.derivation_initial_def)
   apply(rule context_conjI)
    apply(simp (no_asm) add: epdaH.derivation_def)
    apply(clarsimp)
    apply(case_tac i)
     apply(clarsimp)
     apply(case_tac "d 0")
      apply(simp add: epdaH.derivation_initial_def)
     apply(clarsimp)
     apply(case_tac a)
     apply(clarsimp)
     apply(simp add: epdaH.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac n)
    apply(case_tac "d (Suc n)")
     apply(clarsimp)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac
      n="n" and m="Suc n" in epdaH.step_detail_before_some_position)
       apply(rule epdaH.derivation_initial_is_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: epdaH_step_relation_def F_ALT_EPDA_RE_def Let_def epdaH_required_edges_def)
    apply(clarsimp)
    apply(rule_tac x="d" in exI)
    apply(clarsimp)
    apply(rule_tac x="Suc n" in exI)
    apply(clarsimp)
    apply(rule_tac x="na" in exI)
    apply(clarsimp)
    apply(rule epdaH.allPreMaxDomSome_prime)
      apply(simp add: epdaH.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(case_tac "d 0")
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def)
   apply(clarsimp)
   apply(simp add: epdaH_initial_configurations_def F_ALT_EPDA_RE_def Let_def epdaH_configurations_def)
   apply(clarsimp)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  apply(simp add: epdaH_marking_configurations_def epdaH_initial_configurations_def F_ALT_EPDA_RE_def Let_def epdaH_configurations_def)
  apply(erule conjE)+
  apply(erule exE)+
  apply(erule conjE)+
  apply(rule conjI)
   apply(case_tac n)
    apply(rule disjI1)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH.derivation_def epdaH_initial_configurations_def)
   apply(rule disjI2)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="nat" and
      m = "Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="e2" in bexI)
    apply(simp add: epdaH_step_relation_def)
   apply(simp add: epdaH_step_relation_def)
   apply(simp add: epdaH_required_edges_def)
   apply(rule_tac x="d" in exI)
   apply(clarsimp)
   apply(rule_tac x="Suc nat" in exI)
   apply(clarsimp)
   apply(rule_tac x="Suc nat" in exI)
   apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def)
  apply(rule_tac x="epdaH_conf_state c" in exI)
  apply(rule_tac x="epdaH_conf_stack c" in exI)
  apply(rule_tac x="epdaH_conf_history c" in exI)
  apply(rule conjI)
   apply(clarsimp)
  apply(rule conjI)
   apply(case_tac n)
    apply(rule disjI1)
    apply(clarsimp)
    apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(rule disjI2)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="nat" and
      m = "Suc nat"
      in epdaH.step_detail_before_some_position)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="e2" in bexI)
    apply(simp add: epdaH_step_relation_def)
   apply(simp add: epdaH_step_relation_def)
   apply(simp add: epdaH_required_edges_def)
   apply(rule_tac x="d" in exI)
   apply(clarsimp)
   apply(rule_tac x="Suc nat" in exI)
   apply(clarsimp)
   apply(rule_tac x="Suc nat" in exI)
   apply(clarsimp)
   apply(simp add: epdaH_marking_configurations_def epdaH_configurations_def)
  apply(force)
  done

lemma epda_sub__equal_unmarked_language__Nonblockingness_branching_and_preservation_of_initial_marking_derivation: "
  valid_epda G1
  \<Longrightarrow> valid_epda G2
  \<Longrightarrow> epda_sub G1 G2
  \<Longrightarrow> epdaH_initial_marking_derivations_at_end G2 \<subseteq> epdaH_initial_marking_derivations_at_end G1
  \<Longrightarrow> epdaH.Nonblockingness_branching G2
  \<Longrightarrow> epdaH.unmarked_language G2 \<subseteq> epdaH.unmarked_language G1"
  apply(simp add: epdaH.unmarked_language_def epdaH.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(simp add: epdaH_unmarked_effect_def)
  apply(clarsimp)
  apply(erule_tac x="derivation_take d i" in allE)
  apply(erule impE)
   apply(rule epdaH.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(erule_tac x="i" in allE)
  apply(erule impE)
   apply(simp add: maximum_of_domain_def derivation_take_def)
  apply(clarsimp)
  apply(simp add: epdaH_marking_condition_def)
  apply(clarsimp)
  apply(rule_tac x="derivation_take (derivation_append (derivation_take d i) dc i) ia " in exI)
  apply(rule context_conjI)
   apply(subgoal_tac "(derivation_take (derivation_append (derivation_take d i) dc i) ia) \<in> epdaH_initial_marking_derivations_at_end G1")
    apply(simp add: epdaH_initial_marking_derivations_at_end_def)
   apply(subgoal_tac "(derivation_take (derivation_append (derivation_take d i) dc i) ia) \<in> epdaH_initial_marking_derivations_at_end G2")
    apply(force)
   apply(thin_tac "epdaH_initial_marking_derivations_at_end G2 \<subseteq> epdaH_initial_marking_derivations_at_end G1")
   apply(simp add: epdaH_initial_marking_derivations_at_end_def)
   apply(rule conjI)
    apply(rule epdaH.derivation_take_preserves_derivation_initial)
    apply(rule epdaH.derivation_append_preserves_derivation_initial)
      apply(force)
     apply(rule epdaH.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rule epdaH.derivation_append_preserves_derivation)
      apply(rule epdaH.derivation_take_preserves_derivation)
      apply(force)
     apply(force)
    apply(simp add: derivation_take_def derivation_append_fit_def)
    apply(case_tac "dc 0")
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac a)
    apply(clarsimp)
    apply(case_tac x1)
     apply(clarsimp)
    apply(clarsimp)
   apply(rule_tac x="ia" in exI)
   apply(rule conjI)
    apply(simp add: derivation_take_def maximum_of_domain_def)
   apply(simp add: derivation_take_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: epdaH.derivation_initial_def)
  apply(case_tac "i\<le>ia")
   apply(rule_tac x="i" in exI)
   apply(simp add: derivation_take_def derivation_append_def)
  apply(case_tac "ia<i")
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(erule_tac x="i" in allE)
  apply(clarsimp)
  apply(rule_tac x="ia" in exI)
  apply(simp add: derivation_take_def epdaH_string_state_def derivation_append_def)
  done

lemma F_ALT_EPDA_RE__preserves__unmarked_language_if_Nonblockingness_branching__epdaS_required_edges: "
  valid_epda G
  \<Longrightarrow> E = epdaS_required_edges G
  \<Longrightarrow> valid_epda (F_ALT_EPDA_RE G (epdaS_required_edges G))
  \<Longrightarrow>
    ATS_Language0.Nonblockingness_branching epdaH_configurations epdaH_initial_configurations
     epda_step_labels epdaH_step_relation epdaH_marking_condition G \<Longrightarrow>
    ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
     epdaH_unmarked_effect G
    \<subseteq> ATS_Language0.unmarked_language epdaH_initial_configurations epdaH_step_relation
        epdaH_unmarked_effect (F_ALT_EPDA_RE G (epdaS_required_edges G))"
  apply(rule epda_sub__equal_unmarked_language__Nonblockingness_branching_and_preservation_of_initial_marking_derivation)
      apply(force)
     apply(force)
    apply(simp add: epda_sub_def F_ALT_EPDA_RE_def Let_def valid_epda_def)
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_ALT_EPDA_RE_preserves_epdaH_initial_marking_derivations_at_end)
    apply(force)
   apply (metis epdaS_required_edges__vs__epdaH_required_edges)
  apply(force)
  done

lemma F_ALT_EPDA_RE__SOUND2: "
  F_EPDA_RE__SpecInput2 (G, E)
  \<Longrightarrow> F_EPDA_RE__SpecOutput2 (G, E) (F_ALT_EPDA_RE G E)"
  apply(simp add: F_EPDA_RE__SpecInput2_def F_EPDA_RE__SpecOutput2_def)
  apply(rule context_conjI)
   apply(rule F_ALT_EPDA_RE_preserves_DPDA)
    apply(force)
   apply(simp add: epdaS_required_edges_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_ALT_EPDA_RE_establishes_coblockbreeness__epdaS_required_edges)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_ALT_EPDA_RE_preserves_lang__epdaS_required_edges)
    apply(simp add: valid_dpda_def)
   apply(force)
  apply(rule context_conjI)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_ALT_EPDA_RE_preserves_unmarked_lang2__epdaS_required_edges)
     apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply(force)
   apply (metis PDA_to_epda epdaS_to_epdaH_unmarked_language valid_dpda_to_valid_pda)
  apply(rule impI)
  apply(rule context_conjI)
   apply(subgoal_tac "epdaH.unmarked_language G \<subseteq> epdaH.unmarked_language (F_ALT_EPDA_RE G (epdaS_required_edges G))")
    apply (metis PDA_to_epda epdaS_to_epdaH_unmarked_language valid_dpda_to_valid_pda)
   apply(rule F_ALT_EPDA_RE__preserves__unmarked_language_if_Nonblockingness_branching__epdaS_required_edges)
      apply(simp add: valid_dpda_def valid_pda_def)
     apply(force)
    apply (metis PDA_to_epda valid_dpda_to_valid_pda)
   apply(force)
  apply (metis DPDA_to_epdaH_determinism PDA_to_epda antisym epdaH.AX_is_forward_edge_deterministic_correspond_DB_SB epdaH.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long epdaH_language_Nonblockingness_from_operational_Nonblockingness epdaH_operational_Nonblockingness_from_language_Nonblockingness epda_inter_semantics_language_relationship valid_dpda_to_valid_pda)
  done

theorem F_EPDA_RE__SOUND2: "
  F_EPDA_RE__SpecInput2 (G, E)
  \<Longrightarrow> F_EPDA_RE__SpecOutput2 (G, E) (F_EPDA_RE G E)"
  apply(rule_tac t="F_EPDA_RE G E" and s="F_ALT_EPDA_RE G E" in ssubst)
   apply(rule F_EPDA_RE__vs_F_ALT_EPDA_RE)
   apply(simp add: F_EPDA_RE__SpecInput2_def F_EPDA_RE__SpecOutput2_def)
   apply(simp add:  valid_dpda_def valid_pda_def)
  apply(rule F_ALT_EPDA_RE__SOUND2)
  apply(force)
  done

hide_fact
  F_EPDA_R__vs_F_ALT_EPDA_RE
  F_EPDA_RE__vs_F_ALT_EPDA_RE
  F_ALT_EPDA_RE_preserves_PDA
  F_ALT_EPDA_REERev_preserves_edges
  epdaToSymbolE_preserves_valid_epda_step_label
  F_ALT_EPDA_RE_preserves_configuration
  F_ALT_EPDA_REC_preserves_configurations
  F_ALT_EPDA_REC_preserves_initial_configurations
  F_ALT_EPDA_REC_preserves_marking_configurations
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs
  F_ALT_EPDA_RE_C_preserves_configurations
  F_ALT_EPDA_RE_C_preserves_initial_configurations
  F_ALT_EPDA_RE_C_preserves_marking_configurations
  F_ALT_EPDA_RE_initial_simulation_preserves_derivation
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation
  F_ALT_EPDA_RE_preserves_step_relation
  F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation
  F_ALT_EPDA_RE_relation_step_simulation_maps_to_derivation_belongs
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marking_condition
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marking_condition
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_marked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_marked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms
  F_ALT_EPDA_RE_preserves_lang1
  F_ALT_EPDA_RE_preserves_unmarked_language1
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs
  F_ALT_EPDA_RE_C_rev_preserves_configurations
  F_ALT_EPDA_RE_C_rev_preserves_initial_configurations
  F_ALT_EPDA_REC_reverse
  F_ALT_EPDA_REC_reverse2
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation
  F_ALT_EPDA_RERev_preserves_step_relation
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_step_relation_step_simulation
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms
  F_ALT_EPDA_RE_C_rev_preserves_marking_configurations
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marking_condition
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_marked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect
  epdaS_epdaS_F_ALT_EPDA_RE_StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms
  F_ALT_EPDA_RE_preserves_lang2
  F_ALT_EPDA_RE_preserves_unmarked_language2
  F_ALT_EPDA_RE_preserves_derivation
  F_ALT_EPDA_RE__SOUND

end
