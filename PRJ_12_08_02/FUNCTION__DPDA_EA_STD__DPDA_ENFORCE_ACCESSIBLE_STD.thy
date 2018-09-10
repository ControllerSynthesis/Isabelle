section {*FUNCTION\_\_DPDA\_EA\_STD\_\_DPDA\_ENFORCE\_ACCESSIBLE\_STD*}
theory
  FUNCTION__DPDA_EA_STD__DPDA_ENFORCE_ACCESSIBLE_STD

imports
  PRJ_12_08_02__ENTRY

begin

lemma F_DPDA_EA_STD__preserves_DPDA: "
  valid_dpda G
  \<Longrightarrow> valid_dpda (F_DPDA_EA_STD G)"
  apply(simp add: F_DPDA_EA_STD_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" and E="(F_DPDA_DAE G)" in F_EPDA_RE__SOUND)
   apply(simp add: F_EPDA_RE__SpecInput_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_DPDA_DAE__SOUND)
    apply(simp add: F_DPDA_DAE__SpecInput_def)
   apply(simp add: F_DPDA_DAE__SpecOutput_def)
   apply(thin_tac "F_DPDA_DAE G = epdaH_accessible_edges G")
   apply (metis epdaH_accessible_edges_vs_epdaS_accessible_edges valid_dpda_def valid_pda_def)
  apply(simp add: F_EPDA_RE__SpecOutput_def)
  done

lemma F_DPDA_EA_STD__preserves_lang: "
  valid_dpda G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_DPDA_EA_STD G)"
  apply(simp add: F_DPDA_EA_STD_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" and E="(F_DPDA_DAE G)" in F_EPDA_RE__SOUND)
   apply(simp add: F_EPDA_RE__SpecInput_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_DPDA_DAE__SOUND)
    apply(simp add: F_DPDA_DAE__SpecInput_def)
   apply(simp add: F_DPDA_DAE__SpecOutput_def)
   apply(thin_tac "F_DPDA_DAE G = epdaH_accessible_edges G")
   apply (metis epdaH_accessible_edges_vs_epdaS_accessible_edges valid_dpda_def valid_pda_def)
  apply(simp add: F_EPDA_RE__SpecOutput_def)
  done

lemma F_DPDA_EA_STD__preserves_unmarked_language: "
  valid_dpda G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_DPDA_EA_STD G)"
  apply(simp add: F_DPDA_EA_STD_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" and E="(F_DPDA_DAE G)" in F_EPDA_RE__SOUND)
   apply(simp add: F_EPDA_RE__SpecInput_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_DPDA_DAE__SOUND)
    apply(simp add: F_DPDA_DAE__SpecInput_def)
   apply(simp add: F_DPDA_DAE__SpecOutput_def)
   apply(thin_tac "F_DPDA_DAE G = epdaH_accessible_edges G")
   apply (metis epdaH_accessible_edges_vs_epdaS_accessible_edges valid_dpda_def valid_pda_def)
  apply(simp add: F_EPDA_RE__SpecOutput_def)
  done

lemma F_DPDA_EA_STD__enforces_accessible: "
  valid_dpda G
  \<Longrightarrow> epdaS.accessible (F_DPDA_EA_STD G)"
  apply(simp add: F_DPDA_EA_STD_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" and E="(F_DPDA_DAE G)" in F_EPDA_RE__SOUND)
   apply(simp add: F_EPDA_RE__SpecInput_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in F_DPDA_DAE__SOUND)
    apply(simp add: F_DPDA_DAE__SpecInput_def)
   apply(simp add: F_DPDA_DAE__SpecOutput_def)
   apply(thin_tac "F_DPDA_DAE G = epdaH_accessible_edges G")
   apply (metis epdaH_accessible_edges_vs_epdaS_accessible_edges valid_dpda_def valid_pda_def)
  apply(simp add: F_EPDA_RE__SpecOutput_def)
  done

lemma F_DPDA_EA_STD__preserves_epdaH_no_livelocks_from_marking_states: "
  valid_dpda G
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states G
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states (F_DPDA_EA_STD G)"
  apply(simp add: epdaH_no_livelocks_from_marking_states_def F_DPDA_EA_STD_def)
  apply(clarsimp)
  apply(rename_tac d n e c)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(simp add: F_EPDA_R_def F_EPDA_RE_def F_DPDA_DAE_def Let_def)
  apply(rename_tac d n e c)(*strict*)
  apply(rule epdaH.derivation_initialI)
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d n e c ca)(*strict*)
   apply(simp add: get_configuration_def epdaH_initial_configurations_def epdaH.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac d n e c ca)(*strict*)
    apply(simp add: F_ALT_EPDA_RE_def F_DPDA_DAE_def Let_def F_EPDA_R_def F_EPDA_RE_def)
   apply(rename_tac d n e c ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac d n e c ca)(*strict*)
    apply(simp add: F_ALT_EPDA_RE_def F_DPDA_DAE_def Let_def F_EPDA_R_def F_EPDA_RE_def)
   apply(rename_tac d n e c ca)(*strict*)
   apply(simp add: F_ALT_EPDA_RE_def F_DPDA_DAE_def Let_def epdaH_configurations_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(simp add: F_ALT_EPDA_RE_def F_DPDA_DAE_def Let_def F_EPDA_R_def F_EPDA_RE_def)
  apply(rename_tac d n e c)(*strict*)
  apply(simp add: epdaH.derivation_initial_def)
  apply(clarsimp)
  apply(thin_tac "d n = Some (pair (Some e) c)")
  apply(thin_tac "case d 0 of None \<Rightarrow> False | Some (pair a b) \<Rightarrow> b \<in> epdaH_initial_configurations (F_EPDA_RE G (F_DPDA_DAE G)) \<and> a = None")
  apply(rename_tac d n e c)(*strict*)
  apply(thin_tac "edge_src e \<in> epda_marking (F_EPDA_RE G (F_DPDA_DAE G))")
  apply(thin_tac "edge_event e = None")
  apply(simp (no_asm) add: epdaH.derivation_def)
  apply(rename_tac d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac i)
   apply(rename_tac d i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(simp add: epdaH.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac d i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac d nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d nat a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d nat a)(*strict*)
   prefer 2
   apply(rule_tac
      n="nat"
      and m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac d nat a)(*strict*)
     apply(force)
    apply(rename_tac d nat a)(*strict*)
    apply(force)
   apply(rename_tac d nat a)(*strict*)
   apply(force)
  apply(rename_tac d nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat e1 e2 c1 c2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d nat e1 e2 c1 c2 w)(*strict*)
  apply(simp add: F_ALT_EPDA_RE_def F_DPDA_DAE_def Let_def F_EPDA_R_def F_EPDA_RE_def)
  done

definition F_DPDA_EA_STD__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EA_STD__SpecInput G \<equiv>
  valid_dpda G
  \<and> nonblockingness_language (epdaS.unmarked_language G) (epdaS.marked_language G)
  \<and> epdaH_no_livelocks_from_marking_states G"

definition F_DPDA_EA_STD__SpecOutput :: "
  ('p, 'event, 'stack) epda
  \<Rightarrow> ('state, 'event, 'stackx) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_EA_STD__SpecOutput Gi Go \<equiv>
  valid_dpda Go
  \<and> epdaS.marked_language Gi = epdaS.marked_language Go
  \<and> epdaS.unmarked_language Gi = epdaS.unmarked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epdaS.accessible Go
  \<and> epdaH_no_livelocks_from_marking_states Go"

theorem F_DPDA_EA_STD__SOUND: "
  F_DPDA_EA_STD__SpecInput G
  \<Longrightarrow> F_DPDA_EA_STD__SpecOutput G (F_DPDA_EA_STD G)"
  apply(simp add: F_DPDA_EA_STD__SpecInput_def F_DPDA_EA_STD__SpecOutput_def)
  apply(rule conjI)
   apply (metis F_DPDA_EA_STD__preserves_DPDA)
  apply(rule context_conjI)
   apply(rule F_DPDA_EA_STD__preserves_lang)
   apply(force)
  apply(rule context_conjI)
   apply(subgoal_tac "epdaS.unmarked_language G = epdaS.unmarked_language (F_DPDA_EA_STD G)")
    apply(force)
   apply(rule F_DPDA_EA_STD__preserves_unmarked_language)
   apply(force)
  apply(rule context_conjI)
   apply(subgoal_tac "epdaS.unmarked_language G = epdaS.unmarked_language (F_DPDA_EA_STD G)")
    apply(force)
   apply(rule F_DPDA_EA_STD__preserves_unmarked_language)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_EA_STD__enforces_accessible)
   apply(force)
  apply(rule F_DPDA_EA_STD__preserves_epdaH_no_livelocks_from_marking_states)
   apply(force)
  apply(force)
  done

hide_fact F_DPDA_EA_STD__preserves_DPDA
hide_fact F_DPDA_EA_STD__preserves_lang
hide_fact F_DPDA_EA_STD__preserves_unmarked_language
hide_fact F_DPDA_EA_STD__enforces_accessible
hide_fact F_DPDA_EA_STD__preserves_epdaH_no_livelocks_from_marking_states

end
