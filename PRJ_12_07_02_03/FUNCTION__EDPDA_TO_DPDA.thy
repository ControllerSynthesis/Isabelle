section {*FUNCTION\_\_EDPDA\_TO\_DPDA*}
theory
  FUNCTION__EDPDA_TO_DPDA

imports
  PRJ_12_07_02_03__ENTRY

begin

theorem F_EDPDA_TO_DPDA_makesDPDA: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> valid_dpda (F_EDPDA_TO_DPDA G)"
  apply(simp add: valid_dpda_def valid_pda_def F_EDPDA_TO_DPDA_def)
  apply(rule conjI)
   apply (metis F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges F_EDPDA_RNPE_preserves_valid_epda epdaS_epdaS_F_EDPDA_RMPOE_StateSimLR.AX_TSstructure_relation_TSstructure2_belongs F_EDPDA_RMPOE__relation_LR_TSstructure_def)
  apply(rule conjI)
   apply(subgoal_tac "epda_no_mass_popping_edges (F_EDPDA_RMPOE (F_EDPDA_RNPE G))")
    prefer 2
    apply (metis F_EDPDA_RMPOE_enforces_epda_no_mass_popping_edges F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_preserves_valid_epda)
   apply(subgoal_tac "epda_no_nil_popping_edges (F_EDPDA_RMPOE (F_EDPDA_RNPE G))")
    prefer 2
    apply (metis F_EDPDA_RMPOE_preserves_epda_no_nil_popping_edges F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges F_EDPDA_RNPE_preserves_valid_epda)
   apply(simp add: epda_no_mass_popping_edges_def epda_no_nil_popping_edges_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)+
     apply(rename_tac e)(*strict*)
     apply(case_tac "edge_pop e")
      apply(rename_tac e)(*strict*)
      apply(force)
     apply(rename_tac e a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac e a list)(*strict*)
      apply(force)
     apply(rename_tac e a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply (metis F_EDPDA_RMPOE_preserves_is_forward_edge_deterministic_accessible F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible)
  done

theorem F_EDPDA_TO_DPDA_preservesLang: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.marked_language G = epdaS.marked_language (F_EDPDA_TO_DPDA G)"
  apply (metis F_EDPDA_RMPOE_preserves_lang F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible F_EDPDA_RNPE_preserves_lang)
  done

theorem F_EDPDA_TO_DPDA_preservesULang: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.unmarked_language G = epdaS.unmarked_language (F_EDPDA_TO_DPDA G)"
  apply (metis F_EDPDA_RMPOE_preserves_unmarked_language F_EDPDA_TO_DPDA_def F_EDPDA_RNPE_enforces_epda_no_nil_popping_edges F_EDPDA_RNPE_preserves_valid_epda F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible F_EDPDA_RNPE_preserves_unmarked_language)
  done

theorem F_EDPDA_TO_DPDA_generates_epdaH_no_livelocks_from_marking_states: "
  valid_epda G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epda_no_empty_steps_from_marking_states G
  \<Longrightarrow> epdaH_no_livelocks_from_marking_states (F_EDPDA_TO_DPDA G)"
  apply(simp add: F_EDPDA_TO_DPDA_def)
  apply(rule_tac
      M="F_EDPDA_RNPE G"
      in F_EDPDA_RMPOE_enforces_epdaH_no_livelocks_from_marking_states)
     apply (metis F_EDPDA_RNPE_preserves_valid_epda)
    apply (metis F_EDPDA_RNPE_preserves_is_forward_edge_deterministic_accessible)
   apply(rule_tac
      M="G"
      in F_EDPDA_RNPE_preserves_epda_no_empty_steps_from_marking_states)
    apply(force)
   apply(force)
  apply(force)
  done

definition F_EDPDA_TO_DPDA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_TO_DPDA__SpecInput G \<equiv>
  F_EDPDA_RNPE__SpecInput G"

definition F_EDPDA_TO_DPDA__SpecOutput :: "
  ('stateA, 'event, 'stack) epda
  \<Rightarrow> ('stateB, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EDPDA_TO_DPDA__SpecOutput Gi Go \<equiv>
  F_EDPDA_RMPOE__SpecOutput Gi Go"

theorem F_EDPDA_TO_DPDA__SOUND: "
  F_EDPDA_TO_DPDA__SpecInput G
  \<Longrightarrow> F_EDPDA_TO_DPDA__SpecOutput G (F_EDPDA_TO_DPDA G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in F_EDPDA_RNPE__SOUND)
   apply(simp add: F_EDPDA_TO_DPDA__SpecInput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="F_EDPDA_RNPE G" in F_EDPDA_RMPOE__SOUND)
   apply(simp add: F_EDPDA_TO_DPDA__SpecInput_def F_EDPDA_RMPOE__SpecInput_def F_EDPDA_RNPE__SpecOutput_def)
  apply(simp add: F_EDPDA_TO_DPDA__SpecOutput_def F_EDPDA_TO_DPDA__SpecInput_def F_EDPDA_TO_DPDA_def F_EDPDA_RNPE__SpecInput_def F_EDPDA_RMPOE__SpecOutput_def F_EDPDA_RNPE__SpecOutput_def)
  done

end
