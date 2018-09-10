section {*I\_epda\_main*}
theory
  I_epda_main

imports
  I_epda_HS_H
  I_epda_S_HS

begin

lemma epdaS_inst_BF_LinDBRest_DetR_LaOp_axioms: "
  BF_LinDBRest_DetR_LaOp_axioms valid_epda epdaS_configurations
     epdaS_initial_configurations epda_step_labels epdaS_step_relation
     epdaS_marking_condition epdaS_marked_effect epdaS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaS_get_scheduler (@) epdaS_set_unfixed_scheduler_DB
     epdaS_get_unfixed_scheduler_DB epdaS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule epdaS_vs_epdaHS.Nonblockingness_translation_rest2)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(metis epdaHS_inst_hlp_BF_LinDBRest_DetR_LaOp epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer epdaS_vs_epdaHS_is_forward_deterministic_accessible_preserved)
  done

interpretation "epdaS" : loc_autS_5
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* scheduler_fragments *)
  "epda_effects"
  (* empty_scheduler_fragment *)
  epda_empty_scheduler_fragment
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "epda_effects"
  (* empty_unfixed_scheduler *)
  epda_empty_unfixed_scheduler
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  epda_unfixed_scheduler_extendable
  (* schedulers *)
  "epda_effects"
  (* initial_schedulers *)
  "epda_effects"
  (* empty_scheduler *)
  epda_empty_scheduler
  (* get_scheduler *)
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms epdaS_inst_ATS_Language_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_Basic_axioms epdaS_inst_ATS_Scheduler_Fragment_axioms epdaS_inst_ATS_SchedUF_Basic_axioms epdaS_inst_ATS_SchedUF_DB_axioms epdaS_inst_ATS_SchedF_Basic_axioms epdaS_inst_ATS_SchedF_DB_axioms epdaS_inst_ATS_Sched_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_DB0_axioms epdaS_inst_ATS_Sched_DB_axioms )
  apply(simp add: epdaS_inst_BF_LinDBRest_DetR_LaOp_axioms )
  done

lemma epdaS_inst_BF_LinDB_OpLa_axioms: "
  BF_LinDB_OpLa_axioms valid_epda epdaS_configurations
     epdaS_initial_configurations epda_step_labels epdaS_step_relation
     epdaS_marking_condition epdaS_marked_effect epdaS_unmarked_effect
     epda_effects right_quotient_word (@) epda_unfixed_scheduler_extendable
     epdaS_get_scheduler (@) epdaS_set_unfixed_scheduler_DB
     epdaS_get_unfixed_scheduler_DB epdaS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaS.unmarked_language M"
      and s="epdaHS.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaS.marked_language M"
      and s="epdaHS.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis epdaS_vs_epdaHS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaHS.unmarked_language M"
      and s="epdaH.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis equalityI epdaH.AX_unmarked_language_finite epdaHS.AX_unmarked_language_finite epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_unmarked_language_translation1 epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_unmarked_language_translation2)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaHS.marked_language M"
      and s="epdaH.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis equalityI epdaH.AX_marked_language_finite epdaHS.AX_marked_language_finite epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_marked_language_translation2 epdaH_vs_epdaHS.ATS_Branching_Versus_Linear2_marked_language_translation1)
  apply(rename_tac M)(*strict*)
  apply(rule epdaH.AX_BF_Bra_OpLa)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule epdaH_vs_epdaHS.bflin_to_bfbra)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="epdaHS.Nonblockingness_linear M"
      and s="epdaHS.Nonblockingness_linear_DB M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis epdaHS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(rename_tac M)(*strict*)
  apply(rule epdaS_vs_epdaHS.Nonblockingness_translation1)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(force)
  done

interpretation "epdaS" : loc_autS_6
  (* TSstructure *)
  "valid_epda"
  (* configurations *)
  "epdaS_configurations"
  (* initial_configurations *)
  "epdaS_initial_configurations"
  (* step_labels *)
  "epda_step_labels"
  (* step_relation *)
  "epdaS_step_relation"
  (* effects *)
  "epda_effects"
  (* marking_condition *)
  "epdaS_marking_condition"
  (* marked_effect *)
  "epdaS_marked_effect"
  (* unmarked_effect *)
  "epdaS_unmarked_effect"
  (* destinations *)
  "epda_destinations"
  (* get_destinations *)
  "epdaS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "epdaS_string_state"
  (* fixed_schedulers *)
  epda_fixed_schedulers
  (* empty_fixed_scheduler *)
  epda_empty_fixed_scheduler
  (* fixed_scheduler_extendable *)
  epda_fixed_scheduler_extendable
  (* scheduler_fragments *)
  "epda_effects"
  (* empty_scheduler_fragment *)
  epda_empty_scheduler_fragment
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "epda_effects"
  (* empty_unfixed_scheduler *)
  epda_empty_unfixed_scheduler
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  epda_unfixed_scheduler_extendable
  (* schedulers *)
  "epda_effects"
  (* initial_schedulers *)
  "epda_effects"
  (* empty_scheduler *)
  epda_empty_scheduler
  (* get_scheduler *)
  "epdaS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "epdaS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "epdaS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "epdaS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS)
  apply(simp add: epdaS_inst_AX_initial_configuration_belongs epdaS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: epdaS_inst_ATS_Language_by_Finite_Derivations_axioms epdaS_inst_ATS_String_State_Modification_axioms epdaS_inst_ATS_Language_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_Basic_axioms epdaS_inst_ATS_Scheduler_Fragment_axioms epdaS_inst_ATS_SchedUF_Basic_axioms epdaS_inst_ATS_SchedUF_DB_axioms epdaS_inst_ATS_SchedF_Basic_axioms epdaS_inst_ATS_SchedF_DB_axioms epdaS_inst_ATS_Sched_axioms )
  apply(simp add: epdaS_inst_ATS_Sched_DB0_axioms epdaS_inst_ATS_Sched_DB_axioms epdaS_inst_BF_LinDBRest_DetR_LaOp_axioms )
  apply(simp add: epdaS_inst_BF_LinDB_OpLa_axioms )
  done

end
