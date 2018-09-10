section {*I\_kparser\_main*}
theory
  I_kparser_main

imports
  I_kparser_HFS_HF
  I_kparser_S_HFS
  I_kparser_S_FS

begin

lemma parserS_inst_BF_LinDBRest_DetR_LaOp_axioms: "
  BF_LinDBRest_DetR_LaOp_axioms valid_parser parserS_configurations
     parserS_initial_configurations parser_step_labels parserS_step_relation
     parserS_marking_condition parserS_marked_effect parserS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserS_get_scheduler (@)
     parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB
     parserS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule parserS_vs_parserHFS.Nonblockingness_translation_rest2)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(metis parserHFS_inst_hlp_BF_LinDBRest_DetR_LaOp parserS_vs_parserHFS_Nonblockingness_and_lang_transfer parserS_vs_parserHFS_is_forward_deterministic_accessible_preserved)
  done

interpretation "parserS" : loc_autS_5
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* scheduler_fragments *)
  "parser_scheduler_fragments"
  (* empty_scheduler_fragment *)
  "parser_empty_scheduler_fragment"
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "parser_unfixed_schedulers"
  (* empty_unfixed_scheduler *)
  "parser_empty_unfixed_scheduler"
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  "parser_unfixed_scheduler_extendable"
  (* schedulers *)
  "parser_schedulers"
  (* initial_schedulers *)
  "parser_schedulers"
  (* empty_scheduler *)
  "parser_empty_scheduler"
  (* get_scheduler *)
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms parserS_inst_ATS_SchedUF_DB_axioms parserS_inst_ATS_SchedF_DB_axioms parserS_inst_ATS_Sched_DB0_axioms parserS_inst_ATS_Sched_DB_axioms parserS_inst_ATS_Sched_axioms )
  apply(simp add: parserS_inst_BF_LinDBRest_DetR_LaOp_axioms )
  done

lemma parser_inst_BF_LinDB_OpLa_axioms: "
  BF_LinDB_OpLa_axioms valid_parser parserS_configurations
     parserS_initial_configurations parser_step_labels parserS_step_relation
     parserS_marking_condition parserS_marked_effect parserS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserS_get_scheduler (@)
     parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB
     parserS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="parserS.unmarked_language M"
      and s="parserHFS.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis parserS_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="parserS.marked_language M"
      and s="parserHFS.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis parserS_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="parserHFS.unmarked_language M"
      and s="parserHF.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis equalityI parserHF.AX_unmarked_language_finite parserHFS.AX_unmarked_language_finite parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation1 parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation2)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="parserHFS.marked_language M"
      and s="parserHF.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis equalityI parserHF.AX_marked_language_finite parserHFS.AX_marked_language_finite parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation1 parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation2)
  apply(rename_tac M)(*strict*)
  apply(rule parserHF.AX_BF_Bra_OpLa)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule parserHF_vs_parserHFS.bflin_to_bfbra)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="parserHFS.Nonblockingness_linear M"
      and s="parserHFS.Nonblockingness_linear_DB M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply (metis parserHFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(rename_tac M)(*strict*)
  apply(rule parserS_vs_parserHFS.Nonblockingness_translation1)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(force)
  done

interpretation "parserS" : loc_autS_6
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* scheduler_fragments *)
  "parser_scheduler_fragments"
  (* empty_scheduler_fragment *)
  "parser_empty_scheduler_fragment"
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "parser_unfixed_schedulers"
  (* empty_unfixed_scheduler *)
  "parser_empty_unfixed_scheduler"
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  "parser_unfixed_scheduler_extendable"
  (* schedulers *)
  "parser_schedulers"
  (* initial_schedulers *)
  "parser_schedulers"
  (* empty_scheduler *)
  "parser_empty_scheduler"
  (* get_scheduler *)
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms parserS_inst_ATS_SchedUF_DB_axioms parserS_inst_ATS_SchedF_DB_axioms parserS_inst_ATS_Sched_DB0_axioms parserS_inst_ATS_Sched_DB_axioms parserS_inst_ATS_Sched_axioms parserS_inst_BF_LinDBRest_DetR_LaOp_axioms )
  apply(simp add: parser_inst_BF_LinDB_OpLa_axioms )
  done

end
