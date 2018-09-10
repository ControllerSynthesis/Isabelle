section {*PRJ\_09\_\_POST*}
theory
  PRJ_09__POST

imports
  I_cfgLM
  I_cfgRM
  I_cfgSTD
  I_cfg_base
  I_cfg_lemmas
  PRJ_09__ENTRY

begin

lemmas CFG_interpretations =
  cfgLM_inst_AX_step_relation_preserves_belongs
  cfgRM_inst_AX_step_relation_preserves_belongs
  cfgBASE_inst_AX_initial_configuration_belongs
  cfgSTD_inst_AX_step_relation_preserves_belongs
  cfgSTD_inst_ATS_Language_by_Finite_Derivations_axioms
  cfgSTD_inst_ATS_String_State_Modification_axioms
  cfgSTD_inst_ATS_axioms
  cfgSTD_inst_BF_Bra_DetR_LaOp_axioms
  cfgSTD_inst_BF_Bra_OpLa_axioms
  cfgLM_inst_ATS_Language_by_Finite_Derivations_axioms
  cfgLM_inst_ATS_String_State_Modification_axioms
  cfgLM_inst_ATS_axioms
  cfgLM_inst_BF_Bra_DetR_LaOp_axioms
  cfgLM_inst_BF_Bra_OpLa_axioms
  cfgRM_inst_ATS_Language_by_Finite_Derivations_axioms
  cfgRM_inst_ATS_String_State_Modification_axioms
  cfgRM_inst_ATS_axioms
  cfgRM_inst_BF_Bra_DetR_LaOp_axioms
  cfgRM_inst_BF_Bra_OpLa_axioms

end
