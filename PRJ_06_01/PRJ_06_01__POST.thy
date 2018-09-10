section {*PRJ\_06\_01\_\_POST*}
theory
  PRJ_06_01__POST

imports
  L_ATS
  L_ATS_Language
  L_ATS_Language0
  L_ATS_Destinations
  L_ATS_Language_by_Finite_Derivations
  L_ATS_List_Based_Effects
  L_ATS_Marking_Configurations
  L_ATS_String_State_Modification
  PRJ_06_01__ENTRY

begin

lemmas LOCALE_DEFS_02a =
  ATS_def
  ATS_Language_by_Finite_Derivations_def
  ATS_List_Based_Effects_def
  ATS_Marking_Configurations_def
  ATS_String_State_Modification_def
  ATS_Language_def
  ATS_Language0_def
  ATS_Destinations_def

end
