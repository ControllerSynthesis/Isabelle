section {*PRJ\_06\_07\_\_POST*}
theory
  PRJ_06_07__POST

imports
  L_BF_sum_HF
  L_BF_sum_HFS
  L_BF_sum_HFS_Rest
  L_BF_sum_HF_Rest
  L_BF_sum_S
  L_BF_sum_S_Rest
  PRJ_06_07__ENTRY
  interpretation_scheme_autFS
  interpretation_scheme_autHF
  interpretation_scheme_autHFS
  interpretation_scheme_autS
  interpretation_schemes_cfg

begin

lemmas LOCALE_DEFS_interpretation_schemes =
  LOCALE_DEFS_autS
  LOCALE_DEFS_autHF
  LOCALE_DEFS_autHFS
  LOCALE_DEFS_autFS
  BF_sum_HF_def
  BF_sum_HFS_def
  BF_sum_HFS_Rest_def
  BF_sum_HF_Rest_def
  BF_sum_S_def
  BF_sum_S_Rest_def

lemmas LOCALE_DEFS =
  LOCALE_DEFS_ALL
  LOCALE_DEFS_interpretation_schemes

end

