section {*PRJ\_06\_04\_\_POST*}
theory
  PRJ_06_04__POST

imports
  L_ATS_HISTCE_DB
  L_ATS_HISTCE_SB
  L_ATS_HISTCT_DB
  L_ATS_HISTCT_SB
  L_ATS_determHIST_DB
  L_ATS_determHIST_SB
  L_ATS_determHIST_SDB
  PRJ_06_04__ENTRY

begin

lemmas LOCALE_DEFS_02d =
  ATS_HistoryCE_DB_def
  ATS_HistoryCE_SB_def
  ATS_HistoryCT_DB_def
  ATS_HistoryCT_SB_def
  ATS_determHIST_DB_def
  ATS_determHIST_SB_def
  ATS_determHIST_SDB_def

end
