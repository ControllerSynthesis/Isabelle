section {*PRJ\_06\_03\_\_POST*}
theory
  PRJ_06_03__POST

imports
  L_ATS_Sched
  L_ATS_SchedF_Basic
  L_ATS_SchedF_DB
  L_ATS_SchedF_SB
  L_ATS_SchedF_SDB
  L_ATS_SchedUF_Basic
  L_ATS_SchedUF_DB
  L_ATS_SchedUF_SB
  L_ATS_SchedUF_SDB
  L_ATS_Sched_Basic
  L_ATS_Sched_DB
  L_ATS_Sched_DB0
  L_ATS_Sched_SB
  L_ATS_Sched_SDB
  L_ATS_Scheduler_Fragment
  L_Controllable
  PRJ_06_03__ENTRY

begin

lemmas LOCALE_DEFS_02c =
  ATS_Scheduler_Fragment_def
  ATS_SchedF_Basic_def
  ATS_SchedF_DB_def
  ATS_SchedF_SB_def
  ATS_SchedF_SDB_def
  ATS_SchedUF_Basic_def
  ATS_SchedUF_DB_def
  ATS_SchedUF_SB_def
  ATS_SchedUF_SDB_def
  ATS_Sched_def
  ATS_Sched_Basic_def
  ATS_Sched_DB0_def
  ATS_Sched_DB_def
  ATS_Sched_SB_def
  ATS_Sched_SDB_def
  L_Controllable_def

end
