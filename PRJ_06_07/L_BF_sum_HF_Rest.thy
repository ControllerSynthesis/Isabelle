section {*L\_BF\_sum\_HF\_Rest*}
theory
  L_BF_sum_HF_Rest

imports
  PRJ_06_07__ENTRY

begin

locale BF_sum_HF_Rest =
  BF_BraSBRest_DetHSB_LaOp
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  +
  BF_BraSBRest_DetHDB_LaOp
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  +
  BF_BraDBRest_DetHSB_LaOp
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler :: 'conf \<Rightarrow> 'fixed_scheduler"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  +
  BF_BraDBRest_DetHDB_LaOp
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> 'event list set"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "set_history :: 'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "get_history :: 'conf \<Rightarrow> 'history"
  "fixed_schedulers :: 'TSstructure \<Rightarrow> 'fixed_scheduler set"
  "empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'fixed_scheduler"
  "fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'fixed_scheduler \<Rightarrow> bool"
  "get_fixed_scheduler_DB :: 'TSstructure \<Rightarrow> ('label, 'conf) derivation \<Rightarrow> nat \<Rightarrow> 'fixed_scheduler"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect histories history_fragments empty_history empty_history_fragment set_history extend_history join_history_fragments get_history fixed_schedulers empty_fixed_scheduler fixed_scheduler_extendable get_fixed_scheduler get_fixed_scheduler_DB

end
