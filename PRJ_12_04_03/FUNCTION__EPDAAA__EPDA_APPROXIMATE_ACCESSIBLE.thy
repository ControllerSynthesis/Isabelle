section {*FUNCTION\_\_EPDAAA\_\_EPDA\_APPROXIMATE\_ACCESSIBLE*}
theory
  FUNCTION__EPDAAA__EPDA_APPROXIMATE_ACCESSIBLE

imports
  PRJ_12_04_03__ENTRY

begin

theorem F_EPDA_AA_spec: "
  valid_epda G
  \<Longrightarrow> F_EPDA_AA G k = G'
  \<Longrightarrow> epdaH.marked_language G = epdaH.marked_language G'
  \<and> epdaH.unmarked_language G = epdaH.unmarked_language G'
  \<and> valid_epda G'
  \<and> (valid_pda G \<longrightarrow> valid_pda G')
  \<and> (valid_dpda G \<longrightarrow> valid_dpda G')
  \<and> (valid_simple_dpda G \<longrightarrow> valid_simple_dpda G')
  \<and> (epdaH_livelock G \<longleftrightarrow> epdaH_livelock G')"
  apply(unfold F_EPDA_AA_def)
  apply(rule F_EPDA_R_spec)
     apply(force)
    prefer 3
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule F_EPDA_AIA_preserves_epdaH_accessible_states)
    apply(force)
   apply(simp add: F_EPDA_AIA_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_EPDA_AIA_preserves_epdaH_accessible_edges)
   apply(force)
  apply(simp add: F_EPDA_AIA_def)
  apply(force)
  done

definition F_EPDA_AA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_AA__SpecInput G \<equiv>
  valid_epda G"

definition F_EPDA_AA__SpecOutput :: "
  ('stateA, 'event, 'stackA) epda
  \<Rightarrow> ('stateB, 'event, 'stackB) epda
  \<Rightarrow> bool"
  where
    "F_EPDA_AA__SpecOutput Gi Go \<equiv>
  epdaH.marked_language Gi = epdaH.marked_language Go
  \<and> epdaH.unmarked_language Gi = epdaH.unmarked_language Go
  \<and> valid_epda Go
  \<and> (valid_pda Gi \<longrightarrow> valid_pda Go)
  \<and> (valid_dpda Gi \<longrightarrow> valid_dpda Go)
  \<and> (valid_simple_dpda Gi \<longrightarrow> valid_simple_dpda Go)
  \<and> (epdaH_livelock Gi \<longleftrightarrow> epdaH_livelock Go)"

theorem F_EPDA_AA__SOUND: "
  F_EPDA_AA__SpecInput G
  \<Longrightarrow> F_EPDA_AA__SpecOutput G (F_EPDA_AA G k)"
  apply(simp add: F_EPDA_AA__SpecOutput_def F_EPDA_AA__SpecInput_def)
  apply(rule F_EPDA_AA_spec)
   apply(force)
  apply(force)
  done

end
