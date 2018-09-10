section {*FUNCTION\_\_DPDA\_TO\_SDPDA*}
theory
  FUNCTION__DPDA_TO_SDPDA

imports
  PRJ_12_04_04_05__ENTRY

begin

theorem F_DPDA_TO_SDPDA_preserves_language: "
  valid_dpda G
  \<Longrightarrow> epdaS.marked_language (F_DPDA_TO_SDPDA G) = epdaS.marked_language G"
  apply(simp add: F_DPDA_TO_SDPDA_def)
  apply(simp add: Let_def)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      and s="epdaS.marked_language ((F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))))"
      in subst)
   apply(rule F_DPDA_RMPUE__preserves_lang)
     apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__produces_push_and_pop_edges_seperated F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_SPPE__preserves_read_edges_seperated)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_RNE__preserves_read_edges_seperated)
     apply (metis F_DPDA_SEE__preserves_DPDA)
    apply (metis F_DPDA_SEE__produces_read_edges_seperated)
   apply(rule F_FRESH_is_fresh)
   apply(subgoal_tac "valid_dpda (F_DPDA_SEE G)")
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply (metis F_DPDA_SEE__preserves_DPDA)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G)))))"
      and s="epdaS.marked_language ((F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G)))))"
      in ssubst)
   apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_lang F_DPDA_SEE__preserves_DPDA)
  apply(rule_tac
      t="epdaS.marked_language (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))"
      and s="epdaS.marked_language (F_DPDA_SEE G)"
      in ssubst)
   apply (metis F_DPDA_RNE__preserves_lang F_DPDA_SEE__preserves_DPDA)
  apply (metis F_DPDA_SEE__preserves_lang)
  done

definition valid_sdpda2 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "valid_sdpda2 G \<equiv>
  valid_dpda G
  \<and> read_edges_seperated G
  \<and> pop_edges_seperated G
  \<and> push_edges_seperated G
  \<and> mass_push_edges_splitted G
  \<and> neutral_edges_removed G
  \<and> push_and_pop_edges_seperated G"

lemma F_DPDA_TO_SDPDA_makes_SDPDAx: "
  valid_dpda G
  \<Longrightarrow> valid_sdpda2 (F_DPDA_TO_SDPDA G)"
  apply(simp add: valid_sdpda2_def)
  apply(rule context_conjI)
   apply(simp add: F_DPDA_TO_SDPDA_def)
   apply(simp add: Let_def)
   apply(rule F_DPDA_RMPUE__preserves_DPDA)
     apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__produces_push_and_pop_edges_seperated F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_SPPE__preserves_read_edges_seperated)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_RNE__preserves_read_edges_seperated)
     apply (metis F_DPDA_SEE__preserves_DPDA)
    apply (metis F_DPDA_SEE__produces_read_edges_seperated)
   apply(rule F_FRESH_is_fresh)
   apply(subgoal_tac "valid_dpda (F_DPDA_SEE G)")
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply (metis F_DPDA_SEE__preserves_DPDA)
  apply(rule context_conjI)
   apply(simp add: F_DPDA_TO_SDPDA_def)
   apply(simp add: Let_def)
   apply(rule F_DPDA_RMPUE__preserves_read_edges_seperated)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_SPPE__preserves_read_edges_seperated)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply (rule F_DPDA_RNE__preserves_read_edges_seperated)
     apply (metis F_DPDA_SEE__preserves_DPDA)
    apply (metis F_DPDA_SEE__produces_read_edges_seperated)
   apply(rule F_FRESH_is_fresh)
   apply(subgoal_tac "valid_dpda (F_DPDA_SEE G)")
    apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
   apply (metis F_DPDA_SEE__preserves_DPDA)
  apply(simp add: F_DPDA_TO_SDPDA_def)
  apply(simp add: Let_def)
  apply(subgoal_tac "push_and_pop_edges_seperated (F_DPDA_RMPUE (F_DPDA_SPPE (F_DPDA_RNE (F_DPDA_SEE G) (F_FRESH (epda_gamma (F_DPDA_SEE G))))))")
   prefer 2
   apply(rule F_DPDA_RMPUE__preserves_push_and_pop_edges_seperated)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply(rule F_DPDA_SPPE__produces_push_and_pop_edges_seperated)
   apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
  apply(rule conjI)
   apply(simp add: empty_push_edge_def push_and_pop_edges_seperated_def pop_edges_seperated_def push_edges_seperated_def strict_empty_push_edge_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(simp add: read_edges_seperated_def F_DPDA_SPPE__edge_if_def)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(case_tac "edge_event e")
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(simp add: FB_executing_edge_def)
   apply(simp add: strict_executing_edge_def)
   apply(simp add: valid_dpda_def valid_pda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_RMPUE__produces_push_edges_seperated)
       apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
      apply (metis valid_dpda_def)
     apply(force)
    apply(rule F_DPDA_RMPUE__produces_mass_push_edges_splitted)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
   apply(force)
  apply(rule conjI)
   apply(rule F_DPDA_RMPUE__produces_mass_push_edges_splitted)
   apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA F_DPDA_SEE__preserves_DPDA)
  apply(subgoal_tac "valid_dpda (F_DPDA_SEE G)")
   prefer 2
   apply (metis F_DPDA_SEE__preserves_DPDA)
  apply(rule conjI)
   apply(rule F_DPDA_RMPUE__preserves_neutral_edges_removed)
    apply (metis F_DPDA_RNE__preserves_DPDA F_DPDA_SPPE__preserves_DPDA)
   apply(rule F_DPDA_SPPE__preserves_neutral_edges_removed)
    apply (metis F_DPDA_RNE__preserves_DPDA)
   apply(rule F_DPDA_RNE__produces_neutral_edges_removed)
    apply (metis)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_dpda_def valid_pda_def valid_epda_def)
  apply (metis)
  done

lemma valid_sdpda2_implies_valid_simple_dpda: "
  valid_sdpda2 G
  \<Longrightarrow> valid_simple_dpda G"
  apply(simp add: valid_simple_dpda_def)
  apply(rule conjI)
   apply(simp add: valid_sdpda2_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac "edge_event e")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rename_tac e a)(*strict*)
   apply(clarsimp)
   apply(simp add: read_edges_seperated_def valid_sdpda2_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e a)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(simp add: FB_executing_edge_def strict_executing_edge_def)
  apply(rename_tac e)(*strict*)
  apply(case_tac "edge_push e")
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. edge_push e = w' @ [x']")
   apply(rename_tac e a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac e a list)(*strict*)
  apply(thin_tac "edge_push e= a # list")
  apply(clarsimp)
  apply(rename_tac e w' x')(*strict*)
  apply(subgoal_tac "\<exists>x. edge_pop e=[x]")
   apply(rename_tac e w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac e w' x' x)(*strict*)
   apply(subgoal_tac "push_and_pop_edges_seperated G")
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(simp add: valid_sdpda2_def)
   apply(rename_tac e w' x' x)(*strict*)
   apply(subgoal_tac "mass_push_edges_splitted G")
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(simp add: valid_sdpda2_def)
   apply(rename_tac e w' x' x)(*strict*)
   apply(subgoal_tac "neutral_edges_removed G")
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(simp add: valid_sdpda2_def)
   apply(rename_tac e w' x' x)(*strict*)
   apply(simp add: neutral_edges_removed_def mass_push_edges_splitted_def push_and_pop_edges_seperated_def)
   apply(erule_tac
      x="e"
      and P="\<lambda>e. \<not> F_DPDA_SPPE__edge_if e"
      in ballE)
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e w' x' x)(*strict*)
   apply(erule_tac
      x="e"
      and P="\<lambda>e. \<not> F_DPDA_RMPUE__edge_if e"
      in ballE)
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e w' x' x)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e w' x' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e w' x' x)(*strict*)
   apply(simp add: F_DPDA_SPPE__edge_if_def F_DPDA_RMPUE__edge_if_def FB_neutral_edge_def)
   apply(case_tac w')
    apply(rename_tac e w' x' x)(*strict*)
    apply(force)
   apply(rename_tac e w' x' x a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e w' x')(*strict*)
  apply(rule valid_pda_edge_pop_single)
   apply(rename_tac e w' x')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e w' x')(*strict*)
  apply(simp add: valid_sdpda2_def valid_dpda_def)
  done

definition F_DPDA_TO_SDPDA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_TO_SDPDA__SpecInput G \<equiv>
  valid_dpda G"

definition F_DPDA_TO_SDPDA__SpecOutput :: "
  ('stateA, 'event, 'stackA DT_symbol) epda
  \<Rightarrow> ('stateB, 'event, 'stackB DT_symbol) epda
  \<Rightarrow> bool"
  where
    "F_DPDA_TO_SDPDA__SpecOutput Gi Go \<equiv>
  valid_simple_dpda Go"

theorem F_DPDA_TO_SDPDA_makes_SDPDA: "
  valid_dpda G
  \<Longrightarrow> valid_simple_dpda (F_DPDA_TO_SDPDA G)"
  apply (metis F_DPDA_TO_SDPDA_makes_SDPDAx valid_sdpda2_implies_valid_simple_dpda)
  done

theorem F_DPDA_TO_SDPDA__SOUND: "
  F_DPDA_TO_SDPDA__SpecInput G
  \<Longrightarrow> F_DPDA_TO_SDPDA__SpecOutput G (F_DPDA_TO_SDPDA G)"
  apply(simp add: F_DPDA_TO_SDPDA__SpecOutput_def F_DPDA_TO_SDPDA__SpecInput_def)
  apply(rule F_DPDA_TO_SDPDA_makes_SDPDA)
  apply(force)
  done

end
