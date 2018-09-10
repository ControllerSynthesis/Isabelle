section {*L\_ATS\_Branching\_Versus\_Linear1*}
theory
  L_ATS_Branching_Versus_Linear1

imports
  L_ATS_Linear
  L_ATS_Branching

begin

lemma tl_nth_shift: "
  length w>i
  \<Longrightarrow> tl w ! i = w!(Suc i)"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(force)
  done

lemma bexI_conj: "
  P \<and> Q a \<and> a \<in> A
  \<Longrightarrow> P \<and> (\<exists>x\<in> A. Q x)"
  apply(force)
  done

locale ATS_Branching_Versus_Linear1 =
  GLIN : ATS_Linear
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "lin_configurations :: 'TSstructure \<Rightarrow> 'lin_conf set"
  "lin_initial_configurations :: 'TSstructure \<Rightarrow> 'lin_conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "lin_step_relation :: 'TSstructure \<Rightarrow> 'lin_conf \<Rightarrow> 'label \<Rightarrow> 'lin_conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "lin_marking_condition :: 'TSstructure \<Rightarrow> ('label, 'lin_conf) derivation \<Rightarrow> bool"
  "lin_marked_effect :: 'TSstructure \<Rightarrow> ('label, 'lin_conf) derivation \<Rightarrow> 'event list set"
  "lin_unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'lin_conf) derivation \<Rightarrow> 'event list set"
  "lin_fixed_schedulers :: 'TSstructure \<Rightarrow> 'lin_fixed_scheduler set"
  "lin_empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'lin_fixed_scheduler"
  "lin_fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'lin_fixed_scheduler \<Rightarrow> bool"
  "lin_scheduler_fragments :: 'TSstructure \<Rightarrow> 'lin_scheduler_fragment set"
  "lin_empty_scheduler_fragment :: 'TSstructure \<Rightarrow> 'lin_scheduler_fragment"
  "lin_join_scheduler_fragments :: 'lin_scheduler_fragment \<Rightarrow> 'lin_scheduler_fragment \<Rightarrow> 'lin_scheduler_fragment"
  "lin_unfixed_schedulers :: 'TSstructure \<Rightarrow> 'lin_unfixed_scheduler set"
  "lin_empty_unfixed_scheduler :: 'TSstructure \<Rightarrow> 'lin_unfixed_scheduler"
  "lin_unfixed_scheduler_right_quotient :: 'lin_unfixed_scheduler \<Rightarrow> 'lin_unfixed_scheduler \<Rightarrow> 'lin_scheduler_fragment option"
  "lin_extend_unfixed_scheduler :: 'lin_scheduler_fragment \<Rightarrow> 'lin_unfixed_scheduler \<Rightarrow> 'lin_unfixed_scheduler"
  "lin_unfixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'lin_unfixed_scheduler \<Rightarrow> bool"
  "lin_schedulers :: 'TSstructure \<Rightarrow> 'lin_scheduler set"
  "lin_initial_schedulers :: 'TSstructure \<Rightarrow> 'lin_scheduler set"
  "lin_empty_scheduler :: 'TSstructure \<Rightarrow> 'lin_scheduler"
  "lin_get_scheduler :: 'lin_conf \<Rightarrow> 'lin_scheduler"
  "lin_join_fixed_scheduler_unfixed_scheduler :: 'lin_fixed_scheduler \<Rightarrow> 'lin_unfixed_scheduler \<Rightarrow> 'lin_scheduler"
  "lin_extend_scheduler :: 'lin_scheduler_fragment \<Rightarrow> 'lin_scheduler \<Rightarrow> 'lin_scheduler"
  "lin_get_unfixed_scheduler :: 'lin_conf \<Rightarrow> 'lin_unfixed_scheduler"
  "lin_set_unfixed_scheduler :: 'lin_conf \<Rightarrow> 'lin_unfixed_scheduler \<Rightarrow> 'lin_conf"
  "lin_get_fixed_scheduler :: 'lin_conf \<Rightarrow> 'lin_fixed_scheduler"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "lin_set_history :: 'lin_conf \<Rightarrow> 'history \<Rightarrow> 'lin_conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "lin_get_history :: 'lin_conf \<Rightarrow> 'history"
  + GBRA : ATS_Branching
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "bra_configurations :: 'TSstructure \<Rightarrow> 'bra_conf set"
  "bra_initial_configurations :: 'TSstructure \<Rightarrow> 'bra_conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "bra_step_relation :: 'TSstructure \<Rightarrow> 'bra_conf \<Rightarrow> 'label \<Rightarrow> 'bra_conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "bra_marking_condition :: 'TSstructure \<Rightarrow> ('label, 'bra_conf) derivation \<Rightarrow> bool"
  "bra_marked_effect :: 'TSstructure \<Rightarrow> ('label, 'bra_conf) derivation \<Rightarrow> 'event list set"
  "bra_unmarked_effect :: 'TSstructure \<Rightarrow> ('label, 'bra_conf) derivation \<Rightarrow> 'event list set"
  "bra_fixed_schedulers :: 'TSstructure \<Rightarrow> 'bra_fixed_scheduler set"
  "bra_empty_fixed_scheduler :: 'TSstructure \<Rightarrow> 'bra_fixed_scheduler"
  "bra_fixed_scheduler_extendable :: 'TSstructure \<Rightarrow> 'bra_fixed_scheduler \<Rightarrow> bool"
  "bra_get_fixed_scheduler :: 'bra_conf \<Rightarrow> 'bra_fixed_scheduler"
  "histories :: 'TSstructure \<Rightarrow> 'history set"
  "history_fragments :: 'TSstructure \<Rightarrow> 'history_fragment set"
  "empty_history :: 'TSstructure \<Rightarrow> 'history"
  "empty_history_fragment :: 'TSstructure \<Rightarrow> 'history_fragment"
  "bra_set_history :: 'bra_conf \<Rightarrow> 'history \<Rightarrow> 'bra_conf"
  "extend_history :: 'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
  "join_history_fragments :: 'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
  "bra_get_history :: 'bra_conf \<Rightarrow> 'history"
  for
    TSstructure lin_configurations lin_initial_configurations step_labels lin_step_relation effects lin_marking_condition lin_marked_effect lin_unmarked_effect lin_fixed_schedulers lin_empty_fixed_scheduler lin_fixed_scheduler_extendable lin_scheduler_fragments lin_empty_scheduler_fragment lin_join_scheduler_fragments lin_unfixed_schedulers lin_empty_unfixed_scheduler lin_unfixed_scheduler_right_quotient lin_extend_unfixed_scheduler lin_unfixed_scheduler_extendable lin_schedulers lin_initial_schedulers lin_empty_scheduler lin_get_scheduler lin_join_fixed_scheduler_unfixed_scheduler lin_extend_scheduler lin_get_unfixed_scheduler lin_set_unfixed_scheduler lin_get_fixed_scheduler histories history_fragments empty_history empty_history_fragment lin_set_history extend_history join_history_fragments lin_get_history bra_configurations bra_initial_configurations bra_step_relation bra_marking_condition bra_marked_effect bra_unmarked_effect bra_fixed_schedulers bra_empty_fixed_scheduler bra_fixed_scheduler_extendable bra_get_fixed_scheduler bra_set_history bra_get_history
    +

fixes Lin2BraConf :: "'lin_conf \<Rightarrow> 'bra_conf"

fixes Bra2LinConf :: "'bra_conf \<Rightarrow> 'lin_scheduler \<Rightarrow> 'lin_conf"

fixes Bra2LinStep :: "'bra_conf \<Rightarrow> 'label \<Rightarrow> 'bra_conf \<Rightarrow> 'lin_scheduler_fragment"

fixes Bra2LinFin :: "'TSstructure \<Rightarrow> 'bra_fixed_scheduler \<Rightarrow> 'lin_scheduler"

assumes AX_Lin2BraConf_preserves_steps: "
  TSstructure G
  \<Longrightarrow> c1l \<in> lin_configurations G
  \<Longrightarrow> lin_step_relation G c1l e c2l
  \<Longrightarrow> bra_step_relation G (Lin2BraConf c1l) e (Lin2BraConf c2l)"

assumes AX_Lin2BraConf_preserves_initiality: "
  TSstructure G
  \<Longrightarrow> cl \<in> lin_initial_configurations G
  \<Longrightarrow> Lin2BraConf cl \<in> bra_initial_configurations G"

assumes AX_Lin2BraConf_preserves_configurations: "
  TSstructure G
  \<Longrightarrow> cl \<in> lin_configurations G
  \<Longrightarrow> Lin2BraConf cl \<in> bra_configurations G"

assumes AX_Bra2LinStep_closed: "
  TSstructure G
  \<Longrightarrow> c1B \<in> bra_configurations G
  \<Longrightarrow> bra_step_relation G c1B e c2B
  \<Longrightarrow> Bra2LinStep c1B e c2B \<in> lin_scheduler_fragments G"

assumes AX_Bra2LinFin_closed: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> Bra2LinFin G (bra_get_fixed_scheduler cB) \<in> lin_schedulers G"

assumes AX_Bra2LinConf_schedl_get: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> s1L \<in> lin_schedulers G
  \<Longrightarrow> lin_get_scheduler (Bra2LinConf cB s1L) = s2L
  \<Longrightarrow> s1L = s2L"

assumes AX_Bra2LinFin_creates_proper_extension: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> Bra2LinConf cB (Bra2LinFin G (bra_get_fixed_scheduler cB)) \<in> lin_configurations G"

assumes AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed: "
  TSstructure G
  \<Longrightarrow> c1B \<in> bra_configurations G
  \<Longrightarrow> bra_step_relation G c1B e c2B
  \<Longrightarrow> Bra2LinConf c2B sL \<in> lin_configurations G
  \<Longrightarrow> Bra2LinConf c1B (lin_extend_scheduler (Bra2LinStep c1B e c2B) sL) \<in> lin_configurations G"

assumes AX_lin_step_relation_from_Bra2LinStep: "
  TSstructure G
  \<Longrightarrow> c1B \<in> bra_configurations G
  \<Longrightarrow> bra_step_relation G c1B e c2B
  \<Longrightarrow> Bra2LinConf c2B sL \<in> lin_configurations G
  \<Longrightarrow> lin_step_relation G (Bra2LinConf c1B (lin_extend_scheduler (Bra2LinStep c1B e c2B) sL)) e (Bra2LinConf c2B sL)"

assumes AX_Bra2LinConf_only_modifies_lin_unfixed_scheduler: "
  TSstructure G
  \<Longrightarrow> Bra2LinConf (Lin2BraConf cL) sL \<in> lin_configurations G
  \<Longrightarrow> lin_set_unfixed_scheduler cL (lin_get_unfixed_scheduler (Bra2LinConf (Lin2BraConf cL) sL)) = Bra2LinConf (Lin2BraConf cL) sL"

assumes AX_Bra2LinConf_inj: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> Bra2LinConf cB s1L = Bra2LinConf cB s2L
  \<Longrightarrow> s1L = s2L"

assumes AX_equal_by_fixed_unfixed_and_nonscheduler_part: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> cL \<in> lin_configurations G
  \<Longrightarrow> lin_set_unfixed_scheduler (Bra2LinConf cB (Bra2LinFin G (bra_get_fixed_scheduler cB))) (lin_get_unfixed_scheduler cL) = cL
  \<Longrightarrow> cB = Lin2BraConf cL"

assumes AX_Bra2LinConf_preserves_initiality: "
  TSstructure G
  \<Longrightarrow> sL \<in> lin_schedulers G
  \<Longrightarrow> cB \<in> bra_initial_configurations G
  \<Longrightarrow> Bra2LinConf cB sL \<in> lin_initial_configurations G"

assumes AX_Bra2LinConf_preserves_history: "
  TSstructure G
  \<Longrightarrow> cB \<in> bra_configurations G
  \<Longrightarrow> sL \<in> lin_schedulers G
  \<Longrightarrow> Bra2LinConf cB sL \<in> lin_configurations G
  \<Longrightarrow> lin_get_history (Bra2LinConf cB sL) = bra_get_history cB"

assumes AX_Lin2BraConf_preserves_history: "
  TSstructure G
  \<Longrightarrow> cL \<in> lin_configurations G
  \<Longrightarrow> lin_get_history cL = bra_get_history (Lin2BraConf cL)"

context ATS_Branching_Versus_Linear1 begin

definition Lin2BraDer :: "
  ('label,'lin_conf) derivation
  \<Rightarrow> ('label,'bra_conf) derivation"
  where
    "Lin2BraDer d \<equiv>
  derivation_map d Lin2BraConf"

definition Bra2LinDer' :: "
  'TSstructure
  \<Rightarrow> ('label, 'bra_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> 'lin_scheduler_fragment"
  where
    "Bra2LinDer' G d m n \<equiv>
  foldl
    lin_join_scheduler_fragments
    (lin_empty_scheduler_fragment G)
    (map
      (\<lambda>n.
        case d n of Some (pair e1 c1) \<Rightarrow>
        (case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow>
        Bra2LinStep c1 e2 c2))
      (case m of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq n m'))"

lemma Bra2LinDer_prime_modificiation_for_presentation: "
  (case m of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq n m') = butlast(nat_seq n m)"
  apply(case_tac "n<m")
   prefer 2
   apply(case_tac "n=m")
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq m m"
      and s="[m]"
      in ssubst)
     apply (metis natUptTo_n_n)
    apply(case_tac m)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply (metis lessI nat_seqEmpty)
   apply(case_tac m)
    apply(clarsimp)
    apply(case_tac n)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply (metis butlast.simps(1) nat_seqEmpty zero_less_Suc)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq n nat"
      and s="[]"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="nat_seq n (Suc nat)"
      and s="[]"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq n (Suc nat)"
      and s="nat_seq n nat@[(Suc nat)]"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(case_tac n)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply (metis (no_types, hide_lams) One_nat_def add_Suc_right append.simps(1) append.simps(2) diff_Suc_Suc less_delta_exists minus_nat.diff_0 nat_seq_drop_first nat_seq_last zero_less_Suc)
   apply(rename_tac nat nata)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac nat nata)(*strict*)
    prefer 2
    apply(rule_tac
      m="nata"
      and n="(Suc nat)"
      in nat_seq_last)
    apply(force)
   apply(rename_tac nat nata)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

definition Bra2LinDer :: "
  'TSstructure
  \<Rightarrow> ('label, 'bra_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label, 'lin_conf) derivation"
  where
    "Bra2LinDer G d m \<equiv>
  (\<lambda>n.
    if n > m
    then None
    else
      case d m of
        None \<Rightarrow> None
        | Some (pair em cm) \<Rightarrow>
          (case d n of
            None \<Rightarrow> None
            | Some (pair en cn) \<Rightarrow>
              Some (pair en (Bra2LinConf cn (lin_extend_scheduler (Bra2LinDer' G d m n) (Bra2LinFin G (bra_get_fixed_scheduler cm)))))))"

lemma Lin2BraConf_preserves_steps_lift: "
  TSstructure G
  \<Longrightarrow> GLIN.derivation G d
  \<Longrightarrow> GLIN.belongs G d
  \<Longrightarrow> GBRA.derivation G (Lin2BraDer d)"
  apply(simp add: GBRA.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    prefer 2
    apply(rule GLIN.some_position_has_details_at_0)
    apply(force)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: Lin2BraDer_def derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: Lin2BraDer_def derivation_map_def)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> lin_step_relation G c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in GLIN.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: Lin2BraDer_def derivation_map_def)
  apply(rule AX_Lin2BraConf_preserves_steps)
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(rule GLIN.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(force)
  done

lemma Lin2BraConf_preserves_initiality_lift: "
  TSstructure G
  \<Longrightarrow> GLIN.derivation_initial G d
  \<Longrightarrow> GBRA.derivation_initial G (Lin2BraDer d)"
  apply(subgoal_tac "GLIN.belongs G d")
   prefer 2
   apply(rule GLIN.derivation_initial_belongs)
    apply(force)
   apply(force)
  apply(simp add: GLIN.derivation_initial_def GBRA.derivation_initial_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule GLIN.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac c)(*strict*)
   apply(rule Lin2BraConf_preserves_steps_lift)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: Lin2BraDer_def derivation_map_def)
  apply(rule AX_Lin2BraConf_preserves_initiality)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma Lin2BraConf_preserves_maximum_of_domain: "
  TSstructure G
  \<Longrightarrow> GLIN.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (Lin2BraDer d) n"
  apply(simp add: Lin2BraDer_def derivation_map_def maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma Bra2LinDer_defined0: "
  derivation G d
  \<Longrightarrow> Bra2LinDer G d n x \<noteq> None
  \<Longrightarrow> x\<le>n"
  apply(simp add: Bra2LinDer_def)
  apply (metis option.simps(3) trivNat)
  done

lemma Bra2LinDer_defined1: "
  derivation G d
  \<Longrightarrow> Bra2LinDer G d n x \<noteq> None
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> d x \<noteq> None"
  apply(subgoal_tac "x\<le>n")
   prefer 2
   apply(rule Bra2LinDer_defined0)
    apply(force)
   apply(force)
  apply(simp add: Bra2LinDer_def)
  apply(clarsimp)
  apply(rename_tac y ya)(*strict*)
  apply(case_tac "d x")
   apply(rename_tac y ya)(*strict*)
   apply(clarsimp)
   apply(case_tac ya)
   apply(rename_tac y ya option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya a)(*strict*)
  apply(clarsimp)
  done

lemma Bra2LinDer_defined2: "
  derivation G d
  \<Longrightarrow> d x \<noteq> None
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> Bra2LinDer G d n x \<noteq> None"
  apply(simp add: Bra2LinDer_def)
  apply(clarsimp)
  apply(rename_tac y ya)(*strict*)
  apply(case_tac "d x")
   apply(rename_tac y ya)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya)(*strict*)
  apply(case_tac y)
  apply(rename_tac y ya option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac ya option b)(*strict*)
  apply(case_tac ya)
  apply(rename_tac ya option b optiona ba)(*strict*)
  apply(clarsimp)
  done

lemma Bra2LinDer_preserves_step_labels: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> d m = Some (pair e c)
  \<Longrightarrow> m \<le> n
  \<Longrightarrow> \<exists>c. Bra2LinDer G d n m = Some (pair e c)"
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: Bra2LinDer_def)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma schedE_generated: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> m<n
  \<Longrightarrow> foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G)
           (map (\<lambda>n. case_option undefined
                      (case_derivation_configuration
                        (\<lambda>e1 c1.
                            case_option undefined
                             (case_derivation_configuration
                               (\<lambda>a c2.
                                   case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2))
                             (d (Suc n))))
                      (d n))
             (nat_seq (Suc m) (n - Suc 0)))
          \<in> lin_scheduler_fragments G"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(case_tac "m=n")
   apply(rename_tac n y)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc m) m"
      and s="[]"
      in ssubst)
    apply(rename_tac y)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
   apply(rule GLIN.AX_empty_scheduler_fragment_in_scheduler_fragments)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "m<n")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc m) (n - Suc 0) @ [n] = nat_seq (Suc m) n")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule nat_seq_last)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc m) n"
      and s="nat_seq (Suc m) (n - Suc 0) @ [n]"
      in ssubst)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(rule_tac
      t="map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0) @ [n])"
      and s="map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0))@map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) ([n])"
      in ssubst)
   apply(rename_tac n y)(*strict*)
   apply(rule map_append)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in GBRA.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply(force)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(rule GLIN.AX_join_scheduler_fragments_closed)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(rule AX_Bra2LinStep_closed)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_preserves_configurations: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> d m = Some (pair em cm)
  \<Longrightarrow> m \<le> n
  \<Longrightarrow> Bra2LinDer G d n m = Some (pair em c')
  \<Longrightarrow> c' \<in> lin_configurations G
  \<and> (\<exists>sE \<in> lin_scheduler_fragments G. c' = Bra2LinConf cm (lin_extend_scheduler sE (Bra2LinFin G (bra_get_fixed_scheduler cn))))"
  apply(subgoal_tac "cn \<in> bra_configurations G")
   prefer 2
   apply(rule GBRA.belongs_configurations)
    apply(force)
   apply(force)
  apply(subgoal_tac "cm \<in> bra_configurations G")
   prefer 2
   apply(rule GBRA.belongs_configurations)
    apply(force)
   apply(force)
  apply(induct "n-m" arbitrary: n m en cn em cm c')
   apply(rename_tac n m en cn em cm c')(*strict*)
   apply(clarsimp)
   apply(rename_tac m en cn c')(*strict*)
   apply(simp add: Bra2LinDer_def Bra2LinDer'_def)
   apply(clarsimp)
   apply(rename_tac m en cn)(*strict*)
   apply(rule_tac
      t="case_nat [] (nat_seq m) m"
      and s="[]"
      in ssubst)
    apply(rename_tac m en cn)(*strict*)
    apply(case_tac m)
     apply(rename_tac m en cn)(*strict*)
     apply(clarsimp)
    apply(rename_tac m en cn nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac en cn nat)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac m en cn)(*strict*)
   apply(rule conjI)
    apply(rename_tac m en cn)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="lin_extend_scheduler (lin_empty_scheduler_fragment G) (Bra2LinFin G (bra_get_fixed_scheduler cn))"
      and s="Bra2LinFin G (bra_get_fixed_scheduler cn)"
      in ssubst)
     apply(rename_tac m en cn)(*strict*)
     apply(rule GLIN.AX_extend_scheduler_left_neutral)
      apply(rename_tac m en cn)(*strict*)
      apply(force)
     apply(rename_tac m en cn)(*strict*)
     apply(rule AX_Bra2LinFin_closed)
      apply(rename_tac m en cn)(*strict*)
      apply(force)
     apply(rename_tac m en cn)(*strict*)
     apply(force)
    apply(rename_tac m en cn)(*strict*)
    apply(rule AX_Bra2LinFin_creates_proper_extension)
     apply(rename_tac m en cn)(*strict*)
     apply(force)
    apply(rename_tac m en cn)(*strict*)
    apply(force)
   apply(rename_tac m en cn)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="lin_empty_scheduler_fragment G"
      in bexI)
    apply(rename_tac m en cn)(*strict*)
    apply(force)
   apply(rename_tac m en cn)(*strict*)
   apply(rule GLIN.AX_empty_scheduler_fragment_in_scheduler_fragments)
   apply(force)
  apply(rename_tac x n m en cn em cm c')(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="Suc m"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "m<n")
   apply(rename_tac x n m en cn em cm c')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x n m en cn em cm c')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc m) = Some (pair e c)")
   apply(rename_tac x n m en cn em cm c')(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in GBRA.pre_some_position_is_some_position)
     apply(rename_tac x n m en cn em cm c')(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c')(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c')(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c')(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c' e c)(*strict*)
  apply(subgoal_tac "Bra2LinDer G d n (Suc m) \<noteq> None")
   apply(rename_tac x n m en cn em cm c' e c)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_defined2)
      apply(rename_tac x n m en cn em cm c' e c)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c' e c)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c' e c)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c' e c)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c' e c y)(*strict*)
  apply(case_tac y)
  apply(rename_tac x n m en cn em cm c' e c y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
  apply(erule_tac
      x="en"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="cn"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="b"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
  apply(simp add: Bra2LinDer_def Bra2LinDer'_def)
  apply(subgoal_tac "c \<in> bra_configurations G")
   apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
   prefer 2
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c' e c option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c option sE)(*strict*)
  apply(subgoal_tac "case_nat [] (nat_seq (Suc m)) n = nat_seq (Suc m) (n - 1)")
   apply(rename_tac x n m en cn em cm c option sE)(*strict*)
   prefer 2
   apply(case_tac n)
    apply(rename_tac x n m en cn em cm c option sE)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c option sE nat)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c option sE)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "case_nat [] (nat_seq m) n = nat_seq m (n - 1)")
   apply(rename_tac x n m en cn em cm c option sE)(*strict*)
   prefer 2
   apply(case_tac n)
    apply(rename_tac x n m en cn em cm c option sE)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c option sE nat)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c option sE)(*strict*)
  apply(clarsimp)
  apply(thin_tac "case_nat [] (nat_seq (Suc m)) n = nat_seq (Suc m) (n - Suc 0)")
  apply(thin_tac "case_nat [] (nat_seq m) n = nat_seq m (n - Suc 0)")
  apply(subgoal_tac "foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq (Suc m) (n - Suc 0))) = sE")
   apply(rename_tac x n m en cn em cm c option sE)(*strict*)
   prefer 2
   apply(rule_tac
      s="Bra2LinFin G (bra_get_fixed_scheduler cn)"
      in GLIN.AX_extend_scheduler_left_injective)
       apply(rename_tac x n m en cn em cm c option sE)(*strict*)
       apply(force)
      apply(rename_tac x n m en cn em cm c option sE)(*strict*)
      apply(rule schedE_generated)
          apply(rename_tac x n m en cn em cm c option sE)(*strict*)
          apply(force)
         apply(rename_tac x n m en cn em cm c option sE)(*strict*)
         apply(force)
        apply(rename_tac x n m en cn em cm c option sE)(*strict*)
        apply(force)
       apply(rename_tac x n m en cn em cm c option sE)(*strict*)
       apply(force)
      apply(rename_tac x n m en cn em cm c option sE)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c option sE)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c option sE)(*strict*)
    apply(rule AX_Bra2LinFin_closed)
     apply(rename_tac x n m en cn em cm c option sE)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c option sE)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c option sE)(*strict*)
   apply(rule_tac
      cB="c"
      in AX_Bra2LinConf_inj)
     apply(rename_tac x n m en cn em cm c option sE)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c option sE)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c option sE)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c option sE)(*strict*)
  apply(rule_tac
      A="lin_scheduler_fragments G"
      and a="((foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration(\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq m (n - Suc 0)))))"
      in bexI_conj)
  apply(rename_tac x n m en cn em cm c option sE)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c option)(*strict*)
  apply(subgoal_tac "nat_seq m (n-Suc 0) = [m]@(nat_seq (Suc m) (n-Suc 0))")
   apply(rename_tac x n m en cn em cm c option)(*strict*)
   prefer 2
   apply(rule nat_seq_drop_first2)
   apply(force)
  apply(rename_tac x n m en cn em cm c option)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc m) = Some (pair (Some e) c)")
   apply(rename_tac x n m en cn em cm c option)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc m"
      in GBRA.pre_some_position_is_some_position_prime)
      apply(rename_tac x n m en cn em cm c option)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c option)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c option)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c option)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c option)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(rule_tac
      t="lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (Bra2LinStep cm e c)"
      and s="Bra2LinStep cm e c"
      in ssubst)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule AX_Bra2LinStep_closed)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule GBRA.position_change_due_to_step_relation)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(rule_tac
      t="foldl lin_join_scheduler_fragments (Bra2LinStep cm e c) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0)))"
      and s=" lin_join_scheduler_fragments (Bra2LinStep cm e c) (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0))))"
      in ssubst)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule GLIN.AX_foldl_join_scheduler_fragments)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(rule AX_Bra2LinStep_closed)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(rule GBRA.position_change_due_to_step_relation)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n m en cn em cm c e na)(*strict*)
   apply(subgoal_tac "Suc m\<le>na \<and> na \<le> n-Suc 0")
    apply(rename_tac x n m en cn em cm c e na)(*strict*)
    prefer 2
    apply(rule nat_seq_in_interval)
    apply(force)
   apply(rename_tac x n m en cn em cm c e na)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d na = Some (pair e1 c1) \<and> d (Suc na) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
    apply(rename_tac x n m en cn em cm c e na)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in GBRA.step_detail_before_some_position)
      apply(rename_tac x n m en cn em cm c e na)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e na)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e na)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e na)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
   apply(rule AX_Bra2LinStep_closed)
     apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e na e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(rule_tac
      t="lin_extend_scheduler (lin_join_scheduler_fragments (Bra2LinStep cm e c) (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0))))) (Bra2LinFin G (bra_get_fixed_scheduler cn))"
      and s="lin_extend_scheduler (Bra2LinStep cm e c) (lin_extend_scheduler (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc m) (n - Suc 0)))) (Bra2LinFin G (bra_get_fixed_scheduler cn)))"
      in ssubst)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule GLIN.AX_extend_scheduler_compatible_to_join_scheduler_fragments)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac x n m en cn em cm c e)(*strict*)
       apply(force)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac x n m en cn em cm c e)(*strict*)
       apply(force)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(rule GBRA.position_change_due_to_step_relation)
       apply(rename_tac x n m en cn em cm c e)(*strict*)
       apply(force)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule AX_Bra2LinFin_closed)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(rule conjI)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(rule GBRA.position_change_due_to_step_relation)
      apply(rename_tac x n m en cn em cm c e)(*strict*)
      apply(force)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(rule GLIN.AX_join_scheduler_fragments_closed)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule AX_Bra2LinStep_closed)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(rule GBRA.position_change_due_to_step_relation)
     apply(rename_tac x n m en cn em cm c e)(*strict*)
     apply(force)
    apply(rename_tac x n m en cn em cm c e)(*strict*)
    apply(force)
   apply(rename_tac x n m en cn em cm c e)(*strict*)
   apply(force)
  apply(rename_tac x n m en cn em cm c e)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_preserves_configurations_prime: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> d m = Some (pair em cm)
  \<Longrightarrow> m \<le> n
  \<Longrightarrow> Bra2LinDer G d n m = Some (pair em c')
  \<Longrightarrow> c' \<in> lin_configurations G"
  apply(subgoal_tac "c' \<in> lin_configurations G \<and> (\<exists>sE \<in> lin_scheduler_fragments G. c' = Bra2LinConf cm (lin_extend_scheduler sE (Bra2LinFin G (bra_get_fixed_scheduler cn))))")
   apply(force)
  apply(rule Bra2LinDer_preserves_configurations)
        apply(force)+
  done

lemma Bra2LinDer_preserves_derivation: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> GLIN.derivation G (Bra2LinDer G d n)"
  apply(simp add: GLIN.derivation_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(case_tac i)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac y)(*strict*)
    prefer 2
    apply(rule GBRA.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
   apply(rename_tac y c)(*strict*)
   apply(subgoal_tac "\<exists>c. Bra2LinDer G d n 0 = Some (pair None c)")
    apply(rename_tac y c)(*strict*)
    prefer 2
    apply(rule Bra2LinDer_preserves_step_labels)
        apply(rename_tac y c)(*strict*)
        apply(force)
       apply(rename_tac y c)(*strict*)
       apply(force)
      apply(rename_tac y c)(*strict*)
      apply(force)
     apply(rename_tac y c)(*strict*)
     apply(force)
    apply(rename_tac y c)(*strict*)
    apply(force)
   apply(rename_tac y c)(*strict*)
   apply(clarsimp)
  apply(rename_tac y i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat)(*strict*)
  apply(case_tac "Bra2LinDer G d n (Suc nat)")
   apply(rename_tac y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc nat\<le>n")
   apply(rename_tac y nat a)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_defined0)
    apply(rename_tac y nat a)(*strict*)
    apply(force)
   apply(rename_tac y nat a)(*strict*)
   apply(force)
  apply(rename_tac y nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
   apply(rename_tac y nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in GBRA.step_detail_before_some_position)
     apply(rename_tac y nat a)(*strict*)
     apply(force)
    apply(rename_tac y nat a)(*strict*)
    apply(rule Bra2LinDer_defined1)
      apply(rename_tac y nat a)(*strict*)
      apply(force)
     apply(rename_tac y nat a)(*strict*)
     apply(force)
    apply(rename_tac y nat a)(*strict*)
    apply(force)
   apply(rename_tac y nat a)(*strict*)
   apply(force)
  apply(rename_tac y nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>c. Bra2LinDer G d n (Suc nat) = Some (pair (Some e2) c)")
   apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_preserves_step_labels)
       apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac y nat a e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
  apply(subgoal_tac "Bra2LinDer G d n nat \<noteq> None")
   apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_defined2)
      apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
      apply(force)
     apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
     apply(force)
    apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
    apply(force)
   apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
   apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 c ya)(*strict*)
  apply(case_tac ya)
  apply(rename_tac y nat e1 e2 c1 c2 c ya option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 c option b)(*strict*)
  apply(case_tac y)
  apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
  apply(subgoal_tac "c \<in> lin_configurations G \<and> (\<exists>sE \<in> lin_scheduler_fragments G. c = Bra2LinConf c2 (lin_extend_scheduler sE (Bra2LinFin G (bra_get_fixed_scheduler ba))))")
   apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_preserves_configurations)
         apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
         apply(force)
        apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
        apply(force)
       apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
       apply(force)
      apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
      apply(force)
     apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
  apply(subgoal_tac "b \<in> lin_configurations G \<and> (\<exists>sE \<in> lin_scheduler_fragments G. b = Bra2LinConf c1 (lin_extend_scheduler sE (Bra2LinFin G (bra_get_fixed_scheduler ba))))")
   apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
   prefer 2
   apply(rule_tac
      m="nat"
      in Bra2LinDer_preserves_configurations)
         apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
         apply(force)
        apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
        apply(force)
       apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
       apply(force)
      apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
      apply(force)
     apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
   apply(simp add: Bra2LinDer_def)
  apply(rename_tac y nat e1 e2 c1 c2 c option b optiona ba)(*strict*)
  apply(simp add: Bra2LinDer_def Bra2LinDer'_def)
  apply(clarsimp)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
  apply(subgoal_tac "case_nat [] (nat_seq (Suc nat)) n = nat_seq (Suc nat) (n - 1)")
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
   prefer 2
   apply(case_tac n)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa nata)(*strict*)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "case_nat [] (nat_seq nat) n = nat_seq nat (n - 1)")
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
   prefer 2
   apply(case_tac n)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa nata)(*strict*)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
  apply(clarsimp)
  apply(thin_tac "case_nat [] (nat_seq (Suc nat)) n = nat_seq (Suc nat) (n - Suc 0)")
  apply(thin_tac "case_nat [] (nat_seq nat) n = nat_seq nat (n - Suc 0)")
  apply(subgoal_tac "\<exists>x. Suc x=n-nat")
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
   prefer 2
   apply(rule_tac
      x="n-Suc nat"
      in exI)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa)(*strict*)
  apply(erule exE)+
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
  apply(subgoal_tac "nat_seq nat (n-Suc 0) = [nat]@(nat_seq (Suc nat) (n-Suc 0))")
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   prefer 2
   apply(rule nat_seq_drop_first2)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "sEa = (foldl lin_join_scheduler_fragments (lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (Bra2LinStep c1 e2 c2)) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq (Suc nat) (n - Suc 0))))")
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(subgoal_tac "sE = foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq (Suc nat) (n - Suc 0)))")
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(clarify)
    apply(rule_tac
      t="lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (Bra2LinStep c1 e2 c2)"
      and s="Bra2LinStep c1 e2 c2"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule_tac
      t=" (foldl lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))) "
      and s=" lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) ((foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))))"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_foldl_join_scheduler_fragments)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule AX_Bra2LinStep_closed)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule GBRA.belongs_configurations)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
     apply(subgoal_tac "Suc nat\<le>na \<and> na \<le> n-Suc 0")
      apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
      prefer 2
      apply(rule nat_seq_in_interval)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. d na = Some (pair e1 c1) \<and> d (Suc na) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
      apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in GBRA.step_detail_before_some_position)
        apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba x na)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba x na e1 e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule_tac
      t="lin_extend_scheduler (lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0))))) (Bra2LinFin G (bra_get_fixed_scheduler ba))"
      and s=" lin_extend_scheduler (Bra2LinStep c1 e2 c2) (lin_extend_scheduler (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))) (Bra2LinFin G (bra_get_fixed_scheduler ba)))"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_extend_scheduler_compatible_to_join_scheduler_fragments)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule AX_Bra2LinStep_closed)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(rule GBRA.belongs_configurations)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule GBRA.position_change_due_to_step_relation)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule schedE_generated)
          apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
          apply(force)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule AX_Bra2LinFin_closed)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GBRA.belongs_configurations)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule AX_lin_step_relation_from_Bra2LinStep)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(rule_tac
      s="Bra2LinFin G (bra_get_fixed_scheduler ba)"
      in GLIN.AX_extend_scheduler_left_injective)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule schedE_generated)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule AX_Bra2LinFin_closed)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(rule_tac
      cB="c2"
      in AX_Bra2LinConf_inj)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
  apply(rule_tac
      s="Bra2LinFin G (bra_get_fixed_scheduler ba)"
      in GLIN.AX_extend_scheduler_left_injective)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule_tac
      t="lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (Bra2LinStep c1 e2 c2)"
      and s="Bra2LinStep c1 e2 c2"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule_tac
      t=" (foldl lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))) "
      and s=" lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) ((foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))))"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_foldl_join_scheduler_fragments)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule AX_Bra2LinStep_closed)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule GBRA.belongs_configurations)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
     apply(subgoal_tac "Suc nat\<le>na \<and> na \<le> n-Suc 0")
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
      prefer 2
      apply(rule nat_seq_in_interval)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. d na = Some (pair e1 c1) \<and> d (Suc na) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in GBRA.step_detail_before_some_position)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x na e1 e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule_tac
      t="lin_extend_scheduler (lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0))))) (Bra2LinFin G (bra_get_fixed_scheduler ba))"
      and s=" lin_extend_scheduler (Bra2LinStep c1 e2 c2) (lin_extend_scheduler (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (nat_seq (Suc nat) (n - Suc 0)))) (Bra2LinFin G (bra_get_fixed_scheduler ba)))"
      in ssubst)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GLIN.AX_extend_scheduler_compatible_to_join_scheduler_fragments)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule AX_Bra2LinStep_closed)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(rule GBRA.belongs_configurations)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(rule GBRA.position_change_due_to_step_relation)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule schedE_generated)
          apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
          apply(force)
         apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
         apply(force)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule AX_Bra2LinFin_closed)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule GBRA.belongs_configurations)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule GLIN.AX_join_scheduler_fragments_closed)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(rule AX_Bra2LinStep_closed)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(rule GBRA.belongs_configurations)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(rule schedE_generated)
        apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
        apply(force)
       apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
       apply(force)
      apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
      apply(force)
     apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
     apply(force)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(rule AX_Bra2LinFin_closed)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
  apply(rule_tac
      cB="c1"
      in AX_Bra2LinConf_inj)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
    apply(force)
   apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
   apply(force)
  apply(rename_tac nat e2 c1 c2 option optiona ba sE sEa x)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_preserves_belongs: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> GLIN.belongs G (Bra2LinDer G d n)"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule GBRA.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac y c)(*strict*)
  apply(subgoal_tac "\<exists>c. Bra2LinDer G d n 0 = Some (pair None c)")
   apply(rename_tac y c)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_preserves_step_labels)
       apply(rename_tac y c)(*strict*)
       apply(force)
      apply(rename_tac y c)(*strict*)
      apply(force)
     apply(rename_tac y c)(*strict*)
     apply(force)
    apply(rename_tac y c)(*strict*)
    apply(force)
   apply(rename_tac y c)(*strict*)
   apply(force)
  apply(rename_tac y c)(*strict*)
  apply(clarsimp)
  apply(rename_tac y c ca)(*strict*)
  apply(case_tac y)
  apply(rename_tac y c ca option b)(*strict*)
  apply(subgoal_tac "ca \<in> lin_configurations G \<and> (\<exists>sE \<in> lin_scheduler_fragments G. ca = Bra2LinConf SScm (lin_extend_scheduler sE (Bra2LinFin G (bra_get_fixed_scheduler SScn))))" for SScm SScn)
   apply(rename_tac y c ca option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="0"
      and n="n"
      in Bra2LinDer_preserves_configurations)
         apply(rename_tac y c ca option b)(*strict*)
         apply(force)
        apply(rename_tac y c ca option b)(*strict*)
        apply(force)
       apply(rename_tac y c ca option b)(*strict*)
       apply(force)
      apply(rename_tac y c ca option b)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac y c ca option b)(*strict*)
     apply(force)
    apply(rename_tac y c ca option b)(*strict*)
    apply(force)
   apply(rename_tac y c ca option b)(*strict*)
   apply(force)
  apply(rename_tac y c ca option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c option b sE)(*strict*)
  apply(rule GLIN.derivation_belongs)
     apply(rename_tac c option b sE)(*strict*)
     apply(force)
    apply(rename_tac c option b sE)(*strict*)
    apply(force)
   apply(rename_tac c option b sE)(*strict*)
   apply(force)
  apply(rename_tac c option b sE)(*strict*)
  apply(rule Bra2LinDer_preserves_derivation)
     apply(rename_tac c option b sE)(*strict*)
     apply(force)
    apply(rename_tac c option b sE)(*strict*)
    apply(force)
   apply(rename_tac c option b sE)(*strict*)
   apply(force)
  apply(rename_tac c option b sE)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_preserves_maximum_of_domain: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> maximum_of_domain (Bra2LinDer G d n) n"
  apply(simp add: maximum_of_domain_def)
  apply(simp add: Bra2LinDer_def)
  apply(case_tac "d n")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  done

lemma Lin2BraDer_preserves_belongs: "
  TSstructure G
  \<Longrightarrow> GLIN.derivation G d
  \<Longrightarrow> GLIN.belongs G d
  \<Longrightarrow> GBRA.belongs G (Lin2BraDer d)"
  apply(simp add: GBRA.belongs_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: Lin2BraDer_def derivation_map_def)
  apply(case_tac "d i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(simp add: GLIN.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule AX_Lin2BraConf_preserves_configurations)
   apply(rename_tac i option b)(*strict*)
   apply(force)
  apply(rename_tac i option b)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_prime_pullout_head: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> n<m
  \<Longrightarrow> d m \<noteq> None
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d (Suc n) = Some (pair (Some e2) c2)
  \<Longrightarrow> c1 \<in> bra_configurations G
  \<Longrightarrow> Bra2LinDer' G d m n = lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (Bra2LinDer' G d m (Suc n))"
  apply(subgoal_tac "Bra2LinStep c1 e2 c2 \<in> lin_scheduler_fragments G")
   prefer 2
   apply(rule AX_Bra2LinStep_closed)
     apply(force)
    apply(force)
   apply(rule GBRA.position_change_due_to_step_relation)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="Bra2LinDer' G d m n"
      and s="foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case d n of Some (pair e1 c1) \<Rightarrow> case d (Suc n) of Some (pair (Some e2) c2) \<Rightarrow> Bra2LinStep c1 e2 c2) (case m of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq n m'))"
      in ssubst)
   apply(simp add: Bra2LinDer'_def)
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y)(*strict*)
  apply(rule_tac
      t="nat"
      and s="(Suc nat)-(Suc 0)"
      in ssubst)
   apply(rename_tac nat y)(*strict*)
   apply(force)
  apply(rename_tac nat y)(*strict*)
  apply(rule_tac
      t="nat_seq n ((Suc nat)-Suc 0)"
      and s="[n]@(nat_seq (Suc n) ((Suc nat)-Suc 0))"
      in ssubst)
   apply(rename_tac nat y)(*strict*)
   apply(rule_tac
      x="nat-n"
      in nat_seq_drop_first2)
   apply(arith)
  apply(rename_tac nat y)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y)(*strict*)
  apply(rule_tac
      t="lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (Bra2LinStep c1 e2 c2)"
      and s="Bra2LinStep c1 e2 c2"
      in ssubst)
   apply(rename_tac nat y)(*strict*)
   apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
    apply(rename_tac nat y)(*strict*)
    apply(force)
   apply(rename_tac nat y)(*strict*)
   apply(force)
  apply(rename_tac nat y)(*strict*)
  apply(rule_tac
      t="foldl lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq (Suc n) nat))"
      and s="lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (foldl lin_join_scheduler_fragments (lin_empty_scheduler_fragment G) (map (\<lambda>n. case_option undefined (case_derivation_configuration (\<lambda>e1 c1. case_option undefined (case_derivation_configuration (\<lambda>a c2. case a of Some e2 \<Rightarrow> Bra2LinStep c1 e2 c2)) (d (Suc n)))) (d n)) (nat_seq (Suc n) nat)))"
      in ssubst)
   apply(rename_tac nat y)(*strict*)
   apply(rule GLIN.AX_foldl_join_scheduler_fragments)
     apply(rename_tac nat y)(*strict*)
     apply(force)
    apply(rename_tac nat y)(*strict*)
    apply(force)
   apply(rename_tac nat y)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat y na)(*strict*)
   apply(subgoal_tac "Suc n\<le>na \<and> na \<le> nat")
    apply(rename_tac nat y na)(*strict*)
    prefer 2
    apply(rule nat_seq_in_interval)
    apply(force)
   apply(rename_tac nat y na)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d na = Some (pair e1 c1) \<and> d (Suc na) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
    apply(rename_tac nat y na)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in GBRA.step_detail_before_some_position)
      apply(rename_tac nat y na)(*strict*)
      apply(force)
     apply(rename_tac nat y na)(*strict*)
     apply(force)
    apply(rename_tac nat y na)(*strict*)
    apply(force)
   apply(rename_tac nat y na)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
   apply(rule AX_Bra2LinStep_closed)
     apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac nat y na e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac nat y)(*strict*)
  apply(simp add: Bra2LinDer'_def)
  done

lemma Bra2LinDer_prime_closed: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> Bra2LinDer' G d n m \<in> lin_scheduler_fragments G"
  apply(induct "n-m" arbitrary: n m)
   apply(rename_tac n m)(*strict*)
   apply(clarsimp)
   apply(rename_tac m y)(*strict*)
   apply(simp add: Bra2LinDer'_def)
   apply(rule_tac
      t="case m of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq m m'"
      and s="[]"
      in ssubst)
    apply(rename_tac m y)(*strict*)
    apply(case_tac m)
     apply(rename_tac m y)(*strict*)
     apply(clarsimp)
    apply(rename_tac m y nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac y nat)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac m y)(*strict*)
   apply(rule_tac
      t="nat_seq m m"
      and s="[m]"
      in ssubst)
    apply(rename_tac m y)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac m y)(*strict*)
   apply(clarsimp)
   apply (metis GLIN.AX_empty_scheduler_fragment_in_scheduler_fragments)
  apply(rename_tac x n m)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m y)(*strict*)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="Suc m"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d m = Some (pair e1 c1) \<and> d (Suc m) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
   apply(rename_tac x n m y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in GBRA.step_detail_before_some_position)
     apply(rename_tac x n m y)(*strict*)
     apply(force)
    apply(rename_tac x n m y)(*strict*)
    apply(force)
   apply(rename_tac x n m y)(*strict*)
   apply(force)
  apply(rename_tac x n m y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(case_tac "n=m")
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(rule_tac
      t="Bra2LinDer' G d n m"
      and s="lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (Bra2LinDer' G d n (Suc m))"
      in ssubst)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(rule Bra2LinDer_prime_pullout_head)
          apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
          apply(force)
         apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(rule GLIN.AX_join_scheduler_fragments_closed)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(rule AX_Bra2LinStep_closed)
     apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(rule GBRA.position_change_due_to_step_relation)
     apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m y e1 e2 c1 c2)(*strict*)
  apply(force)
  done

lemma Bra2LinDer_prime_split: "
  TSstructure G
  \<Longrightarrow> y\<le>n
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d (n+x) \<noteq> None
  \<Longrightarrow> Bra2LinDer' G d (n + x) y = lin_join_scheduler_fragments (Bra2LinDer' G d n y) (Bra2LinDer' G d (n + x) n)"
  apply(subgoal_tac "Bra2LinDer' G d (n + x) y \<in> lin_scheduler_fragments G")
   prefer 2
   apply(rule Bra2LinDer_prime_closed)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "Bra2LinDer' G d n y \<in> lin_scheduler_fragments G")
   prefer 2
   apply(rule Bra2LinDer_prime_closed)
       apply(force)
      apply(force)
     apply(force)
    apply (metis GBRA.allPreMaxDomSome GBRA.derivationNoFromNone2_prime maximum_of_domain_def le_iff_add less_iff_Suc_add)
   apply(force)
  apply(subgoal_tac "Bra2LinDer' G d (n + x) n \<in> lin_scheduler_fragments G")
   prefer 2
   apply(rule Bra2LinDer_prime_closed)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(induct "n-y" arbitrary: n y)
   apply(rename_tac n y)(*strict*)
   apply(simp add: Bra2LinDer'_def)
   apply(clarsimp)
   apply(rename_tac y ya)(*strict*)
   apply(case_tac "y+x")
    apply(rename_tac y ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac ya)(*strict*)
    apply (metis GLIN.AX_join_scheduler_fragments_neutral_left)
   apply(rename_tac y ya nat)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
    apply(rename_tac y ya nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac ya nat)(*strict*)
    apply(rule sym)
    apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
     apply(rename_tac ya nat)(*strict*)
     apply(force)
    apply(rename_tac ya nat)(*strict*)
    apply(force)
   apply(rename_tac y ya nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac ya nata)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc nata) nata"
      and s="[]"
      in ssubst)
    apply(rename_tac ya nata)(*strict*)
    apply (metis le_refl less_eq_Suc_le_raw nat_seqEmpty)
   apply(rename_tac ya nata)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule GLIN.AX_join_scheduler_fragments_neutral_right)
    apply(rename_tac ya nata)(*strict*)
    apply(force)
   apply(rename_tac ya nata)(*strict*)
   apply(force)
  apply(rename_tac xa n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa n y ya)(*strict*)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="Suc y"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa n y ya)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa n y ya)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa n y ya)(*strict*)
   apply(rule Bra2LinDer_prime_closed)
       apply(rename_tac xa n y ya)(*strict*)
       apply(force)
      apply(rename_tac xa n y ya)(*strict*)
      apply(force)
     apply(rename_tac xa n y ya)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa n y ya)(*strict*)
   apply(rule Bra2LinDer_prime_closed)
       apply(rename_tac xa n y ya)(*strict*)
       apply(force)
      apply(rename_tac xa n y ya)(*strict*)
      apply(force)
     apply(rename_tac xa n y ya)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya)(*strict*)
    apply (metis GBRA.allPreMaxDomSome GBRA.derivationNoFromNone_prime GBRA.derivationNoFromNone2 maximum_of_domain_def le_iff_add less_iff_Suc_add)
   apply(rename_tac xa n y ya)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d y = Some (pair e1 c1) \<and> d (Suc y) = Some (pair (Some e2) c2) \<and> bra_step_relation G c1 e2 c2")
   apply(rename_tac xa n y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+x"
      in GBRA.step_detail_before_some_position)
     apply(rename_tac xa n y ya)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "Bra2LinDer' G d (n+x) y = lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (Bra2LinDer' G d (n+x) (Suc y))")
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_prime_pullout_head)
          apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
          apply(force)
         apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Bra2LinDer' G d n y = lin_join_scheduler_fragments (Bra2LinStep c1 e2 c2) (Bra2LinDer' G d n (Suc y))")
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule Bra2LinDer_prime_pullout_head)
          apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
          apply(force)
         apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
      apply (metis GBRA.allPreMaxDomSome GBRA.derivationNoFromNone_prime GBRA.derivationNoFromNone2 maximum_of_domain_def le_iff_add less_iff_Suc_add)
     apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(rule GBRA.belongs_configurations)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rule GLIN.AX_join_scheduler_fragments_associative)
     apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply (metis AX_Bra2LinStep_closed GBRA.belongs_configurations)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(rule Bra2LinDer_prime_closed)
       apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply (metis GBRA.allPreMaxDomSome GBRA.derivationNoFromNone_prime GBRA.derivationNoFromNone2 maximum_of_domain_def le_iff_add less_iff_Suc_add)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
  apply(rule Bra2LinDer_prime_closed)
      apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac xa n y ya e1 e2 c1 c2)(*strict*)
  apply(force)
  done

lemma Bra2LinConf_closed_wrt_Bra2LinDer_prime: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G db
  \<Longrightarrow> GBRA.belongs G db
  \<Longrightarrow> db n = Some (pair e1 c1)
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> db m = Some (pair e2 c2)
  \<Longrightarrow> Bra2LinConf c1 (lin_extend_scheduler (Bra2LinDer' G db m n) (Bra2LinFin G (bra_get_fixed_scheduler c2))) \<in> lin_configurations G"
  apply(induct "m-n" arbitrary: n m e1 c1 e2 c2)
   apply(rename_tac n m e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e2 c2)(*strict*)
   apply(simp add: Bra2LinDer'_def)
   apply(rule_tac
      t="case n of 0 \<Rightarrow> [] | Suc m' \<Rightarrow> nat_seq n m'"
      and s="[]"
      in ssubst)
    apply(rename_tac n e2 c2)(*strict*)
    apply(case_tac n)
     apply(rename_tac n e2 c2)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e2 c2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 c2 nat)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac n e2 c2)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="lin_extend_scheduler (lin_empty_scheduler_fragment G) (Bra2LinFin G (bra_get_fixed_scheduler c2))"
      and s="(Bra2LinFin G (bra_get_fixed_scheduler c2))"
      in ssubst)
    apply(rename_tac n e2 c2)(*strict*)
    apply(rule GLIN.AX_extend_scheduler_left_neutral)
     apply(rename_tac n e2 c2)(*strict*)
     apply(force)
    apply(rename_tac n e2 c2)(*strict*)
    apply(rule AX_Bra2LinFin_closed)
     apply(rename_tac n e2 c2)(*strict*)
     apply(force)
    apply(rename_tac n e2 c2)(*strict*)
    apply (metis GBRA.belongs_configurations)
   apply(rename_tac n e2 c2)(*strict*)
   apply (metis AX_Bra2LinFin_creates_proper_extension GBRA.belongs_configurations)
  apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
  apply(erule_tac
      x="Suc n"
      in meta_allE)
  apply(erule_tac
      x="m"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. db (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(erule_tac
      x="Some e"
      in meta_allE)
   apply(erule_tac
      x="c"
      in meta_allE)
   apply(erule_tac
      x="e2"
      in meta_allE)
   apply(erule_tac
      x="c2"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(rule_tac
      t="Bra2LinDer' G db m n"
      and s="lin_join_scheduler_fragments (Bra2LinStep c1 e (c)) (Bra2LinDer' G db m (Suc n))"
      in ssubst)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule Bra2LinDer_prime_pullout_head)
           apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
           apply(force)
          apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
          apply(force)
         apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
         apply(force)
        apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
        apply(force)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(force)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(rule_tac
      t="lin_extend_scheduler (lin_join_scheduler_fragments (Bra2LinStep c1 e (c)) (Bra2LinDer' G db m (Suc n))) (Bra2LinFin G (bra_get_fixed_scheduler c2)) "
      and s=" lin_extend_scheduler (Bra2LinStep c1 e (c)) (lin_extend_scheduler (Bra2LinDer' G db m (Suc n)) (Bra2LinFin G (bra_get_fixed_scheduler c2)))"
      in ssubst)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule GLIN.AX_extend_scheduler_compatible_to_join_scheduler_fragments)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(force)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(rule AX_Bra2LinStep_closed)
        apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
        apply(force)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(rule GBRA.belongs_configurations)
        apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
        apply(force)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(force)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(rule GBRA.position_change_due_to_step_relation)
        apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
        apply(force)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(force)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(rule Bra2LinDer_prime_closed)
         apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
         apply(force)
        apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
        apply(force)
       apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
       apply(force)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule AX_Bra2LinFin_closed)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule GBRA.belongs_configurations)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(rule AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(rule GBRA.belongs_configurations)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(rule GBRA.position_change_due_to_step_relation)
      apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2 e c)(*strict*)
   apply(force)
  apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
  apply(subgoal_tac "\<exists>e c. db (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="m"
      in GBRA.pre_some_position_is_some_position_prime)
      apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m e1 c1 e2 c2)(*strict*)
  apply(simp add: Lin2BraDer_def derivation_map_def)
  done

lemma AX_Bra2LinConf_preserves_history_lift: "
  TSstructure G
  \<Longrightarrow> GBRA.derivation G d
  \<Longrightarrow> GBRA.belongs G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> lin_get_history (the(get_configuration(Bra2LinDer G d n i))) = bra_get_history c"
  apply(simp add: Bra2LinDer_def get_configuration_def)
  apply(case_tac "d n")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(rule AX_Bra2LinConf_preserves_history)
     apply(rename_tac option b)(*strict*)
     apply(force)
    apply(rename_tac option b)(*strict*)
    apply (metis GBRA.belongs_configurations)
   apply(rename_tac option b)(*strict*)
   apply (metis Bra2LinDer_prime_closed AX_Bra2LinFin_closed GBRA.belongs_configurations GBRA.derivationNoFromNone GBRA.derivationNoFromNone2 GLIN.AX_extend_scheduler_closed lessI)
  apply(rename_tac option b)(*strict*)
  apply (metis Bra2LinConf_closed_wrt_Bra2LinDer_prime)
  done

lemma AX_Lin2BraConf_preserves_history_lift: "
  TSstructure G
  \<Longrightarrow> GLIN.derivation G d
  \<Longrightarrow> GLIN.belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> lin_get_history c = bra_get_history (Lin2BraConf c)"
  apply(rule AX_Lin2BraConf_preserves_history)
   apply(force)+
  apply (metis GLIN.belongs_configurations)
  done

end

end

