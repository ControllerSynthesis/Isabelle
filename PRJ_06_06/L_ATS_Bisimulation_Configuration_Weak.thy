section {*L\_ATS\_Bisimulation\_Configuration\_Weak*}
theory
  L_ATS_Bisimulation_Configuration_Weak

imports
  PRJ_06_06__PRE

begin

(*
translation of
  Nonblockingness_branching
using
  bisimulation relation on configuration where steps are mimicked weakly.
*)

locale ATS_Bisimulation_Configuration_Weak =
  GL:
  ATS_Language
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  +
  GR:
  ATS_Language
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2

context ATS_Bisimulation_Configuration_Weak
begin

definition bisimulation_initial :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('conf1 \<times> 'conf2) set
  \<Rightarrow> bool"
  where
    "bisimulation_initial G1 G2 R \<equiv>
  \<forall>i2 \<in> initial_configurations2 G2.
    \<exists>i1 \<in> initial_configurations1 G1.
      (i1,i2) \<in> R"

definition Nonblockingness_branching_bisimulation_step :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('conf1 \<times> 'conf2) set
  \<Rightarrow> 'conf1 set
  \<Rightarrow> 'conf2 set
  \<Rightarrow> bool"
  where
    "Nonblockingness_branching_bisimulation_step G1 G2 R A1 A2 \<equiv>
  (\<forall>(s1,s2)\<in> R.
  (\<forall>e2 s2'.
  step_relation2 G2 s2 e2 s2'
  \<longrightarrow> (\<exists>s1' d n.
  GL.derivation G1 d
  \<and> maximum_of_domain d n
  \<and> (get_configuration (d 0)) = Some s1
  \<and> (get_configuration (d n)) = Some s1'
  \<and> (s1',s2') \<in> R
  ))
  \<and>
  (\<forall>e1 s1'.
  step_relation1 G1 s1 e1 s1'
  \<longrightarrow> (\<exists>s2' d n.
  GR.derivation G2 d
  \<and> maximum_of_domain d n
  \<and> (get_configuration (d 0)) = Some s2
  \<and> (get_configuration (d n)) = Some s2'
  \<and> (s1',s2') \<in> R
  \<and> (s1' \<in> A1 \<longrightarrow> s2' \<in> A2)
  )))"

definition bisimulation_preserves_steps1 :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('conf1 \<times> 'conf2) set
  \<Rightarrow> bool"
  where
    "bisimulation_preserves_steps1 G1 G2 R \<equiv>
  \<forall>(s1,s2) \<in> R.
    \<forall>e2 s2'.
      step_relation2 G2 s2 e2 s2'
      \<longrightarrow> (\<exists>s1' d n.
            GL.derivation G1 d
            \<and> maximum_of_domain d n
            \<and> (get_configuration (d 0)) = Some s1
            \<and> (get_configuration (d n)) = Some s1'
            \<and> (s1',s2') \<in> R)"

definition bisimulation_preserves_steps2 :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('conf1 \<times> 'conf2) set
  \<Rightarrow> bool"
  where
    "bisimulation_preserves_steps2 G1 G2 R \<equiv>
  \<forall>(s1,s2) \<in> R.
    \<forall>e1 s1'.
      step_relation1 G1 s1 e1 s1'
      \<longrightarrow> (\<exists>s2' d n.
           GR.derivation G2 d
           \<and> maximum_of_domain d n
           \<and> (get_configuration (d 0)) = Some s2
           \<and> (get_configuration (d n)) = Some s2'
           \<and> (s1',s2') \<in> R)"

definition bisimulation_preserves_marking_condition :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('conf1 \<times> 'conf2) set
  \<Rightarrow> bool"
  where
    "bisimulation_preserves_marking_condition G1 G2 R \<equiv>
  \<forall>(s1,s2) \<in> R.
    (\<exists>dh n. derivation_append_fit dh (der1 s1) n
      \<and> GL.derivation G1 dh
      \<and> maximum_of_domain dh n
      \<and> marking_condition1 G1 dh)
    \<longrightarrow> (\<forall>dh n.
          derivation_append_fit dh (der1 s2) n
          \<and> maximum_of_domain dh n
          \<and> GR.derivation G2 dh
          \<longrightarrow> marking_condition2 G2 dh)"

lemma Nonblockingness_branching_bisimulation_makes_derivation_left: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> bisimulation_initial GL GR R
  \<Longrightarrow> Nonblockingness_branching_bisimulation_step GL GR R A1 A2
  \<Longrightarrow> GR.derivation_initial GR d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> get_configuration (d n) = Some cR
  \<Longrightarrow> \<exists>d' n' cL.
  GL.derivation_initial GL d'
  \<and> maximum_of_domain d' n'
  \<and> (get_configuration (d' n') = Some cL)
  \<and> (cL,cR) \<in> R"
  apply(subgoal_tac "\<exists>cR. d 0 = Some (pair None cR) \<and> cR \<in> initial_configurations2 GR")
   prefer 2
   apply(simp add: GR.derivation_initial_def)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac cRa)(*strict*)
  apply(rename_tac cR0)
  apply(rename_tac cR0)(*strict*)
  apply(simp add: bisimulation_initial_def)
  apply(erule_tac
      x="cR0"
      in ballE)
   apply(rename_tac cR0)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac cR0)(*strict*)
  apply(clarsimp)
  apply(rename_tac cR0 i1)(*strict*)
  apply(rename_tac cL0)
  apply(rename_tac cR0 cL0)(*strict*)
  apply(induct n arbitrary: cR d)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="der1 cL0"
      in exI)
   apply(rule conjI)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(simp add: GL.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac cR0 cL0 cR d)(*strict*)
     apply(rule GL.der1_is_derivation)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="cL0"
      in exI)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac n cR0 cL0 cR d)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="cR0"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="cL0"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n cR0 cL0 cR d)(*strict*)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n cR0 cL0 cR d a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d option)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> step_relation2 GR c1 e2 c2")
   apply(rename_tac n cR0 cL0 cR d option)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in GR.step_detail_before_some_position)
     apply(rename_tac n cR0 cL0 cR d option)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac n cR0 cL0 cR d option)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d option)(*strict*)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d option)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(rule GR.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
  apply(simp add: Nonblockingness_branching_bisimulation_step_def)
  apply(erule_tac
      x="(cL, c1)"
      in ballE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
   apply(clarsimp)
   apply(thin_tac "\<forall>e1 s1'. step_relation1 GL cL e1 s1' \<longrightarrow> (\<exists>s2' d. ATS.derivation step_relation2 GR d \<and> (\<exists>n. maximum_of_domain d n \<and> get_configuration (d 0) = Some c1 \<and> get_configuration (d n) = Some s2' \<and> (s1', s2') \<in> R \<and> (s1' \<in> A1 \<longrightarrow> s2' \<in> A2)))")
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
   apply(erule_tac
      x="e2"
      in allE)
   apply(erule_tac
      x="cR"
      in allE)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
   apply(rule_tac
      x="derivation_append d' da n'"
      in exI)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "\<exists>c. da 0 = Some (pair None c)")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
    prefer 2
    apply(rule GL.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
   apply(clarsimp)
   apply(case_tac "d' n'")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option)(*strict*)
   apply(case_tac "da na")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule GL.derivation_append_preserves_derivation_initial)
      apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
      apply(force)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule GL.derivation_append_preserves_derivation)
      apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
      apply(simp add: GL.derivation_initial_def)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule_tac
      x="n'+na"
      in exI)
   apply(rule conjI)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule_tac
      x="if na=0 then cL else s1'"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
  apply(force)
  done

lemma Nonblockingness_branching_bisimulation_makes_derivation_left2: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> bisimulation_initial GL GR R
  \<Longrightarrow> bisimulation_preserves_steps1 GL GR R
  \<Longrightarrow> GR.derivation_initial GR d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> get_configuration (d n) = Some cR
  \<Longrightarrow> \<exists>d' n' cL.
  GL.derivation_initial GL d'
  \<and> maximum_of_domain d' n'
  \<and> (get_configuration (d' n') = Some cL)
  \<and> (cL,cR) \<in> R"
  apply(subgoal_tac "\<exists>cR. d 0 = Some (pair None cR) \<and> cR \<in> initial_configurations2 GR")
   prefer 2
   apply(simp add: GR.derivation_initial_def)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac cRa)(*strict*)
  apply(rename_tac cR0)
  apply(rename_tac cR0)(*strict*)
  apply(simp add: bisimulation_initial_def)
  apply(erule_tac
      x="cR0"
      in ballE)
   apply(rename_tac cR0)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac cR0)(*strict*)
  apply(clarsimp)
  apply(rename_tac cR0 i1)(*strict*)
  apply(rename_tac cL0)
  apply(rename_tac cR0 cL0)(*strict*)
  apply(induct n arbitrary: cR d)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="der1 cL0"
      in exI)
   apply(rule conjI)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(simp add: GL.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac cR0 cL0 cR d)(*strict*)
     apply(rule GL.der1_is_derivation)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac cR0 cL0 cR d)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac cR0 cL0 cR d)(*strict*)
   apply(rule_tac
      x="cL0"
      in exI)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac n cR0 cL0 cR d)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="cR0"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="cL0"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n cR0 cL0 cR d)(*strict*)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n cR0 cL0 cR d a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d option)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> step_relation2 GR c1 e2 c2")
   apply(rename_tac n cR0 cL0 cR d option)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in GR.step_detail_before_some_position)
     apply(rename_tac n cR0 cL0 cR d option)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac n cR0 cL0 cR d option)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d option)(*strict*)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d option)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(rule GR.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
  apply(simp add: bisimulation_preserves_steps1_def)
  apply(erule_tac
      x="(cL, c1)"
      in ballE)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      in allE)
   apply(erule_tac
      x="cR"
      in allE)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
   apply(rule_tac
      x="derivation_append d' da n'"
      in exI)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "\<exists>c. da 0 = Some (pair None c)")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
    prefer 2
    apply(rule GL.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
   apply(clarsimp)
   apply(case_tac "d' n'")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option)(*strict*)
   apply(case_tac "da na")
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule GL.derivation_append_preserves_derivation_initial)
      apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
      apply(force)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule GL.derivation_append_preserves_derivation)
      apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
      apply(simp add: GL.derivation_initial_def)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(clarsimp)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule_tac
      x="n'+na"
      in exI)
   apply(rule conjI)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
     apply(force)
    apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
    apply(force)
   apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL s1' da na option optiona)(*strict*)
   apply(rule_tac
      x="if na=0 then cL else s1'"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
  apply(rename_tac n cR0 cL0 cR d e1 e2 c1 d' n' cL)(*strict*)
  apply(force)
  done

lemma Nonblockingness_branching_bisimulation_makes_derivation_right: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> bisimulation_preserves_steps2 GL GR R
  \<Longrightarrow> GL.derivation GL d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> get_configuration (d 0) = Some c0L
  \<Longrightarrow> get_configuration (d n) = Some cnL
  \<Longrightarrow> (c0L,c0R) \<in> R
  \<Longrightarrow> c0R \<in> configurations2 GR
  \<Longrightarrow> \<exists>d' n' cnR.
  GR.derivation GR d'
  \<and> GR.belongs GR d'
  \<and> maximum_of_domain d' n'
  \<and> (get_configuration (d' 0) = Some c0R)
  \<and> (get_configuration (d' n') = Some cnR)
  \<and> (cnL,cnR) \<in> R"
  apply(induct n arbitrary: d cnL)
   apply(rename_tac d cnL)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule_tac
      x="der1 c0R"
      in exI)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule GR.der1_is_derivation)
   apply(rename_tac d)(*strict*)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule GR.der1_belongs)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac d)(*strict*)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac n d cnL)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> step_relation1 GL c1 e2 c2")
   apply(rename_tac n d cnL)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in GL.step_detail_before_some_position)
     apply(rename_tac n d cnL)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac n d cnL)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d (Suc n)")
     apply(rename_tac n d cnL)(*strict*)
     apply(force)
    apply(rename_tac n d cnL a)(*strict*)
    apply(force)
   apply(rename_tac n d cnL)(*strict*)
   apply(force)
  apply(rename_tac n d cnL)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
   apply(rule GL.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_take_def get_configuration_def)
  apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_take_def get_configuration_def)
  apply(rename_tac n d cnL e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR)(*strict*)
  apply(simp add: bisimulation_preserves_steps2_def)
  apply(erule_tac
      x="(c1, cnR)"
      in ballE)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
  apply(rule_tac
      x="derivation_append d' da n'"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
     apply(force)
    apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
    apply(force)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d' n'")
    apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option)(*strict*)
   apply(case_tac "da 0")
    apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option a optiona conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option optiona)(*strict*)
   apply(case_tac "optiona")
    apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option optiona)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option optiona a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option a)(*strict*)
   apply(simp add: GR.derivation_def)
   apply(erule_tac
      x="0"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d' 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d' i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d' i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation2 GR i'2 i1v i2)))"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(rule GR.derivation_append_preserves_belongs)
     apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
     apply(force)
    apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
    apply(force)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
  apply(rule_tac
      x="n'+na"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(rule concat_has_max_dom)
    apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
    apply(force)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d 0")
   apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na)(*strict*)
   apply(force)
  apply(rename_tac n d cnL e1 e2 c1 c2 d' n' cnR s2' da na a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na a)(*strict*)
  apply(case_tac a)
  apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option)(*strict*)
  apply(rule_tac
      x="s2'"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac n d cnL e1 e2 c1 d' n' cnR s2' da na option)(*strict*)
  apply(simp add: get_configuration_def derivation_append_def)
  apply(clarsimp)
  done

theorem preserve_Nonblockingness: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> bisimulation_initial GL GR R
  \<Longrightarrow> bisimulation_preserves_steps1 GL GR R
  \<Longrightarrow> bisimulation_preserves_steps2 GL GR R
  \<Longrightarrow> bisimulation_preserves_marking_condition GL GR R
  \<Longrightarrow> GL.Nonblockingness_branching GL
  \<Longrightarrow> GR.Nonblockingness_branching GR"
  apply(simp add: GR.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in GR.some_position_has_details_before_max_dom)
     apply(rename_tac dh n)(*strict*)
     apply(simp add: GR.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(blast)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c)(*strict*)
  apply(subgoal_tac "\<exists>d' n' cL. GL.derivation_initial GL d' \<and> maximum_of_domain d' n' \<and> (get_configuration (d' n') = Some cL) \<and> (cL,c) \<in> R")
   apply(rename_tac dh n e c)(*strict*)
   prefer 2
   apply(rule Nonblockingness_branching_bisimulation_makes_derivation_left2)
         apply(rename_tac dh n e c)(*strict*)
         apply(force)
        apply(rename_tac dh n e c)(*strict*)
        apply(force)
       apply(rename_tac dh n e c)(*strict*)
       apply(force)
      apply(rename_tac dh n e c)(*strict*)
      apply(force)
     apply(rename_tac dh n e c)(*strict*)
     apply(force)
    apply(rename_tac dh n e c)(*strict*)
    apply(force)
   apply(rename_tac dh n e c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac dh n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL)(*strict*)
  apply(simp add: GL.Nonblockingness_branching_def)
  apply(erule_tac
      x="d'"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="n'"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc x= Some (pair e c)")
   apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
   prefer 2
   apply(rule_tac
      m="x"
      in GL.some_position_has_details_before_max_dom)
     apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
   apply(blast)
  apply(rename_tac dh n e c d' n' cL dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac dh n e c d' n' cL dc x ea ca)(*strict*)
   prefer 2
   apply(simp add: GL.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(case_tac "dc 0")
    apply(rename_tac dh n e c d' n' cL dc x ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e c d' n' cL dc x ea ca a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e c d' n' cL dc x ea ca option b)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca option b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
  apply(subgoal_tac "\<exists>d' n' cR. GR.derivation GR d' \<and> GR.belongs GR d' \<and> maximum_of_domain d' n' \<and> (get_configuration (d' 0) = Some c) \<and> (get_configuration (d' n') = Some cR) \<and> (ca,cR) \<in> R")
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
   prefer 2
   apply(rule Nonblockingness_branching_bisimulation_makes_derivation_right)
           apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
           apply(force)
          apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
          apply(force)
         apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
         apply(force)
        apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
        apply(force)
       apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
       apply(force)
      apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
    apply(subgoal_tac "cb=cL")
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
    apply(simp add: get_configuration_def derivation_append_fit_def)
    apply(case_tac "d' n'")
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
   apply(rule_tac GR.belongs_configurations)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
    apply(rule GR.derivation_initial_belongs)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(rule_tac
      x="derivation_take d'TSstructure1 n'TSstructure1"
      in exI)
  apply(rule conjI)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule GR.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule GR.derivation_take_preserves_belongs)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule_tac
      x="n'TSstructure1"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: get_configuration_def)
   apply(case_tac "d'TSstructure1 n'TSstructure1")
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(simp add: derivation_append_fit_def derivation_take_def get_configuration_def)
   apply(simp add: GR.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(case_tac "d'TSstructure1 0")
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(simp add: bisimulation_preserves_marking_condition_def)
  apply(erule_tac
      x="(ca, cR)"
      in ballE)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule_tac
      x="derivation_append d' dc n'"
      in exI)
   apply(rule_tac
      x="n'+x"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_append_def der1_def)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc ca d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(case_tac "d' n'")
     apply(rename_tac dh n e c d' n' cL dc ca d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc ca d'TSstructure1 n'TSstructure1 cR a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n e c d' n' cL dc ca d'TSstructure1 n'TSstructure1 cR a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(rule GL.derivation_append_preserves_derivation)
      apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
      apply(simp add: GL.derivation_initial_def)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d' n'")
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option)(*strict*)
    apply(simp add: derivation_append_fit_def)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(erule_tac
      x="derivation_append dh (derivation_take d'TSstructure1 n'TSstructure1) n"
      in allE)
  apply(subgoal_tac "derivation_append (derivation_append dh (derivation_take d'TSstructure1 n'TSstructure1) n) (der1 cR) (n + n'TSstructure1) = derivation_append dh (derivation_take d'TSstructure1 n'TSstructure1) n")
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   prefer 2
   apply(rule ext)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(simp add: der1_def derivation_take_def)
   apply(clarsimp)
   apply(case_tac "dc (xa-n')")
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa a)(*strict*)
   apply(rule_tac
      m="xa-n'"
      in GL.no_some_beyond_maximum_of_domain)
      apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa a)(*strict*)
      apply(force)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa a)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa a)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR xa a)(*strict*)
   apply(force)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(erule impE)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule_tac
      x="n+n'TSstructure1"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_append_def der1_def)
    apply(simp add: get_configuration_def derivation_take_def)
    apply(case_tac "d'TSstructure1 n'TSstructure1")
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
    apply(clarsimp)
    apply(case_tac n'TSstructure1)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 cR a nat)(*strict*)
    apply(case_tac a)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 cR a nat option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(simp add: get_configuration_def)
    apply(case_tac "d'TSstructure1 n'TSstructure1")
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(force)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(rule GR.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
   apply(simp add: get_configuration_def derivation_take_def)
   apply(case_tac "d'TSstructure1 0")
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR option a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR a)(*strict*)
   apply(simp add: GR.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac dh n e c d' n' cL dc x ea ca cb d'TSstructure1 n'TSstructure1 cR)(*strict*)
  apply(force)
  done

end

end
