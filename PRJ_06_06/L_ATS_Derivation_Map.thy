section {*L\_ATS\_Derivation\_Map*}
theory
  L_ATS_Derivation_Map

imports
  PRJ_06_06__PRE

begin

locale ATS_Derivation_Map =
  GL:
  ATS
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  +
  GR:
  ATS
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2
    +
  fixes TSstructure_rel :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"

context ATS_Derivation_Map begin

definition der_map :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2)
  \<Rightarrow> ('TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2)
  \<Rightarrow> ('label1, 'conf1)derivation
  \<Rightarrow> ('label2, 'conf2)derivation"
  where
    "der_map G1 G2 fe fc d =
  (\<lambda>n. case d n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow>
  Some (pair (case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some(fe G1 G2 e')) (fc G1 G2 c)))"

definition der_map_preserves_steps :: "
  ('TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2)
  \<Rightarrow> ('TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2)
  \<Rightarrow> bool"
  where
    "der_map_preserves_steps fe fc =
  (\<forall>G1 G2 c1 e c2.
  TSstructure1 G1
  \<longrightarrow> TSstructure_rel G1 G2
  \<longrightarrow> TSstructure2 G2
  \<longrightarrow> step_relation1 G1 c1 e c2
  \<longrightarrow> step_relation2 G2 (fc G1 G2 c1) (fe G1 G2 e) (fc G1 G2 c2))"

lemma der_map_preserves_derivation: "
  TSstructure1 G1
  \<Longrightarrow> TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure2 G2
  \<Longrightarrow> GL.derivation G1 d
  \<Longrightarrow> der_map_preserves_steps fe fc
  \<Longrightarrow> GR.derivation G2 (der_map G1 G2 fe fc d)"
  apply(simp (no_asm) add: GR.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: GL.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(simp add: der_map_def)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac option b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "der_map G1 G2 fe fc d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat a)(*strict*)
   apply(simp add: der_map_def)
  apply(rename_tac nat a aa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat a aa)(*strict*)
   prefer 2
   apply(rule_tac
      n="nat"
      and m="Suc nat"
      in GL.step_detail_before_some_position)
     apply(rename_tac nat a aa)(*strict*)
     apply(force)
    apply(rename_tac nat a aa)(*strict*)
    apply(force)
   apply(rename_tac nat a aa)(*strict*)
   apply(force)
  apply(rename_tac nat a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a e1 e2 c1 c2)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a e1 e2 c1 c2 option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 option b)(*strict*)
  apply(simp add: der_map_def)
  apply(case_tac option)
   apply(rename_tac nat e1 e2 c1 c2 option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: der_map_preserves_steps_def)
  done

definition der_map_preserves_configurations_initial :: "
  ('TSstructure1\<Rightarrow>'TSstructure2\<Rightarrow>'conf1\<Rightarrow>'conf2)
  \<Rightarrow>bool"
  where
    "der_map_preserves_configurations_initial fc =
  (\<forall>G1 G2 c.
  TSstructure1 G1
  \<longrightarrow> TSstructure_rel G1 G2
  \<longrightarrow> TSstructure2 G2
  \<longrightarrow> c \<in> initial_configurations1 G1
  \<longrightarrow> (fc G1 G2 c) \<in> initial_configurations2 G2)"

theorem der_map_preserves_derivation_initial: "
  TSstructure1 G1
  \<Longrightarrow> TSstructure_rel G1 G2
  \<Longrightarrow> TSstructure2 G2
  \<Longrightarrow> GL.derivation_initial G1 d
  \<Longrightarrow> der_map_preserves_steps fe fc
  \<Longrightarrow> der_map_preserves_configurations_initial fc
  \<Longrightarrow> GR.derivation_initial G2 (der_map G1 G2 fe fc d)"
  apply(rule GR.derivation_initialI)
   apply(rule der_map_preserves_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(rule GL.derivation_initial_is_derivation)
    apply(force)
   apply(force)
  apply(simp add: der_map_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d 0")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
  apply(rename_tac c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: GL.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: der_map_preserves_configurations_initial_def)
  apply(rename_tac option b a)(*strict*)
  apply(force)
  done

end

end

