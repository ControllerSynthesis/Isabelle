section {*L\_ATS\_Simulation\_Configuration\_WeakLRRequired*}
theory
  L_ATS_Simulation_Configuration_WeakLRRequired

imports
  L_ATS_Simulation_Configuration_Weak

begin

locale ATS_Simulation_Configuration_WeakRequired =
  ATS_Simulation_Configuration_Weak
  "TSstructure1 :: 'TSstructure1 \<Rightarrow> bool"
  "configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "initial_configurations1 :: 'TSstructure1 \<Rightarrow> 'conf1 set"
  "step_labels1 :: 'TSstructure1 \<Rightarrow> 'label1 set"
  "step_relation1 :: 'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> bool"
  "effects1 :: 'TSstructure1 \<Rightarrow> 'event1 set"
  "marking_condition1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> bool"
  "marked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "unmarked_effect1 :: 'TSstructure1 \<Rightarrow> ('label1,'conf1)derivation \<Rightarrow> 'event1 set"
  "TSstructure2 :: 'TSstructure2 \<Rightarrow> bool"
  "configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "initial_configurations2 :: 'TSstructure2 \<Rightarrow> 'conf2 set"
  "step_labels2 :: 'TSstructure2 \<Rightarrow> 'label2 set"
  "step_relation2 :: 'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> 'label2 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "effects2 :: 'TSstructure2 \<Rightarrow> 'event2 set"
  "marking_condition2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> bool"
  "marked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "unmarked_effect2 :: 'TSstructure2 \<Rightarrow> ('label2,'conf2)derivation \<Rightarrow> 'event2 set"
  "relation_configuration :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_initial_configuration :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"
  "relation_effect :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"
  "relation_TSstructure :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"
  "relation_initial_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  "relation_step_simulation :: 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool"
  for
    TSstructure1 configurations1 initial_configurations1 step_labels1 step_relation1 effects1 marking_condition1 marked_effect1 unmarked_effect1 TSstructure2 configurations2 initial_configurations2 step_labels2 step_relation2 effects2 marking_condition2 marked_effect2 unmarked_effect2 relation_configuration relation_initial_configuration relation_effect relation_TSstructure relation_initial_simulation relation_step_simulation
    +

fixes relation_labelsLR :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"

fixes marking_configurations1 :: "'TSstructure1 \<Rightarrow> 'conf1 set"

fixes marking_configurations2 :: "'TSstructure2 \<Rightarrow> 'conf2 set"

assumes AX_relation_configuration_compatible_with_marking_configurations: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c1 \<in> marking_configurations1 G1
  \<Longrightarrow> c2 \<in> marking_configurations2 G2"

assumes AX_relation_step_simulation_no_reach_marking_with_empty_simulant: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> n = 0
  \<Longrightarrow> c1' \<notin> marking_configurations1 G1"

assumes AX_relation_step_simulationReach: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> GR.derivation G2 d2
  \<Longrightarrow> GR.belongs G2 d2
  \<Longrightarrow> the(get_configuration(d2 0)) = c2
  \<Longrightarrow> relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> relation_configuration G1 G2 c1' (the(get_configuration(d2 n)))
  \<Longrightarrow> (\<exists>k e2 c2.
        d2 k = Some (pair (Some e2) c2)
        \<and> relation_labelsLR G1 G2 e1 e2)
      \<or> (n=0
         \<and> (\<exists>e2 c2'.
              step_relation2 G2 c2 e2 c2'
              \<and> relation_labelsLR G1 G2 e1 e2))"

context ATS_Simulation_Configuration_WeakRequired begin

lemma ATS_Simulation_Configuration_WeakReach_simulation_derivation_exists_witness_EXTENDED_Required: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 x = Some (pair e1 c1)
  \<Longrightarrow> \<exists>d2 n2 f.
  GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_initial_configuration G1 G2 (the (get_configuration (d1 0))) (the (get_configuration (d2 0)))
  \<and> relation_configuration G1 G2 c1 (the (get_configuration (d2 n2)))
  \<and> simulating_derivation G1 G2 d1 x d2 n2 f
  \<and> (\<forall>i\<le>x. \<forall>e1 c1. d1 i = Some (pair e1 c1) \<longrightarrow> (case e1 of None \<Rightarrow> True | Some e1' \<Rightarrow> \<exists>k\<le>Suc (f i). \<exists>d2'.
  GR.derivation G2 d2'
  \<and> the(get_configuration(d2' 0)) = the(get_configuration(d2 (f i)))
  \<and> (k = Suc (f i) \<longrightarrow> c1 \<notin> marking_configurations1 G1)
  \<and> (case ((get_label (derivation_append d2 d2' (f i) k))) of None \<Rightarrow> False | Some e2' \<Rightarrow> relation_labelsLR G1 G2 e1' e2')))"
  apply(induct x arbitrary: e1 c1)
   apply(rename_tac e1 c1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "c1 \<in> initial_configurations1 G1")
    apply(rename_tac e1 c1)(*strict*)
    prefer 2
    apply(simp add: GL.derivation_initial_def)
   apply(rename_tac e1 c1)(*strict*)
   apply(subgoal_tac "\<exists>d2 n. GR.derivation_initial G2 d2 \<and> relation_initial_configuration G1 G2 c1 (the(get_configuration(d2 0))) \<and> relation_initial_simulation G1 G2 c1 d2 \<and> maximum_of_domain d2 n \<and> relation_configuration G1 G2 c1 (the(get_configuration(d2 n)))")
    apply(rename_tac e1 c1)(*strict*)
    prefer 2
    apply(rule AX_relation_initial_simulation)
     apply(rename_tac e1 c1)(*strict*)
     apply(force)
    apply(rename_tac e1 c1)(*strict*)
    apply(force)
   apply(rename_tac e1 c1)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c1 d2 n)(*strict*)
   apply(rule_tac
      x="d2"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac e1 c1 d2 n)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac e1 c1 d2 n)(*strict*)
   apply(rule_tac
      x="\<lambda>x. n"
      in exI)
   apply(rule conjI)
    apply(rename_tac e1 c1 d2 n)(*strict*)
    apply(simp add: simulating_derivation_def)
    apply(rule conjI)
     apply(rename_tac e1 c1 d2 n)(*strict*)
     apply(simp add: simulating_derivation_I_def)
     apply(rule conjI)
      apply(rename_tac e1 c1 d2 n)(*strict*)
      apply(simp add: get_configuration_def)
      apply (metis GR.derivation_take_id_prime_prime GR.derivation_initial_is_derivation eq_imp_le)
     apply(rename_tac e1 c1 d2 n)(*strict*)
     apply(rule conjI)
      apply(rename_tac e1 c1 d2 n)(*strict*)
      apply(simp add: maximum_of_domain_def derivation_take_def get_configuration_def)
     apply(rename_tac e1 c1 d2 n)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac e1 c1 d2 n)(*strict*)
    apply(rule conjI)
     apply(rename_tac e1 c1 d2 n)(*strict*)
     apply(simp add: simulating_derivation_S_def)
    apply(rename_tac e1 c1 d2 n)(*strict*)
    apply(simp add: simulating_derivation_DEF_def)
    apply(rule conjI)
     apply(rename_tac e1 c1 d2 n)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac e1 c1 d2 n)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac e1 c1 d2 n)(*strict*)
   apply(simp add: GL.derivation_initial_def)
  apply(rename_tac x e1 c1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 x = Some (pair e1 c1) \<and> d1 (Suc x) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac x e1 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc x"
      in GL.step_detail_before_some_position)
     apply(rename_tac x e1 c1)(*strict*)
     apply(rule GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x e1 c1)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac x e1 c1)(*strict*)
   apply(force)
  apply(rename_tac x e1 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c1 e1a e2 c1a)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 xa)(*strict*)
  apply(rename_tac f)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
   prefer 2
   apply(rule GR.some_position_has_details_before_max_dom)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
   apply(force)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
  apply(subgoal_tac "\<exists>d2 n. GR.derivation G2 d2 \<and> GR.belongs G2 d2 \<and> the(get_configuration(d2 0)) = c \<and> relation_step_simulation G1 G2 c1a e2 c1 c d2 \<and> maximum_of_domain d2 n \<and> relation_configuration G1 G2 c1 (the(get_configuration(d2 n)))")
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
   prefer 2
   apply(rule AX_relation_step_simulation)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
    apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
   apply(force)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n)(*strict*)
  apply(rule_tac
      x="derivation_append d2 d2a n2"
      in exI)
  apply(subgoal_tac "\<exists>c. d2a 0 = Some (pair None c)")
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n)(*strict*)
   apply(clarsimp)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation_initial)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
      apply (metis AX_TSstructure_relation_TSstructure2_belongs)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
      apply (metis GR.derivation_initial_is_derivation)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(rule_tac
      x="n2+n"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply (metis concat_has_max_dom)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(simp add: get_configuration_def derivation_append_def)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(rule conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(simp add: get_configuration_def derivation_append_def)
    apply(clarsimp)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(rule_tac
      x="\<lambda>z. if z<Suc x then f z else f x + n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(simp add: simulating_derivation_def)
    apply(rule context_conjI)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
     apply(clarsimp)
     apply(simp only: simulating_derivation_I_def)
     apply(erule exE)+
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
     apply(rule_tac
      x="d2'"
      in exI)
     apply(rule_tac
      x="na"
      in exI)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
      apply (metis (erased, hide_lams) GR.derivation_initial_is_derivation derivation_take_def derivation_take_derivation_append_ignore GR.derivation_take_id_prime GR.derivation_take_preserves_derivation_initial GR.maximum_of_domainUnique maximum_of_domain_def)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
     apply (metis (erased, hide_lams) GR.derivation_append_derivation_take GR.derivation_initial_is_derivation derivation_take_def)
    apply(erule_tac
      x="x"
      in allE)
    apply(erule impE)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(rule propSym,rule context_conjI)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
     apply(simp add: simulating_derivation_DEF_def)
     apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i)(*strict*)
      apply(clarsimp)
      apply(erule_tac
      x="i"
      in allE)
      apply(clarsimp)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
      apply(subgoal_tac "f i \<le> f x")
       apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
       prefer 2
       apply(rule_tac
      d="d2"
      in GR.allPreMaxDomSome_prime)
         apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
        apply(rule GR.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
       apply(force)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i y)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c)(*strict*)
     apply(erule disjE)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c)(*strict*)
      apply(simp add: derivation_append_def maximum_of_domain_def)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c)(*strict*)
     apply(subgoal_tac "get_configuration(derivation_append d2 d2a (f x) (f x + n)) = get_configuration(d2a n)")
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c)(*strict*)
     apply(simp add: derivation_append_def)
     apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 f e d2a c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(simp add: simulating_derivation_S_def)
    apply(erule conjE)+
    apply(rule allI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
    apply(case_tac "i<x")
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
     apply(rule impI)
     apply(thin_tac "i<x")
     apply(erule_tac
      x="i"
      in allE)
     apply(erule impE)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
     apply(rule allI)+
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci')(*strict*)
     apply(rule impI)
     apply(erule_tac
      x="ei"
      in allE)
     apply(erule_tac
      x="ci"
      in allE)
     apply(erule_tac
      x="ei'"
      in allE)
     apply(erule_tac
      x="ci'"
      in allE)
     apply(erule impE)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci')(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci')(*strict*)
     apply(erule exE)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
     apply(rule_tac
      x="d2'"
      in exI)
     apply(subgoal_tac "f i \<le> n2")
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
      prefer 2
      apply(simp add: simulating_derivation_DEF_def)
      apply(clarsimp)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na)(*strict*)
      apply(erule_tac
      x="i"
      and P="\<lambda>i. i \<le> x \<longrightarrow> (\<exists>y. d2 (f i) = Some y) \<and> relation_configuration G1 G2 (the (get_configuration (d1 i))) (the (get_configuration (d2 (f i))))"
      in allE)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na)(*strict*)
      apply(clarsimp)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
      apply(rule_tac
      d="d2"
      in GR.allPreMaxDomSome_prime)
        apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
       apply(rule GR.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
     apply(rule_tac
      t="derivation_append d2 d2a n2 (f i)"
      and s="d2 (f i)"
      in ssubst)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
      apply(simp add: derivation_append_def get_configuration_def)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2')(*strict*)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
     apply(erule conjE)+
     apply(rule_tac
      x="na"
      in exI)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
     apply(subgoal_tac "f i+na \<le> n2")
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
      prefer 2
      apply(simp add: simulating_derivation_DEF_def)
      apply(clarsimp)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na)(*strict*)
      apply(erule_tac
      x="Suc i"
      and P="\<lambda>i. i \<le> x \<longrightarrow> (\<exists>y. d2 (f i) = Some y) \<and> relation_configuration G1 G2 (the (get_configuration (d1 i))) (the (get_configuration (d2 (f i))))"
      in allE)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na)(*strict*)
      apply(clarsimp)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
      apply(rule_tac
      d="d2"
      in GR.allPreMaxDomSome_prime)
        apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
       apply(rule GR.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x c1 e1a e2 c1a d2 f e d2a n c i ei ci ei' ci' na y)(*strict*)
      apply(force)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' d2' na)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' na)(*strict*)
     apply(rule ext)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci' na xa)(*strict*)
     apply(simp add: derivation_take_def derivation_drop_def derivation_append_def)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
    apply(rule conjI)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
    apply(rule impI)
    apply(rule impI)
    apply(subgoal_tac "i=x")
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i)(*strict*)
    apply(thin_tac "\<not> i < x")
    apply(thin_tac "\<not> i < x")
    apply(thin_tac "i < Suc x")
    apply(rule allI)+
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c i ei ci ei' ci')(*strict*)
    apply(rule impI)
    apply(clarsimp)
    apply(rename_tac x d2 n2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(subgoal_tac "f x=n2")
     apply(rename_tac x d2 n2 f e d2a n c ei ci ei' ci')(*strict*)
     prefer 2
     apply(simp add: simulating_derivation_DEF_def)
    apply(rename_tac x d2 n2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(clarsimp)
    apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(rule_tac
      t="(the (get_configuration (derivation_append d2 d2a (f x) (f x))))"
      and s="(the (get_configuration (Some (pair None c))))"
      in ssubst)
     apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
     apply(simp add: get_configuration_def derivation_append_def)
    apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(rule_tac
      t="derivation_take (derivation_drop (derivation_append d2 d2a (f x)) (f x)) n"
      and s="d2a"
      in ssubst)
     apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
     apply(rule ext)
     apply(rename_tac x d2 f e d2a n c ei ci ei' ci' xa)(*strict*)
     apply(simp add: derivation_take_def derivation_drop_def derivation_append_def)
     apply(simp add: get_configuration_def)
     apply(clarsimp)
     apply (metis GR.allPreMaxDomSome_prime)
    apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(rule conjI)
     apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
     apply(force)
    apply(rename_tac x d2 f e d2a n c ei ci ei' ci')(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   prefer 2
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n)(*strict*)
   apply (metis GR.some_position_has_details_at_0)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" in AX_relation_step_simulationReach)
            apply(force)
           prefer 2
           apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
          apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
         apply(force)
        apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
   apply(force)
  apply(rule allI)
  apply(case_tac "i\<le>x")
   apply(erule_tac x="i" in allE)
   apply(clarsimp)
   apply(case_tac e1)
    apply(force)
   apply(clarsimp)
   apply(erule disjE)
    apply(clarsimp)
    apply(subgoal_tac "f i\<le>n2")
     apply(rule_tac x="k" in exI)
     apply(clarsimp)
     apply(rule_tac x="d2'" in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(simp add: get_configuration_def derivation_append_def get_label_def)
     apply(simp add: get_configuration_def derivation_append_def get_label_def)
     apply(rule conjI)
      apply(force)
     apply(force)
    apply(simp add: simulating_derivation_def simulating_derivation_DEF_def)
    apply(clarsimp)
    apply (metis GR.allPreMaxDomSome_prime GR.derivation_initial_is_derivation option.distinct(1))
   apply(clarsimp)
   apply(subgoal_tac "f i\<le>n2")
    apply(case_tac "k\<le>f i")
     apply(rule_tac x="k" in exI)
     apply(clarsimp)
     apply(rule_tac x="d2'" in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(simp add: get_configuration_def derivation_append_def get_label_def)
     apply(simp add: get_configuration_def derivation_append_def get_label_def)
    apply(rule_tac x="k" in exI)
    apply(clarsimp)
    apply(rule_tac x="d2'" in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(simp add: get_configuration_def derivation_append_def get_label_def)
    apply(simp add: get_configuration_def derivation_append_def get_label_def)
   apply(simp add: simulating_derivation_def simulating_derivation_DEF_def)
   apply(clarsimp)
   apply (metis GR.allPreMaxDomSome_prime GR.derivation_initial_is_derivation option.distinct(1))
  apply(rule impI)
  apply(subgoal_tac "i=Suc x")
   prefer 2
   apply(force)
  apply(erule_tac x="x" in allE)
  apply(clarsimp)
  apply(subgoal_tac "n2= f x")
   prefer 2
   apply(simp add: simulating_derivation_def simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule disjE)
   apply(clarsimp)
   apply(rule_tac
      x="f x+k"
      in exI)
   apply(rule conjI)
    apply(clarsimp)
    apply(subgoal_tac "k\<le>n")
     apply(force)
    apply (metis (full_types) GR.allPreMaxDomSome_prime option.distinct(1))
   apply(rule_tac
      x="der1 (the (get_configuration (derivation_append d2 d2a (f x) ((f x) + n))))"
      in exI)
   apply(rule conjI)
    apply(rule GR.der1_is_derivation)
   apply(rule conjI)
    apply(simp add: der1_def get_configuration_def get_label_def derivation_append_def)
   apply(simp add: get_configuration_def get_label_def derivation_append_def)
   apply(case_tac k)
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac n)
    apply(clarsimp)
    apply(subgoal_tac "False")
     apply(force)
    apply (metis GR.derivationNoFromNone_prime GR.noSomeAfterMaxDom less_Suc_eq_0_disj)
   apply(clarsimp)
   apply(subgoal_tac "Suc nat\<le>Suc nata")
    prefer 2
    apply(rule GR.allPreMaxDomSome_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      x="Suc(f x)"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="der2 (the (get_configuration (Some (pair e (the (get_configuration (Some (pair None c))))))))
        e2a xa"
      in exI)
  apply(rule conjI)
   apply(rule GR.der2_is_derivation)
   apply(force)
  apply(rule conjI)
   apply(simp add: get_configuration_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: derivation_append_def get_label_def der2_def)
  apply(rule_tac ?d2.0="d2a" in AX_relation_step_simulation_no_reach_marking_with_empty_simulant)
        apply(force)
       prefer 3
       apply(force)
      apply(force)
     apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
    apply(simp add: get_configuration_def)
   apply(force)
  apply(force)
  done

theorem ATS_Simulation_Configuration_WeakRequired_exists_ALT: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GR.is_forward_deterministic_accessible G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 n1 = Some (pair (Some e1) c1)
  \<Longrightarrow> n1\<le>n1'
  \<Longrightarrow> d1 n1'= Some (pair e1' c1')
  \<Longrightarrow> c1' \<in> marking_configurations1 G1
  \<Longrightarrow> \<exists>d2 n2' n2 e2 c2 e2' c2'.
  GR.derivation_initial G2 d2
  \<and> d2 n2 = Some (pair (Some e2) c2)
  \<and> relation_labelsLR G1 G2 e1 e2
  \<and> n2 \<le> n2'
  \<and> d2 n2' = Some (pair e2' c2')
  \<and> relation_configuration G1 G2 c1' c2'"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac x="n1'" in ATS_Simulation_Configuration_WeakReach_simulation_derivation_exists_witness_EXTENDED_Required)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="d2" in exI)
  apply(clarsimp)
  apply(rule_tac x="f n1'" in exI)
  apply(subgoal_tac "n2=f n1'")
   prefer 2
   apply(simp add: simulating_derivation_def simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(subgoal_tac "(\<exists>e2' c2'. d2 (f n1') = Some (pair e2' c2') \<and> relation_configuration G1 G2 c1' c2')")
   prefer 2
   apply(simp add: simulating_derivation_def simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac x="n1" in allE)
   apply(erule_tac x="n1'" in allE)
   apply(clarsimp)
   apply(case_tac  y)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(case_tac "n1=n1'")
   apply(clarsimp)
   apply(erule_tac x="n1'" in allE)
   apply(case_tac "n1'")
    apply(clarsimp)
    apply (metis GL.derivation_initial_is_derivation GL.initialNotEdgeSome_prime)
   apply(rename_tac n1)
   apply(clarsimp)
   apply(case_tac "k\<le>(f (Suc n1))")
    apply(rule_tac x="k" in exI)
    apply(clarsimp)
    apply(simp add: derivation_append_def get_label_def)
    apply(case_tac "d2 k")
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac a)
    apply(clarsimp)
    apply(case_tac x1)
     apply(clarsimp)
    apply(clarsimp)
   apply(subgoal_tac "k = Suc(f (Suc n1))")
    prefer 2
    apply(force)
   apply(clarsimp)
  apply(case_tac "f n1 = f n1'")
   apply(erule_tac x="n1'" in allE')
   apply(erule_tac x="n1" in allE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="n1'-Suc 0" and
      m="n1'"
      in GL.step_detail_before_some_position)
      apply(rule GL.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "ka \<le>  (f n1)")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac "k\<le>(f (n1'))")
    apply(rule_tac x="k" in exI)
    apply(clarsimp)
    apply(simp add: derivation_append_def get_label_def)
    apply(case_tac "d2 k")
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac a)
    apply(clarsimp)
    apply(case_tac x1)
     apply(clarsimp)
    apply(clarsimp)
   apply(subgoal_tac "k = Suc (f n1')")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac n1')
    apply(force)
   apply(clarsimp)
   apply(rename_tac n1')
   apply(subgoal_tac "f n1 \<le> f n1'")
    prefer 2
    apply(rule_tac f="f" in mono_all)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "f n1' \<le> f (Suc n1')")
    prefer 2
    apply(rule_tac f="f" in mono_all)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "f n1' < f (Suc n1')")
    apply(force)
   apply(simp add: simulating_derivation_def simulating_derivation_S_def)
   apply(clarsimp)
   apply(erule_tac x="n1'" in allE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule AX_relation_step_simulation_no_reach_marking_with_empty_simulant)
          apply(force)
         prefer 4
         apply(force)
        apply(simp add: get_configuration_def)
        apply(simp add: simulating_derivation_DEF_def)
        apply(erule_tac x="n1'" in allE)
        apply(clarsimp)
        apply(simp add: get_configuration_def)
       apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
      apply(simp add: get_configuration_def)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "f n1 \<le> f (n1')")
   prefer 2
   apply(rule_tac f="f" in mono_all)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "f n1 < f n1'")
   prefer 2
   apply(force)
  apply(subgoal_tac "n1 < n1'")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(erule_tac x="n1" in allE)
  apply(clarsimp)
  apply(rule_tac x="k" in exI)
  apply(case_tac "k\<le>f n1")
   apply(simp add: get_label_def derivation_append_def)
   apply(case_tac "d2 k")
    apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(case_tac x1)
    apply(clarsimp)
   apply(clarsimp)
  apply(subgoal_tac "k= Suc(f n1)")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(case_tac "get_label (derivation_append d2 d2' (f n1) (Suc (f n1)))")
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "derivation_append d2 d2' (f n1) (Suc (f n1)) = d2' (Suc 0)")
   prefer 2
   apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(thin_tac "derivation_append d2 d2' (f n1) (Suc (f n1)) = d2' (Suc 0)")
  apply(case_tac "d2' (Suc 0)")
   apply(force)
  apply(clarsimp)
  apply(case_tac aa)
  apply(clarsimp)
  apply(rename_tac e c)
  apply(subgoal_tac "c2' \<in> SSX" for SSX)
   prefer 2
   apply(rule_tac ?c1.0="c1'" in AX_relation_configuration_compatible_with_marking_configurations)
     apply(force)
    apply(simp add: get_configuration_def)
   apply(force)
  apply(subgoal_tac "d2' (Suc 0) = d2 (f n1 + Suc 0)")
   apply(force)
  apply(rule_tac t="d2' (Suc 0)" and s="derivation_append d2 d2' (f n1) (f n1+Suc 0)" in ssubst)
   apply(simp add: derivation_append_def)
  apply(rule_tac ?d2.0="d2" and ?n1.0="f n1+Suc 0" and ?n2.0="f n1'" in GR.is_forward_edge_deterministic_accessible__derivation__conincide)
         apply(force)
        apply(rule GR.derivation_append_preserves_derivation_initial)
          apply (metis AX_TSstructure_relation_TSstructure2_belongs)
         apply(force)
        apply(rule GR.derivation_append_preserves_derivation)
          apply (metis GR.derivation_initial_is_derivation)
         apply(force)
        apply(simp add: get_configuration_def)
        apply(case_tac "d2 (f n1)")
         apply(clarsimp)
         apply(simp add: simulating_derivation_DEF_def simulating_derivation_def)
         apply(clarsimp)
         apply(erule_tac x="n1" in allE)
         apply(force)
        apply(clarsimp)
        apply(case_tac a)
        apply(clarsimp)
        apply(case_tac "d2' 0")
         apply(clarsimp)
         apply (metis GR.initialNotNone_prime)
        apply(clarsimp)
        apply(case_tac a)
        apply(clarsimp)
        apply(case_tac x1a)
         apply(clarsimp)
        apply(clarsimp)
        apply (metis GR.initialNotEdgeSome_prime)
       apply(force)
      apply(simp add: derivation_append_def)
     apply(simp add: derivation_append_def)
    apply(force)
   apply(force)
  apply(force)
  done

end

end
