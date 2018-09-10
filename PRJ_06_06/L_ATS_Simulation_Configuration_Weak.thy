section {*L\_ATS\_Simulation\_Configuration\_Weak*}
theory
  L_ATS_Simulation_Configuration_Weak

imports
  PRJ_06_06__PRE

begin

(*
translation of
  is_forward_edge_deterministic_accessible
  get_accessible_configurations
  Nonblockingness_branching
  unmarked language
  marked language
using
  simulation relation on configuration where steps are mimicked weakly.
*)

locale ATS_Simulation_Configuration_Weak =
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
    +

fixes relation_configuration :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"

fixes relation_initial_configuration :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"

fixes relation_effect :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'event1 \<Rightarrow> 'event2 \<Rightarrow> bool"

fixes relation_TSstructure :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"

fixes relation_initial_simulation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"

fixes relation_step_simulation :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'label1 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> ('label2, 'conf2) derivation \<Rightarrow> bool"

assumes AX_TSstructure_relation_TSstructure1_belongs: "
  relation_TSstructure G1 G2
  \<Longrightarrow> TSstructure1 G1"

assumes AX_TSstructure_relation_TSstructure2_belongs: "
  relation_TSstructure G1 G2
  \<Longrightarrow> TSstructure2 G2"

assumes AX_relation_initial_simulation: "
  relation_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> \<exists>d2 n.
  GR.derivation_initial G2 d2
  \<and> relation_initial_configuration G1 G2 c1 (the(get_configuration(d2 0)))
  \<and> relation_initial_simulation G1 G2 c1 d2
  \<and> maximum_of_domain d2 n
  \<and> relation_configuration G1 G2 c1 (the(get_configuration(d2 n)))"

assumes AX_relation_step_simulation: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> \<exists>d2 n.
  GR.derivation G2 d2
  \<and> GR.belongs G2 d2
  \<and> the(get_configuration(d2 0)) = c2
  \<and> relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<and> maximum_of_domain d2 n
  \<and> relation_configuration G1 G2 c1' (the(get_configuration(d2 n)))"

context ATS_Simulation_Configuration_Weak begin

definition simulating_derivation_I :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1, 'conf1) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label2, 'conf2) derivation
  \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat)
  \<Rightarrow> bool"
  where
    "simulating_derivation_I G1 G2 d1 n1 d2 n2 f \<equiv>
  \<exists>d2' n.
  relation_initial_simulation G1 G2 (the (get_configuration (d1 0))) d2'
  \<and> maximum_of_domain d2' n
  \<and> derivation_take d2 n = d2'
  \<and> f 0 = n
  \<and> d2 n \<noteq> None"

definition simulating_derivation_DEF :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1, 'conf1) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label2, 'conf2) derivation
  \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat)
  \<Rightarrow> bool"
  where
    "simulating_derivation_DEF G1 G2 d1 n1 d2 n2 f \<equiv>
  (\<forall>i \<le> n1.
    d2 (f i) \<noteq> None
    \<and> relation_configuration G1 G2
        (the (get_configuration(d1 i)))
        (the (get_configuration(d2 (f i)))))
  \<and> f n1 = n2"

definition simulating_derivation_S :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1, 'conf1) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label2, 'conf2) derivation
  \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat)
  \<Rightarrow> bool"
  where
    "simulating_derivation_S G1 G2 d1 n1 d2 n2 f \<equiv>
  \<forall>i < n1. \<forall>ei ci ei' ci'.
    d1 i = Some (pair ei ci)
    \<and> d1 (Suc i) = Some (pair (Some ei') ci')
    \<longrightarrow> (\<exists>d2' n.
    relation_step_simulation G1 G2 ci ei' ci'
      (the (get_configuration (d2(f i)))) d2'
    \<and> maximum_of_domain d2' n
    \<and> f (Suc i) = f i + n
    \<and> derivation_take (derivation_drop d2 (f i)) n = d2')"

definition simulating_derivation :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1, 'conf1) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label2, 'conf2) derivation
  \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat)
  \<Rightarrow> bool"
  where
    "simulating_derivation G1 G2 d1 n1 d2 n2 f \<equiv>
  simulating_derivation_I G1 G2 d1 n1 d2 n2 f
  \<and> simulating_derivation_S G1 G2 d1 n1 d2 n2 f
  \<and> simulating_derivation_DEF G1 G2 d1 n1 d2 n2 f"

lemma mono_one: "
  simulating_derivation G1 G2 d1 n1 d2 n2 f
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 n1\<noteq>None
  \<Longrightarrow> Suc x \<le> n1
  \<Longrightarrow> f x \<le> f (Suc x)"
  apply(simp add: simulating_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: simulating_derivation_S_def)
  apply(erule_tac
      x="x"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 x = Some (pair e1 c1) \<and> d1 (Suc x) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n1"
      in GL.step_detail_before_some_position)
     apply(rename_tac y)(*strict*)
     apply(rule GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac y)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  done

lemma mono_all: "
  simulating_derivation G1 G2 d1 n1 d2 n2 f
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 n1\<noteq>None
  \<Longrightarrow> x \<le> y
  \<Longrightarrow> y \<le> n1
  \<Longrightarrow> f x \<le> f y"
  apply(induct "y-x" arbitrary: x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa x)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x ya)(*strict*)
  apply(case_tac y)
   apply(rename_tac xa x ya)(*strict*)
   apply(force)
  apply(rename_tac xa x ya nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x y nat)(*strict*)
  apply(erule_tac
      x="Suc x"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x y nat)(*strict*)
   apply(force)
  apply(rename_tac xa x y nat)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x y nat)(*strict*)
   apply(force)
  apply(rename_tac xa x y nat)(*strict*)
  apply(rule_tac
      j="f(Suc x)"
      in le_trans)
   apply(rename_tac xa x y nat)(*strict*)
   apply(rule mono_one)
      apply(rename_tac xa x y nat)(*strict*)
      apply(force)
     apply(rename_tac xa x y nat)(*strict*)
     apply(force)
    apply(rename_tac xa x y nat)(*strict*)
    apply(force)
   apply(rename_tac xa x y nat)(*strict*)
   apply(force)
  apply(rename_tac xa x y nat)(*strict*)
  apply(force)
  done

lemma ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 x = Some (pair e1 c1)
  \<Longrightarrow> \<exists>d2 n2 f.
  GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_initial_configuration G1 G2 (the (get_configuration (d1 0))) (the (get_configuration (d2 0)))
  \<and> relation_configuration G1 G2 c1 (the (get_configuration (d2 n2)))
  \<and> simulating_derivation G1 G2 d1 x d2 n2 f"
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
    defer
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n)(*strict*)
    apply (metis GR.some_position_has_details_at_0)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
   apply(rule GR.some_position_has_details_before_max_dom)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f)(*strict*)
   apply(force)
  apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c)(*strict*)
  apply(rule_tac
      x="\<lambda>z. if z<Suc x then f z else f x + n"
      in exI)
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
    apply (metis GR.allPreMaxDomSome_prime derivation_take_derivation_append_ignore GR.derivation_initial_is_derivation)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
   apply(rule conjI)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2 f e d2a n c d2' na)(*strict*)
   apply (metis GR.allPreMaxDomSome_prime derivation_take_conf_end derivation_take_derivation_append_ignore GR.derivation_initial_is_derivation)
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
      and P="\<lambda>i. i \<le> x \<longrightarrow> (\<exists>y. d2 (f (i)) = Some y) \<and> relation_configuration G1 G2 (the (get_configuration (d1 (i)))) (the (get_configuration (d2 (f (i)))))"
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
  done

lemma ATS_Simulation_Configuration_Weak_simulation_derivation_exists: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> d1 x = Some (pair e1 c1)
  \<Longrightarrow> \<exists>d2 n2.
  GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_initial_configuration G1 G2 (the (get_configuration (d1 0))) (the (get_configuration (d2 0)))
  \<and> relation_configuration G1 G2 c1 (the (get_configuration (d2 n2)))"
  apply(metis ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness)
  done

lemma ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation G1 d1
  \<Longrightarrow> GL.belongs G1 d1
  \<Longrightarrow> d1 0 = Some (pair e0 c0)
  \<Longrightarrow> relation_configuration G1 G2 c0 c0'
  \<Longrightarrow> c0' \<in> configurations2 G2
  \<Longrightarrow> d1 x = Some (pair e1 c1)
  \<Longrightarrow> \<exists>d2 n2.
  GR.derivation G2 d2
  \<and> GR.belongs G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> the (get_configuration (d2 0)) = c0'
  \<and> relation_configuration G1 G2 (the (get_configuration (d1 0))) (the (get_configuration (d2 0)))
  \<and> relation_configuration G1 G2 c1 (the (get_configuration (d2 n2)))"
  apply(induct x arbitrary: e1 c1)
   apply(rename_tac e1 c1)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 c0'"
      in exI)
   apply(rule conjI)
    apply(rule GR.der1_is_derivation)
   apply(rule conjI)
    apply(rule GR.der1_belongs)
    apply(metis)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rule der1_maximum_of_domain)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac x e1 c1)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 x = Some (pair e1 c1) \<and> d1 (Suc x) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac x e1 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc x"
      in GL.step_detail_before_some_position)
     apply(rename_tac x e1 c1)(*strict*)
     apply(force)
    apply(rename_tac x e1 c1)(*strict*)
    apply(force)
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
  apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
    apply(clarsimp)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
    apply(simp add: get_configuration_def der1_def)
    apply(subgoal_tac "\<exists>d2 n. GR.derivation G2 d2 \<and> GR.belongs G2 d2 \<and> the(get_configuration(d2 0)) = ca \<and> relation_step_simulation G1 G2 c1a e2 c1 ca d2 \<and> maximum_of_domain d2 n \<and> relation_configuration G1 G2 c1 (the(get_configuration(d2 n)))")
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
     prefer 2
     apply(rule AX_relation_step_simulation)
        apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
      apply (metis GL.belongs_step_labels)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
     apply(force)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 e c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n)(*strict*)
    apply(rule_tac
      x="derivation_append d2 d2a n2"
      in exI)
    apply(subgoal_tac "\<exists>c. d2a 0 = Some (pair None c)")
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
     apply(rule context_conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply(rule GR.derivation_append_preserves_derivation)
        apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
        apply(force)
       apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
       apply(force)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
     apply(rule conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply(rule GR.derivation_append_preserves_belongs)
        apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
        apply (metis AX_TSstructure_relation_TSstructure2_belongs)
       apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
       apply(force)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
     apply(rule_tac
      x="n2+n"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply (metis concat_has_max_dom)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
     apply(rule context_conjI)
      apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
      apply(simp add: get_configuration_def derivation_append_def)
     apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n ca)(*strict*)
     apply(simp add: get_configuration_def derivation_append_def)
     apply(clarsimp)
    apply(rename_tac x c1 e1a e2 c1a d2 n2 e c d2a n)(*strict*)
    apply (metis GR.some_position_has_details_at_0)
   apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
   apply (metis GR.some_position_has_details_at_0)
  apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
  apply(rule GR.some_position_has_details_before_max_dom)
    apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
    apply(force)
   apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
   apply(force)
  apply(rename_tac x c1 e1a e2 c1a d2 n2)(*strict*)
  apply(force)
  done

lemma simulating_derivation_exist_initial: "
  GR.derivation_initial G2 d2
  \<Longrightarrow> relation_initial_simulation G1 G2 c1 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> relation_configuration G1 G2 c1 (the (get_configuration (d2 n)))
  \<Longrightarrow> d2 0 = Some (pair None c2)
  \<Longrightarrow> simulating_derivation G1 G2 (derivation_append (der1 c1) (der1 c1) 0) 0 (derivation_append (der1 (the (get_configuration (d2 0)))) d2 0) (0 + n) (\<lambda>x. n)"
  apply(rule_tac
      t="derivation_append (der1 c1) (der1 c1) 0"
      and s="der1 c1"
      in ssubst)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(simp add: derivation_append_def der1_def)
  apply(rule_tac
      t="derivation_append (der1 (the (get_configuration (d2 0)))) d2 0"
      and s="d2"
      in ssubst)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def der1_def)
  apply(clarsimp)
  apply(simp add: simulating_derivation_def)
  apply(rule conjI)
   apply(simp add: simulating_derivation_I_def)
   apply(simp add: der1_def)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      t="derivation_take d2 n"
      and s="d2"
      in ssubst)
    apply(rule ext)
    apply(rename_tac x)(*strict*)
    apply(simp add: derivation_take_def)
    apply(clarsimp)
    apply(rule sym)
    apply(rule GR.none_position_after_max_dom)
      apply(rename_tac x)(*strict*)
      apply(rule GR.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(simp add: maximum_of_domain_def)
  apply(rule conjI)
   apply(simp add: simulating_derivation_S_def)
  apply(simp add: simulating_derivation_DEF_def)
  apply(rule conjI)
   apply(simp add: maximum_of_domain_def)
  apply(simp add: get_configuration_def der1_def)
  done

lemma simulating_derivation_exist_step: "
  ATS.derivation_initial initial_configurations1 step_relation1 G1 d
  \<Longrightarrow> maximum_of_domain d (Suc x)
  \<Longrightarrow> d x = Some (pair e0 c1)
  \<Longrightarrow> d (Suc x) = Some (pair (Some e1) c1')
  \<Longrightarrow> ATS.derivation_initial initial_configurations2 step_relation2 G2 deri2
  \<Longrightarrow> maximum_of_domain deri2 deri2n
  \<Longrightarrow> simulating_derivation G1 G2 d x deri2 deri2n f
  \<Longrightarrow> deri2 deri2n = Some (pair e (the (get_configuration (Some (pair None c2)))))
  \<Longrightarrow> ATS.derivation step_relation2 G2 d2
  \<Longrightarrow> relation_step_simulation G1 G2 c1 e1 c1' (the (get_configuration (Some (pair None c2)))) d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> relation_configuration G1 G2 c1' (the (get_configuration (d2 n)))
  \<Longrightarrow> d2 0 = Some (pair None c2)
  \<Longrightarrow> simulating_derivation G1 G2 (derivation_append (derivation_take d x) (der2 c1 e1 c1') x) (Suc x) (derivation_append deri2 d2 deri2n) (deri2n + n) (\<lambda>a. if a \<le> x then f a else f x + n)"
  apply(rule_tac
      s="d"
      and t="(derivation_append (derivation_take d x) (der2 c1 e1 c1') x)"
      in ssubst)
   apply(rule ext)
   apply(rename_tac xa)(*strict*)
   apply(simp add: derivation_append_def derivation_take_def der2_def)
   apply(case_tac "xa-x")
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac xa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa)(*strict*)
    apply(subgoal_tac "Suc x=xa")
     apply(rename_tac xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa nata)(*strict*)
   apply(subgoal_tac "xa=x+Suc(Suc nata)")
    apply(rename_tac xa nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac nata)(*strict*)
   apply(rule sym)
   apply(rule GL.none_position_after_max_dom)
     apply(rename_tac nata)(*strict*)
     apply(rule GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac nata)(*strict*)
    apply(force)
   apply(rename_tac nata)(*strict*)
   apply(force)
  apply(simp add: simulating_derivation_def)
  apply(rule conjI)
   apply(simp add: simulating_derivation_I_def)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(subgoal_tac "f 0 \<le> deri2n")
    apply(rename_tac y)(*strict*)
    prefer 2
    apply (metis GR.derivation_append_derivation_take derivation_take_twice_prime GR.derivation_initial_is_derivation GR.maximum_of_domainUnique less_or_eq_imp_le nat_le_linear)
   apply(rename_tac y)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append deri2 d2 deri2n) (f 0)"
      and s="derivation_take deri2 (f 0)"
      in ssubst)
    apply(rename_tac y)(*strict*)
    apply(rule ext)
    apply(rename_tac y xa)(*strict*)
    apply(simp add: derivation_take_def)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(simp add: derivation_append_def)
  apply(rule conjI)
   apply(simp add: simulating_derivation_S_def)
   apply(rule allI)
   apply(rename_tac i)(*strict*)
   apply(rule conjI)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(rename_tac i ei ci ei' ci')(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(rename_tac i ei ci ei' ci' na)(*strict*)
    apply(simp add: simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(subgoal_tac "f i \<le> f x")
     apply(rename_tac i ei ci ei' ci' na)(*strict*)
     prefer 2
     apply(erule_tac
      x="i"
      in allE)
     apply(clarsimp)
     apply(rename_tac i ei ci ei' ci' na y)(*strict*)
     apply(case_tac y)
     apply(rename_tac i ei ci ei' ci' na y option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
     apply(rule_tac
      M="G2"
      and d="deri2"
      in GR.allPreMaxDomSome_prime)
       apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
       apply(rule GR.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
      apply(force)
     apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
     apply(force)
    apply(rename_tac i ei ci ei' ci' na)(*strict*)
    apply(subgoal_tac "\<exists>y. deri2 (f i) = Some y")
     apply(rename_tac i ei ci ei' ci' na)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i ei ci ei' ci' na)(*strict*)
    apply(erule exE)
    apply(rename_tac i ei ci ei' ci' na y)(*strict*)
    apply(rule_tac
      t="(derivation_append deri2 d2 (f x) (f i))"
      and s="Some y"
      in ssubst)
     apply(rename_tac i ei ci ei' ci' na y)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac i ei ci ei' ci' na y)(*strict*)
    apply(case_tac y)
    apply(rename_tac i ei ci ei' ci' na y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
    apply(erule_tac
      x="Suc i"
      in allE)
    apply(erule impE)
     apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
     apply(force)
    apply(rename_tac i ei ci ei' ci' na option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac i ei ci ei' ci' na option b y)(*strict*)
    apply(case_tac y)
    apply(rename_tac i ei ci ei' ci' na option b y optiona ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba)(*strict*)
    apply(rule_tac
      t="derivation_take (derivation_drop (derivation_append deri2 d2 (f x)) (f i)) na"
      and s="derivation_take (derivation_drop deri2 (f i)) na"
      in ssubst)
     apply(rename_tac i ei ci ei' ci' na option b optiona ba)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba)(*strict*)
    apply(rule ext)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
    apply(simp add: derivation_take_def)
    apply(clarsimp)
    apply(simp add: derivation_drop_def)
    apply(rule conjI)
     apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac i ei ci ei' ci' na option b optiona ba)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(subgoal_tac "f (Suc i) \<le> f x")
     apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
     apply(force)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
    apply(rule_tac
      M="G2"
      and d="deri2"
      in GR.allPreMaxDomSome_prime)
      apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
      apply(rule GR.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
     apply(force)
    apply(rename_tac i ei ci ei' ci' na option b optiona ba xa)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i ei ci ei' ci')(*strict*)
   apply(subgoal_tac "x=i")
    apply(rename_tac i ei ci ei' ci')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i ei ci ei' ci')(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="get_configuration(derivation_append deri2 d2 deri2n (f x))"
      and s="get_configuration(Some (pair None c2))"
      in ssubst)
    apply(simp add: simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
    apply(simp add: get_configuration_def)
   apply(rule_tac
      t="derivation_take (derivation_drop (derivation_append deri2 d2 deri2n) (f x)) n"
      and s="d2"
      in ssubst)
    prefer 2
    apply(force)
   apply(rule ext)
   apply(rename_tac xa)(*strict*)
   apply(simp add: simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(rule conjI)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_drop_def)
    apply(rule conjI)
     apply(rename_tac xa)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def)
     apply(simp add: get_configuration_def)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply (metis GR.allPreMaxDomSome_prime)
  apply(simp add: simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac i y)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac i y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i option b)(*strict*)
   apply(subgoal_tac "f i \<le> f x")
    apply(rename_tac i option b)(*strict*)
    apply(force)
   apply(rename_tac i option b)(*strict*)
   apply(rule_tac
      M="G2"
      and d="deri2"
      in GR.allPreMaxDomSome_prime)
     apply(rename_tac i option b)(*strict*)
     apply(rule GR.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i option b)(*strict*)
    apply(force)
   apply(rename_tac i option b)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=Suc x")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(rule_tac
      t="get_configuration (derivation_append deri2 d2 (f x) (f x + n))"
      and s="get_configuration(d2 n)"
      in ssubst)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(simp add: get_configuration_def)
  done

definition relation_step_simulation_preservation :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1,'conf1)derivation
  \<Rightarrow> ('label2,'conf2)derivation
  \<Rightarrow> bool"
  where
    "relation_step_simulation_preservation G1 G2 d1' d2' \<equiv>
  \<exists>c1 e1 c1' c2 d1 n1 d2 n2 ds n f.
  relation_TSstructure G1 G2
  \<and> relation_configuration G1 G2 c1 c2
  \<and> e1 \<in> step_labels1 G1
  \<and> step_relation1 G1 c1 e1 c1'
  \<and> relation_step_simulation G1 G2 c1 e1 c1' c2 ds
  \<and> maximum_of_domain ds n
  \<and> GL.derivation_initial G1 d1
  \<and> maximum_of_domain d1 n1
  \<and> GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_initial_configuration G1 G2
        (the (get_configuration (d1 0)))
        (the (get_configuration (d2 0)))
  \<and> derivation_append_fit d1 (der2 c1 e1 c1') n1
  \<and> derivation_append_fit d2 ds n2
  \<and> d1' = derivation_append d1 (der2 c1 e1 c1') n1
  \<and> d2' = derivation_append d2 ds n2
  \<and> simulating_derivation G1 G2 d1' (Suc n1) d2' (n2 + n) f"

lemma relation_step_simulation_preservation_PROVE: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> relation_step_simulation G1 G2 c1 e1 c1' c2 ds
  \<Longrightarrow> maximum_of_domain ds n
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> GR.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> relation_initial_configuration G1 G2
        (the(get_configuration(d1 0)))
        (the(get_configuration(d2 0)))
  \<Longrightarrow> derivation_append_fit d1 (der2 c1 e1 c1') n1
  \<Longrightarrow> derivation_append_fit d2 ds n2
  \<Longrightarrow> d1' = derivation_append d1 (der2 c1 e1 c1') n1
  \<Longrightarrow> d2' = derivation_append d2 ds n2
  \<Longrightarrow> simulating_derivation G1 G2 d1' (Suc n1) d2' (n2+n) f
  \<Longrightarrow> relation_step_simulation_preservation G1 G2 d1' d2'"
  apply(simp (no_asm) only: relation_step_simulation_preservation_def)
  apply(rule_tac
      x="c1"
      in exI)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="c1'"
      in exI)
  apply(rule_tac
      x="c2"
      in exI)
  apply(rule_tac
      x="d1"
      in exI)
  apply(rule_tac
      x="n1"
      in exI)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="n2"
      in exI)
  apply(rule_tac
      x="ds"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="f"
      in exI)
  apply(force)
  done

lemma relation_step_simulation_preservation_PROVE2: "
  (\<And>c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f.
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> e1 \<in> step_labels1 G1
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> GL.derivation_initial G1 deri1
  \<Longrightarrow> maximum_of_domain deri1 deri1n
  \<Longrightarrow> GR.derivation_initial G2 deri2
  \<Longrightarrow> maximum_of_domain deri2 deri2n
  \<Longrightarrow> relation_initial_configuration G1 G2 (the(get_configuration(deri1 0))) (the(get_configuration(deri2 0)))
  \<Longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n
  \<Longrightarrow> derivation_append_fit deri2 d2 deri2n
  \<Longrightarrow> simulating_derivation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n+n) f
  \<Longrightarrow> d1' = derivation_append deri1 (der2 c1 e1 c1') deri1n
  \<Longrightarrow> d2' = derivation_append deri2 d2 deri2n
  \<Longrightarrow> Q G1 G2 d1' d2')
  \<Longrightarrow> relation_step_simulation_preservation G1 G2 d1' d2'
  \<Longrightarrow> Q G1 G2 d1' d2'"
  apply(unfold relation_step_simulation_preservation_def)
  apply(erule exE)+
  apply(rename_tac c1 e1 c1' c2 d1 n1 d2 n2 ds n f)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1'"
      in meta_allE)
  apply(erule_tac
      x="ds"
      in meta_allE)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="d1"
      in meta_allE)
  apply(erule_tac
      x="n1"
      in meta_allE)
  apply(erule_tac
      x="d2"
      in meta_allE)
  apply(erule_tac
      x="n2"
      in meta_allE)
  apply(erule_tac
      x="f"
      in meta_allE)
  apply(force)
  done

definition relation_initial_simulation_preservation :: "
  'TSstructure1
  \<Rightarrow> 'TSstructure2
  \<Rightarrow> ('label1,'conf1)derivation
  \<Rightarrow> ('label2,'conf2)derivation
  \<Rightarrow> bool"
  where
    "relation_initial_simulation_preservation G1 G2 d1' d2' \<equiv>
  \<exists>c1 d1 n1 d2 n2 ds n f.
  relation_TSstructure G1 G2
  \<and> c1 \<in> initial_configurations1 G1
  \<and> relation_initial_simulation G1 G2 c1 ds
  \<and> maximum_of_domain ds n
  \<and> GL.derivation_initial G1 d1
  \<and> maximum_of_domain d1 n1
  \<and> GR.derivation_initial G2 d2
  \<and> maximum_of_domain d2 n2
  \<and> relation_initial_configuration G1 G2
        (the (get_configuration (d1 0)))
        (the (get_configuration (d2 0)))
  \<and> derivation_append_fit d1 (der1 c1) n1
  \<and> derivation_append_fit d2 ds n2
  \<and> d1' = derivation_append d1 (der1 c1) n1
  \<and> d2' = derivation_append d2 ds n2
  \<and> simulating_derivation G1 G2 d1' n1 d2' (n2 + n) f"

lemma relation_initial_simulation_preservation_PROVE: "
  relation_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> relation_initial_simulation G1 G2 c1 ds
  \<Longrightarrow> maximum_of_domain ds n
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> GR.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> relation_initial_configuration G1 G2
        (the(get_configuration(d1 0)))
        (the(get_configuration(d2 0)))
  \<Longrightarrow> derivation_append_fit d1 (der1 c1) n1
  \<Longrightarrow> derivation_append_fit d2 ds n2
  \<Longrightarrow> d1' = derivation_append d1 (der1 c1) n1
  \<Longrightarrow> d2' = derivation_append d2 ds n2
  \<Longrightarrow> simulating_derivation G1 G2 d1' n1 d2' (n2+n) f
  \<Longrightarrow> relation_initial_simulation_preservation G1 G2 d1' d2'"
  apply(simp (no_asm) only: relation_initial_simulation_preservation_def)
  apply(rule_tac
      x="c1"
      in exI)
  apply(rule_tac
      x="d1"
      in exI)
  apply(rule_tac
      x="n1"
      in exI)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="n2"
      in exI)
  apply(rule_tac
      x="ds"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="f"
      in exI)
  apply(force)
  done

lemma relation_initial_simulation_preservation_PROVE2: "
  (\<And>c1 d2 n deri1 deri1n deri2 deri2n f.
  relation_TSstructure G1 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> relation_initial_simulation G1 G2 c1 d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> GL.derivation_initial G1 deri1
  \<Longrightarrow> maximum_of_domain deri1 deri1n
  \<Longrightarrow> GR.derivation_initial G2 deri2
  \<Longrightarrow> maximum_of_domain deri2 deri2n
  \<Longrightarrow> relation_initial_configuration G1 G2 (the(get_configuration(deri1 0))) (the(get_configuration(deri2 0)))
  \<Longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n
  \<Longrightarrow> derivation_append_fit deri2 d2 deri2n
  \<Longrightarrow> simulating_derivation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n+n) f
  \<Longrightarrow> d1' = (derivation_append deri1 (der1 c1) deri1n)
  \<Longrightarrow> d2' = derivation_append deri2 d2 deri2n
  \<Longrightarrow> Q G1 G2 d1' d2')
  \<Longrightarrow> relation_initial_simulation_preservation G1 G2 d1' d2'
  \<Longrightarrow> Q G1 G2 d1' d2'"
  apply(unfold relation_initial_simulation_preservation_def)
  apply(erule exE)+
  apply(rename_tac c1 d1 n1 d2 n2 ds n f)(*strict*)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="ds"
      in meta_allE)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="d1"
      in meta_allE)
  apply(erule_tac
      x="n1"
      in meta_allE)
  apply(erule_tac
      x="d2"
      in meta_allE)
  apply(erule_tac
      x="n2"
      in meta_allE)
  apply(erule_tac
      x="f"
      in meta_allE)
  apply(force)
  done

lemma get_accessible_configurations_transfer: "
  relation_TSstructure G1 G2
  \<Longrightarrow> c2 \<in> configurations2 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> (\<And>cA cB.
          relation_configuration G1 G2 c1 cA
          \<Longrightarrow> relation_configuration G1 G2 c1 cB
          \<Longrightarrow> cA \<in> configurations2 G2
          \<Longrightarrow> cB \<in> configurations2 G2
          \<Longrightarrow> cA = cB)
  \<Longrightarrow> c1 \<in> GL.get_accessible_configurations G1
  \<Longrightarrow> c2 \<in> GR.get_accessible_configurations G2"
  apply(simp add: GL.get_accessible_configurations_def GR.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d i option)(*strict*)
   prefer 2
   apply(rule ATS_Simulation_Configuration_Weak_simulation_derivation_exists)
     apply(rename_tac d i option)(*strict*)
     apply(force)
    apply(rename_tac d i option)(*strict*)
    apply(force)
   apply(rename_tac d i option)(*strict*)
   apply(force)
  apply(rename_tac d i option)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option d2 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n2"
      in exI)
  apply(simp add: get_configuration_def)
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac d i option d2 n2 y)(*strict*)
  apply(case_tac y)
  apply(rename_tac d i option d2 n2 y optiona conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
  apply(erule_tac x="conf" in meta_allE)
  apply(erule_tac x="c2" in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
   apply(rule_tac d="d2" in GR.belongs_configurations)
    apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
   apply(rule GR.derivation_initial_belongs)
    apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
    apply(rule AX_TSstructure_relation_TSstructure2_belongs)
    apply(force)
   apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
   apply(force)
  apply(rename_tac d i option d2 n2 optiona conf)(*strict*)
  apply(force)
  done

theorem get_accessible_configurations_transfer_ALT: "
  relation_TSstructure G1 G2
  \<Longrightarrow> c2 \<in> configurations2 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> inj_on (relation_configuration G1 G2 c1) (configurations2 G2)
  \<Longrightarrow> c1 \<in> GL.get_accessible_configurations G1
  \<Longrightarrow> c2 \<in> GR.get_accessible_configurations G2"
  apply(rule get_accessible_configurations_transfer)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac cA cB)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac cA cB)(*strict*)
  apply(simp add: inj_on_def)
  done

end

end
