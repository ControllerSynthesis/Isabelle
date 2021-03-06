section {*L\_ATS\_Simulation\_Configuration\_WeakLR\_Unmarked\_Effect*}
theory
  L_ATS_Simulation_Configuration_WeakLR_Unmarked_Effect

imports
  L_ATS_Simulation_Configuration_Weak

begin

locale ATS_Simulation_Configuration_Weak_Unmarked_Effect =
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

assumes AX_relation_step_simulation_preserves_unmarked_effect: "
  relation_step_simulation_preservation G1 G2 d1' d2'
  \<Longrightarrow> left_total_on
        (relation_effect G1 G2)
        (unmarked_effect1 G1 d1')
        (unmarked_effect2 G2 d2')"

assumes AX_relation_initial_simulation_preserves_unmarked_effect: "
  relation_initial_simulation_preservation G1 G2 d1' d2'
  \<Longrightarrow> left_total_on
        (relation_effect G1 G2)
        (unmarked_effect1 G1 d1')
        (unmarked_effect2 G2 d2')"

context ATS_Simulation_Configuration_Weak_Unmarked_Effect begin

theorem ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound: "
  relation_TSstructure G1 G2
  \<Longrightarrow> left_total_on (relation_effect G1 G2) (GL.finite_unmarked_language G1) (GR.finite_unmarked_language G2)"
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(simp add: GL.finite_unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac a d x)(*strict*)
  apply(case_tac x)
   apply(rename_tac a d x)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac a d)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d c)(*strict*)
    apply(rename_tac c1)
    apply(rename_tac a d c1)(*strict*)
    apply(subgoal_tac "c1 \<in> initial_configurations1 G1")
     apply(rename_tac a d c1)(*strict*)
     prefer 2
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac a d c1)(*strict*)
    apply(subgoal_tac "\<exists>ds n. GR.derivation_initial G2 ds \<and> relation_initial_configuration G1 G2 c1 (the(get_configuration(ds 0))) \<and> relation_initial_simulation G1 G2 c1 ds \<and> maximum_of_domain ds n \<and> relation_configuration G1 G2 c1 (the(get_configuration(ds n)))")
     apply(rename_tac a d c1)(*strict*)
     prefer 2
     apply(rule AX_relation_initial_simulation)
      apply(rename_tac a d c1)(*strict*)
      apply(force)
     apply(rename_tac a d c1)(*strict*)
     apply(force)
    apply(rename_tac a d c1)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d c1 ds n)(*strict*)
    apply(subgoal_tac "\<exists>c2. ds 0 = Some (pair None c2)")
     apply(rename_tac a d c1 ds n)(*strict*)
     apply(clarsimp)
     apply(rename_tac a d c1 ds n c2)(*strict*)
     apply(subgoal_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 (derivation_append (der1 c1) (der1 c1) 0)) (unmarked_effect2 G2 (derivation_append (der1 (the(get_configuration(ds 0)))) ds 0))")
      apply(rename_tac a d c1 ds n c2)(*strict*)
      prefer 2
      apply(rule AX_relation_initial_simulation_preserves_unmarked_effect)
      apply(rule relation_initial_simulation_preservation_PROVE)
                   apply(rename_tac a d c1 ds n c2)(*strict*)
                   prefer 13
                   apply(force)
                  apply(rename_tac a d c1 ds n c2)(*strict*)
                  prefer 12
                  apply(force)
                 apply(rename_tac a d c1 ds n c2)(*strict*)
                 apply(force)
                apply(rename_tac a d c1 ds n c2)(*strict*)
                apply(force)
               apply(rename_tac a d c1 ds n c2)(*strict*)
               apply(force)
              apply(rename_tac a d c1 ds n c2)(*strict*)
              apply(force)
             apply(rename_tac a d c1 ds n c2)(*strict*)
             apply(simp add: GL.derivation_initial_def)
             apply(rule conjI)
              apply(rename_tac a d c1 ds n c2)(*strict*)
              apply(rule GL.der1_is_derivation)
             apply(rename_tac a d c1 ds n c2)(*strict*)
             apply(simp add: der1_def)
            apply(rename_tac a d c1 ds n c2)(*strict*)
            apply(rule der1_maximum_of_domain)
           apply(rename_tac a d c1 ds n c2)(*strict*)
           apply(simp add: GR.derivation_initial_def)
           apply(rule conjI)
            apply(rename_tac a d c1 ds n c2)(*strict*)
            apply(rule GR.der1_is_derivation)
           apply(rename_tac a d c1 ds n c2)(*strict*)
           apply(simp add: der1_def get_configuration_def)
          apply(rename_tac a d c1 ds n c2)(*strict*)
          apply(rule der1_maximum_of_domain)
         apply(rename_tac a d c1 ds n c2)(*strict*)
         apply(simp add: der1_def get_configuration_def)
        apply(rename_tac a d c1 ds n c2)(*strict*)
        apply(simp add: derivation_append_fit_def der1_def)
       apply(rename_tac a d c1 ds n c2)(*strict*)
       apply(simp add: derivation_append_fit_def der1_def get_configuration_def)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(rule_tac
      t="Some (pair None c2)"
      and s="ds 0"
      in ssubst)
       apply(rename_tac a d c1 ds n c2)(*strict*)
       apply(simp add: derivation_append_fit_def der1_def get_configuration_def)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(rule simulating_derivation_exist_initial)
          apply(rename_tac a d c1 ds n c2)(*strict*)
          apply(force)
         apply(rename_tac a d c1 ds n c2)(*strict*)
         apply(force)
        apply(rename_tac a d c1 ds n c2)(*strict*)
        apply(force)
       apply(rename_tac a d c1 ds n c2)(*strict*)
       apply(force)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(force)
     apply(rename_tac a d c1 ds n c2)(*strict*)
     apply(subgoal_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 d) (unmarked_effect2 G2 ds)")
      apply(rename_tac a d c1 ds n c2)(*strict*)
      prefer 2
      apply(rule_tac
      t="d"
      and s="derivation_append (der1 c1) (der1 c1) 0"
      in ssubst)
       apply(rename_tac a d c1 ds n c2)(*strict*)
       apply(rule ext)
       apply(rename_tac a d c1 ds n c2 x)(*strict*)
       apply(simp add: derivation_append_def der1_def)
       apply(clarsimp)
       apply (metis GL.derivation_initial_is_derivation GL.noSomeAfterMaxDom)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(rule_tac
      t="ds"
      and s="derivation_append (der1 (the (get_configuration (Some (pair None c2))))) ds 0"
      in ssubst)
       apply(rename_tac a d c1 ds n c2)(*strict*)
       apply(rule ext)
       apply(rename_tac a d c1 ds n c2 x)(*strict*)
       apply(simp add: derivation_append_def der1_def get_configuration_def)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(force)
     apply(rename_tac a d c1 ds n c2)(*strict*)
     apply(thin_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 (derivation_append (der1 c1) (der1 c1) 0)) (unmarked_effect2 G2 (derivation_append (der1 (the (get_configuration (ds 0)))) ds 0))")
     apply(rename_tac a d c1 ds n c2)(*strict*)
     apply(simp add: left_total_on_def)
     apply(erule_tac
      x="a"
      in ballE)
      apply(rename_tac a d c1 ds n c2)(*strict*)
      apply(clarsimp)
      apply(rename_tac a d c1 ds n c2 b)(*strict*)
      apply(rule_tac
      x="b"
      in bexI)
       apply(rename_tac a d c1 ds n c2 b)(*strict*)
       apply(force)
      apply(rename_tac a d c1 ds n c2 b)(*strict*)
      apply(simp add: GR.finite_unmarked_language_def)
      apply(rule_tac
      x="ds"
      in exI)
      apply(clarsimp)
      apply (metis)
     apply(rename_tac a d c1 ds n c2)(*strict*)
     apply(force)
    apply(rename_tac a d c1 ds n)(*strict*)
    apply (metis GR.derivation_initial_is_derivation GR.some_position_has_details_at_0)
   apply(rename_tac a d)(*strict*)
   apply (metis GL.derivation_initial_is_derivation GL.some_position_has_details_at_0)
  apply(rename_tac a d x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d nat)(*strict*)
  apply(rename_tac x)
  apply(rename_tac a d x)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> step_relation1 G1 c1 e2 c2")
   apply(rename_tac a d x)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc x"
      in GL.step_detail_before_some_position)
     apply(rename_tac a d x)(*strict*)
     apply(rule GL.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac a d x)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac a d x)(*strict*)
   apply(force)
  apply(rename_tac a d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d x e1 e2 c1 c2)(*strict*)
  apply(rename_tac e0 e1 c1 c1')
  apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
  apply(subgoal_tac "\<exists>d2 n2 f. GR.derivation_initial G2 d2 \<and> maximum_of_domain d2 n2 \<and> relation_initial_configuration G1 G2 (the(get_configuration(d 0))) (the(get_configuration(d2 0))) \<and> relation_configuration G1 G2 c1 (the(get_configuration(d2 n2))) \<and> simulating_derivation G1 G2 d x d2 n2 f")
   apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
   prefer 2
   apply(rule ATS_Simulation_Configuration_Weak_simulation_derivation_exists_witness)
     apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
     apply(force)
    apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
    apply(force)
   apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
   apply(force)
  apply(rename_tac a d x e0 e1 c1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac a d x e0 e1 c1 c1' d2 n2 xa)(*strict*)
  apply(rename_tac f)
  apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2 = Some (pair e c)")
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c)(*strict*)
   apply(rename_tac c2)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
   apply(subgoal_tac "\<exists>ds n. GR.derivation G2 ds \<and> GR.belongs G2 ds \<and> the(get_configuration(ds 0)) = c2 \<and> relation_step_simulation G1 G2 c1 e1 c1' c2 ds \<and> maximum_of_domain ds n \<and> relation_configuration G1 G2 c1' (the(get_configuration(ds n)))")
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
    prefer 2
    apply(rule AX_relation_step_simulation)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
       apply(force)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
     apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
    apply(force)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n)(*strict*)
   apply(subgoal_tac "\<exists>c2. ds 0 = Some (pair None c2)")
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
    apply(subgoal_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 (derivation_append SSd1 (der2 c1 e1 c1') SSn1)) (unmarked_effect2 G2 (derivation_append SSd2 ds SSn2))" for SSd1 SSn1 SSd2 SSn2)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
     prefer 2
     apply(rule AX_relation_step_simulation_preserves_unmarked_effect)
     apply(rule_tac
      ?d1.0="derivation_take d x"
      and ?d2.0="d2"
      and ?n1.0="x"
      and ?n2.0="n2"
      and f="\<lambda>a. if a \<le> x then f a else f x + n"
      in relation_step_simulation_preservation_PROVE)
                    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                    prefer 14
                    apply(force)
                   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                   prefer 14
                   apply(force)
                  apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                  apply(force)
                 apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                 apply(force)
                apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                apply (metis GL.belongs_step_labels GL.derivation_initial_belongs AX_TSstructure_relation_TSstructure1_belongs)
               apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
               apply(force)
              apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
              apply(simp add: get_configuration_def)
             apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
             apply(force)
            apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
            apply (metis GL.derivation_take_preserves_derivation_initial)
           apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
           apply (metis GL.derivationNoFromNone GL.derivation_initial_is_derivation maximum_of_domain_derivation_take)
          apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
          apply(force)
         apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
         apply(force)
        apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
        apply(simp add: get_configuration_def derivation_take_def)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
       apply(simp add: derivation_append_fit_def derivation_take_def der2_def)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
      apply(simp add: derivation_append_fit_def get_configuration_def)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
     apply(rule simulating_derivation_exist_step)
                 apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
                 apply(force)+
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
    apply(subgoal_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 d) (unmarked_effect2 G2 (derivation_append d2 ds n2))")
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
     prefer 2
     apply(rule_tac
      t="d"
      and s="(derivation_append (derivation_take d x) (der2 c1 e1 c1') x)"
      in ssubst)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
      apply(rule ext)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa)(*strict*)
      apply(simp add: derivation_append_def derivation_take_def der2_def)
      apply(case_tac "xa-x")
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa)(*strict*)
       apply(clarsimp)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nat)(*strict*)
      apply(clarsimp)
      apply(case_tac nat)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nat)(*strict*)
       apply(clarsimp)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa)(*strict*)
       apply(subgoal_tac "Suc x=xa")
        apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa)(*strict*)
       apply(clarsimp)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nat nata)(*strict*)
      apply(clarsimp)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nata)(*strict*)
      apply(subgoal_tac "xa=x+Suc(Suc nata)")
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nata)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 xa nata)(*strict*)
      apply(clarsimp)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 nata)(*strict*)
      apply(rule GL.none_position_after_max_dom)
        apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 nata)(*strict*)
        apply(rule GL.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 nata)(*strict*)
       apply(force)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 nata)(*strict*)
      apply(force)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
     apply(force)
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
    apply(thin_tac "left_total_on (relation_effect G1 G2) (unmarked_effect1 G1 (derivation_append (derivation_take d x) (der2 c1 e1 c1') x)) (unmarked_effect2 G2 (derivation_append d2 ds n2))")
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
    apply(simp add: left_total_on_def)
    apply(erule_tac
      x="a"
      in ballE)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
     apply(clarsimp)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
     apply(rule_tac
      x="b"
      in bexI)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
      apply(force)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
     apply(simp add: GR.finite_unmarked_language_def)
     apply(rule_tac
      x="derivation_append d2 ds n2"
      in exI)
     apply(clarsimp)
     apply(rule context_conjI)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
      apply(rule GR.derivation_append_preserves_derivation_initial)
        apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
        apply (metis AX_TSstructure_relation_TSstructure2_belongs)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
       apply(force)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
      apply(rule GR.derivation_append_preserves_derivation)
        apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
        apply(rule GR.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
       apply(force)
      apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2 b)(*strict*)
     apply(rule_tac
      x="n2+n"
      in exI)
     apply (metis concat_has_max_dom)
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n c2)(*strict*)
    apply(force)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f e ds n)(*strict*)
   apply (metis GR.some_position_has_details_at_0)
  apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
  apply(rule GR.some_position_has_details_before_max_dom)
    apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
    apply(rule GR.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
   apply(force)
  apply(rename_tac a d x e0 e1 c1 c1' d2 n2 f)(*strict*)
  apply(force)
  done

end

end
