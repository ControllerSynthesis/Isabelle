section {*L\_ATS\_Isomorphism*}
theory
  L_ATS_Isomorphism

imports
  PRJ_06_06__PRE

begin

locale ATS_Isomorphism =
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

fixes marking_configuration1 :: "'TSstructure1 \<Rightarrow> 'conf1 \<Rightarrow> bool"

fixes marking_configuration2 :: "'TSstructure2 \<Rightarrow> 'conf2 \<Rightarrow> bool"

fixes relation_TSstructure :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> bool"

fixes relation_configuration :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'conf1 \<Rightarrow> 'conf2 \<Rightarrow> bool"

fixes relation_label :: "'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> 'label1 \<Rightarrow> 'label2 \<Rightarrow> bool"

assumes AX_relation_TSstructure_closed1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> TSstructure1 G1"

assumes AX_relation_TSstructure_closed2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> TSstructure2 G2"

assumes AX_relation_configuration_closed1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c1 \<in> configurations1 G1"

assumes AX_relation_configuration_closed2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c2 \<in> configurations2 G2"

assumes AX_relation_configuration_for_initial_closed1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1
  \<Longrightarrow> c2 \<in> initial_configurations2 G2"

assumes AX_relation_configuration_for_initial_closed2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> c2 \<in> initial_configurations2 G2
  \<Longrightarrow> c1 \<in> initial_configurations1 G1"

assumes AX_relation_label_closed1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_label G1 G2 e1 e2
  \<Longrightarrow> e1 \<in> step_labels1 G1"

assumes AX_relation_label_closed2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_label G1 G2 e1 e2
  \<Longrightarrow> e2 \<in> step_labels2 G2"

assumes AX_relation_configuration_bijection_on: "
  relation_TSstructure G1 G2
  \<Longrightarrow> bijection_on (relation_configuration G1 G2) (configurations1 G1) (configurations2 G2)"

assumes AX_relation_label_bijection_on: "
  relation_TSstructure G1 G2
  \<Longrightarrow> bijection_on (relation_label G1 G2) (step_labels1 G1) (step_labels2 G2)"

assumes AX_marking_configuration1_equivalent: "
  TSstructure1 G1
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> marking_condition1 G1 d1
  \<longleftrightarrow> (\<exists>i c1. get_configuration(d1 i) = Some c1 \<and> marking_configuration1 G1 c1)"

assumes AX_marking_configuration2_equivalent: "
  TSstructure2 G2
  \<Longrightarrow> GR.derivation_initial G2 d2
  \<Longrightarrow> marking_condition2 G2 d2
  \<longleftrightarrow> (\<exists>i c2. get_configuration(d2 i) = Some c2 \<and> marking_configuration2 G2 c2)"

assumes AX_relation_configuration_preserves_marking_configuration: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> marking_configuration1 G1 c1 \<longleftrightarrow> marking_configuration2 G2 c2"

assumes AX_step_preservation1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'
  \<Longrightarrow> relation_label G1 G2 e1 e2
  \<Longrightarrow> relation_configuration G1 G2 c1' c2'
  \<Longrightarrow> step_relation2 G2 c2 e2 c2'"

assumes AX_step_preservation2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> relation_configuration G1 G2 c1 c2
  \<Longrightarrow> step_relation2 G2 c2 e2 c2'
  \<Longrightarrow> relation_label G1 G2 e1 e2
  \<Longrightarrow> relation_configuration G1 G2 c1' c2'
  \<Longrightarrow> step_relation1 G1 c1 e1 c1'"

context ATS_Isomorphism begin

lemma preserve_derivation1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation G1 d1
  \<Longrightarrow> GL.belongs G1 d1
  \<Longrightarrow> \<exists>d2.
  GR.derivation G2 d2
  \<and> GR.belongs G2 d2
  \<and> (\<forall>i\<le>MAXval. \<forall>e1 c1.
  (d1 i = None \<longrightarrow> d2 i = None)
  \<and> (d1 i = Some (pair e1 c1) \<longrightarrow> (\<exists>e2 c2.
  d2 i = Some (pair e2 c2)
  \<and> relation_configuration G1 G2 c1 c2
  \<and> (case e1 of None \<Rightarrow> (case e2 of None \<Rightarrow> True | Some e2' \<Rightarrow> False)
  | Some e1' \<Rightarrow> (case e2 of None \<Rightarrow> False | Some e2' \<Rightarrow> relation_label G1 G2 e1' e2')
  ))))"
  apply(induct MAXval)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c1. d1 0 = Some (pair None c1)")
    prefer 2
    apply (metis GL.some_position_has_details_at_0)
   apply(clarsimp)
   apply(rename_tac c1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c1)(*strict*)
    prefer 2
    apply(rule_tac
      a="c1"
      in bijection_on_RT)
     apply(rename_tac c1)(*strict*)
     apply(rule AX_relation_configuration_bijection_on)
     apply(force)
    apply(rename_tac c1)(*strict*)
    apply (metis GL.belongs_configurations)
   apply(rename_tac c1)(*strict*)
   apply(clarsimp)
   apply(rename_tac c1 b)(*strict*)
   apply(rule_tac
      x="der1 b"
      in exI)
   apply(rule conjI)
    apply(rename_tac c1 b)(*strict*)
    apply(rule GR.der1_is_derivation)
   apply(rename_tac c1 b)(*strict*)
   apply(rule conjI)
    apply(rename_tac c1 b)(*strict*)
    apply(rule GR.der1_belongs)
    apply (metis)
   apply(rename_tac c1 b)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac MAXval)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2)(*strict*)
  apply(case_tac "d1 (Suc MAXval)")
   apply(rename_tac MAXval d2)(*strict*)
   apply(rule_tac
      x="derivation_take d2 MAXval"
      in exI)
   apply(rule conjI)
    apply(rename_tac MAXval d2)(*strict*)
    apply(rule GR.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac MAXval d2)(*strict*)
   apply(rule conjI)
    apply(rename_tac MAXval d2)(*strict*)
    apply(rule GR.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac MAXval d2)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d2 i)(*strict*)
   apply(case_tac "i\<le>MAXval")
    apply(rename_tac MAXval d2 i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac MAXval d2 i)(*strict*)
   apply(subgoal_tac "i=Suc MAXval")
    apply(rename_tac MAXval d2 i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac MAXval d2 i)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d2)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac MAXval d2 a)(*strict*)
  apply(case_tac a)
  apply(rename_tac MAXval d2 a option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac MAXval d2 a e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac MAXval d2 e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d2 c)(*strict*)
   apply(simp add: GL.derivation_def)
   apply(erule_tac
      x="Suc MAXval"
      in allE)+
   apply(clarsimp)
   apply(case_tac "d1 MAXval")
    apply(rename_tac MAXval d2 c)(*strict*)
    apply(force)
   apply(rename_tac MAXval d2 c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac MAXval d2 c a option conf)(*strict*)
   apply(force)
  apply(rename_tac MAXval d2 e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c a)(*strict*)
  apply(rename_tac e)
  apply(rename_tac MAXval d2 c e)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d2 c e)(*strict*)
   prefer 2
   apply(rule_tac
      a="e"
      and A="step_labels1 G1"
      in bijection_on_RT)
    apply(rename_tac MAXval d2 c e)(*strict*)
    apply(rule AX_relation_label_bijection_on)
    apply(force)
   apply(rename_tac MAXval d2 c e)(*strict*)
   apply (metis GL.belongs_step_labels)
  apply(rename_tac MAXval d2 c e)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c e b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d2 c e b)(*strict*)
   prefer 2
   apply(rule_tac
      a="c"
      in bijection_on_RT)
    apply(rename_tac MAXval d2 c e b)(*strict*)
    apply(rule AX_relation_configuration_bijection_on)
    apply(force)
   apply(rename_tac MAXval d2 c e b)(*strict*)
   apply (metis GL.belongs_configurations)
  apply(rename_tac MAXval d2 c e b)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c e b ba)(*strict*)
  apply(rename_tac e' c')
  apply(rename_tac MAXval d2 c e e' c')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d2 c e e' c')(*strict*)
   prefer 2
   apply(rule_tac
      n="MAXval"
      and d="d1"
      and m="Suc MAXval"
      in GL.step_detail_before_some_position)
     apply(rename_tac MAXval d2 c e e' c')(*strict*)
     apply(force)
    apply(rename_tac MAXval d2 c e e' c')(*strict*)
    apply(force)
   apply(rename_tac MAXval d2 c e e' c')(*strict*)
   apply(force)
  apply(rename_tac MAXval d2 c e e' c')(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c e e' c' e1 c1)(*strict*)
  apply(erule_tac x="MAXval" in allE')
  apply(simp (no_asm_use))
  apply(erule conjE)+
  apply(thin_tac "d1 MAXval = None \<longrightarrow> d2 MAXval = None")
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule impE)
   apply(rename_tac MAXval d2 c e e' c' e1 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac MAXval d2 c e e' c' e1 c1)(*strict*)
  apply(erule exE)+
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      ?c1.0="c1"
      and c1'="c"
      and c2'="c'"
      and ?e1.0="e"
      and ?e2.0="e'"
      in AX_step_preservation1)
       apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
       apply(force)
      apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
  apply(rule_tac
      x="derivation_append d2 (der2 c2 e' c') MAXval"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
    apply(rule GR.der2_is_derivation)
    apply(force)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   apply(rule GR.derivation_append_preserves_belongs)
     apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
     apply (metis AX_relation_TSstructure_closed2)
    apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
  apply(case_tac "i\<le>MAXval")
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i e1a c1a e2a c2a)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
  apply(subgoal_tac "i=Suc MAXval")
   apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2 i)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d2 c e e' c' e1 c1 e2 c2)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  done

lemma preserve_initial_derivation1: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.derivation_initial G1 d1
  \<Longrightarrow> \<exists>d2.
  GR.derivation_initial G2 d2
  \<and> (\<forall>i\<le>MAXval. \<forall>e1 c1.
  (d1 i = None \<longrightarrow> d2 i = None)
  \<and> (d1 i = Some (pair e1 c1) \<longrightarrow> (\<exists>e2 c2.
  d2 i = Some (pair e2 c2)
  \<and> relation_configuration G1 G2 c1 c2
  \<and> (case e1 of None \<Rightarrow> (case e2 of None \<Rightarrow> True | Some e2' \<Rightarrow> False)
  | Some e1' \<Rightarrow> (case e2 of None \<Rightarrow> False | Some e2' \<Rightarrow> relation_label G1 G2 e1' e2')
  ))))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      MAXval="MAXval"
      in preserve_derivation1)
     apply(force)
    apply(simp add: GL.derivation_initial_def)
    apply(force)
   apply(rule GL.derivation_initial_belongs)
    apply (metis AX_relation_TSstructure_closed1)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule GR.derivation_initialI)
   apply(rename_tac d2)(*strict*)
   apply(force)
  apply(rename_tac d2)(*strict*)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(rename_tac d2 c y)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac y)
  apply(rename_tac d2 c y option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac d2 ca y e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d2 ca e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac d2 ca e c)(*strict*)
   prefer 2
   apply(rename_tac d2 ca e c a)(*strict*)
   apply(simp add: GL.derivation_initial_def GL.derivation_def)
  apply(rename_tac d2 ca e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d2 ca c)(*strict*)
  apply(simp add: GL.derivation_initial_def)
  apply(clarsimp)
  apply(rule AX_relation_configuration_for_initial_closed1)
    apply(rename_tac d2 ca c)(*strict*)
    apply(force)
   apply(rename_tac d2 ca c)(*strict*)
   apply(force)
  apply(rename_tac d2 ca c)(*strict*)
  apply(force)
  done

lemma preserve_derivation2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GR.derivation G2 d2
  \<Longrightarrow> GR.belongs G2 d2
  \<Longrightarrow> \<exists>d1.
  GL.derivation G1 d1
  \<and> GL.belongs G1 d1
  \<and> (\<forall>i\<le>MAXval. \<forall>e2 c2.
  (d2 i = None \<longrightarrow> d1 i = None)
  \<and> (d2 i = Some (pair e2 c2) \<longrightarrow> (\<exists>e1 c1.
  d1 i = Some (pair e1 c1)
  \<and> relation_configuration G1 G2 c1 c2
  \<and> (case e2 of None \<Rightarrow> (case e1 of None \<Rightarrow> True | Some e1' \<Rightarrow> False)
  | Some e2' \<Rightarrow> (case e1 of None \<Rightarrow> False | Some e1' \<Rightarrow> relation_label G1 G2 e1' e2')
  ))))"
  apply(induct MAXval)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c1. d2 0 = Some (pair None c1)")
    prefer 2
    apply (metis GR.some_position_has_details_at_0)
   apply(clarsimp)
   apply(rename_tac c1)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac c1)(*strict*)
    prefer 2
    apply(rule_tac
      b="c1"
      in bijection_on_LT)
     apply(rename_tac c1)(*strict*)
     apply(rule AX_relation_configuration_bijection_on)
     apply(force)
    apply(rename_tac c1)(*strict*)
    apply (metis GR.belongs_configurations)
   apply(rename_tac c1)(*strict*)
   apply(clarsimp)
   apply(rename_tac c1 a)(*strict*)
   apply(rule_tac
      x="der1 a"
      in exI)
   apply(rule conjI)
    apply(rename_tac c1 a)(*strict*)
    apply(rule GL.der1_is_derivation)
   apply(rename_tac c1 a)(*strict*)
   apply(rule conjI)
    apply(rename_tac c1 a)(*strict*)
    apply(rule GL.der1_belongs)
    apply (metis)
   apply(rename_tac c1 a)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac MAXval)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1)(*strict*)
  apply(case_tac "d2 (Suc MAXval)")
   apply(rename_tac MAXval d1)(*strict*)
   apply(rule_tac
      x="derivation_take d1 MAXval"
      in exI)
   apply(rule conjI)
    apply(rename_tac MAXval d1)(*strict*)
    apply(rule GL.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac MAXval d1)(*strict*)
   apply(rule conjI)
    apply(rename_tac MAXval d1)(*strict*)
    apply(rule GL.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac MAXval d1)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d1 i)(*strict*)
   apply(case_tac "i\<le>MAXval")
    apply(rename_tac MAXval d1 i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_take_def)
   apply(rename_tac MAXval d1 i)(*strict*)
   apply(subgoal_tac "i=Suc MAXval")
    apply(rename_tac MAXval d1 i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac MAXval d1 i)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac MAXval d1 a)(*strict*)
  apply(case_tac a)
  apply(rename_tac MAXval d1 a option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac MAXval d1 a e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac MAXval d1 e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d1 c)(*strict*)
   apply(simp add: GR.derivation_def)
   apply(erule_tac
      x="Suc MAXval"
      in allE)+
   apply(clarsimp)
   apply(case_tac "d2 MAXval")
    apply(rename_tac MAXval d1 c)(*strict*)
    apply(force)
   apply(rename_tac MAXval d1 c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac MAXval d1 c a option conf)(*strict*)
   apply(force)
  apply(rename_tac MAXval d1 e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c a)(*strict*)
  apply(rename_tac e)
  apply(rename_tac MAXval d1 c e)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d1 c e)(*strict*)
   prefer 2
   apply(rule_tac
      b="e"
      and A="step_labels1 G1"
      in bijection_on_LT)
    apply(rename_tac MAXval d1 c e)(*strict*)
    apply(rule AX_relation_label_bijection_on)
    apply(force)
   apply(rename_tac MAXval d1 c e)(*strict*)
   apply (metis GR.belongs_step_labels)
  apply(rename_tac MAXval d1 c e)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c e a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d1 c e a)(*strict*)
   prefer 2
   apply(rule_tac
      b="c"
      in bijection_on_LT)
    apply(rename_tac MAXval d1 c e a)(*strict*)
    apply(rule AX_relation_configuration_bijection_on)
    apply(force)
   apply(rename_tac MAXval d1 c e a)(*strict*)
   apply (metis GR.belongs_configurations)
  apply(rename_tac MAXval d1 c e a)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c e a aa)(*strict*)
  apply(rename_tac e' c')
  apply(rename_tac MAXval d1 c e e' c')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d1 c e e' c')(*strict*)
   prefer 2
   apply(rule_tac
      n="MAXval"
      and d="d2"
      and m="Suc MAXval"
      in GR.step_detail_before_some_position)
     apply(rename_tac MAXval d1 c e e' c')(*strict*)
     apply(force)
    apply(rename_tac MAXval d1 c e e' c')(*strict*)
    apply(force)
   apply(rename_tac MAXval d1 c e e' c')(*strict*)
   apply(force)
  apply(rename_tac MAXval d1 c e e' c')(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c e e' c' e1 c1)(*strict*)
  apply(erule_tac x="MAXval" in allE')
  apply(simp (no_asm_use))
  apply(erule conjE)+
  apply(thin_tac "d2 MAXval = None \<longrightarrow> d1 MAXval = None")
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule impE)
   apply(rename_tac MAXval d1 c e e' c' e1 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac MAXval d1 c e e' c' e1 c1)(*strict*)
  apply(erule exE)+
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   prefer 2
   apply(rule_tac
      ?c2.0="c1"
      and c2'="c"
      and c1'="c'"
      and ?e2.0="e"
      and ?e1.0="e'"
      in AX_step_preservation2)
       apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
       apply(force)
      apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
      apply(force)
     apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
     apply(force)
    apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
    apply(force)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   apply(force)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
  apply(rule_tac
      x="derivation_append d1 (der2 c1a e' c') MAXval"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   apply(rule GL.derivation_append_preserves_derivation)
     apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
     apply(force)
    apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
    apply(rule GL.der2_is_derivation)
    apply(force)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
  apply(rule conjI)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   apply(rule GL.derivation_append_preserves_belongs)
     apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
     apply (metis AX_relation_TSstructure_closed1)
    apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
    apply(force)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
   apply(force)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
  apply(case_tac "i\<le>MAXval")
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
   apply(clarsimp)
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i e2 c2 e1b c1b)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
  apply(subgoal_tac "i=Suc MAXval")
   apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a i)(*strict*)
  apply(clarsimp)
  apply(rename_tac MAXval d1 c e e' c' e1 c1 e1a c1a)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  done

lemma preserve_initial_derivation2: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GR.derivation_initial G2 d2
  \<Longrightarrow> \<exists>d1.
  GL.derivation_initial G1 d1
  \<and> (\<forall>i\<le>MAXval. \<forall>e2 c2.
  (d2 i = None \<longrightarrow> d1 i = None)
  \<and> (d2 i = Some (pair e2 c2) \<longrightarrow> (\<exists>e1 c1.
  d1 i = Some (pair e1 c1)
  \<and> relation_configuration G1 G2 c1 c2
  \<and> (case e2 of None \<Rightarrow> (case e1 of None \<Rightarrow> True | Some e1' \<Rightarrow> False)
  | Some e2' \<Rightarrow> (case e1 of None \<Rightarrow> False | Some e1' \<Rightarrow> relation_label G1 G2 e1' e2')
  ))))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      MAXval="MAXval"
      in preserve_derivation2)
     apply(force)
    apply(simp add: GR.derivation_initial_def)
    apply(force)
   apply(rule GR.derivation_initial_belongs)
    apply (metis AX_relation_TSstructure_closed2)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d1)(*strict*)
  apply(rule_tac
      x="d1"
      in exI)
  apply(clarsimp)
  apply(rule GL.derivation_initialI)
   apply(rename_tac d1)(*strict*)
   apply(force)
  apply(rename_tac d1)(*strict*)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(rename_tac d1 c y)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac y)
  apply(rename_tac d1 c y option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac d1 ca y e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 ca e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac d1 ca e c)(*strict*)
   prefer 2
   apply(rename_tac d1 ca e c a)(*strict*)
   apply(simp add: GR.derivation_initial_def GL.derivation_def)
  apply(rename_tac d1 ca e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 ca c)(*strict*)
  apply(simp add: GR.derivation_initial_def)
  apply(clarsimp)
  apply(rule AX_relation_configuration_for_initial_closed2)
    apply(rename_tac d1 ca c)(*strict*)
    apply(force)
   apply(rename_tac d1 ca c)(*strict*)
   apply(force)
  apply(rename_tac d1 ca c)(*strict*)
  apply(force)
  done

theorem is_forward_edge_deterministic_accessible_preservation: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.is_forward_edge_deterministic_accessible G1
  \<Longrightarrow> GR.is_forward_edge_deterministic_accessible G2"
  apply(simp add: GR.is_forward_edge_deterministic_accessible_def GR.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac c d c1 c2 e1 e2 i)(*strict*)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c d c1 c2 e1 e2 i a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac c d c1 c2 e1 e2 i e)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d c1 c2 e1 e2 i e)(*strict*)
   prefer 2
   apply(rule_tac
      MAXval="i"
      in preserve_initial_derivation2)
    apply(rename_tac c d c1 c2 e1 e2 i e)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e)(*strict*)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1)(*strict*)
  apply(simp add: GL.is_forward_edge_deterministic_accessible_def GL.get_accessible_configurations_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
  apply(erule_tac
      x="c1a"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
   prefer 2
   apply(rule_tac
      b="e1"
      and B="step_labels2 G2"
      in bijection_on_LT)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
    apply(rule AX_relation_label_bijection_on)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
   apply(rule GR.AX_step_relation_preserves_belongsE)
     apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
     apply(rule AX_relation_TSstructure_closed2)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
   apply (metis AX_relation_configuration_closed2)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
   prefer 2
   apply(rule_tac
      b="e2"
      and B="step_labels2 G2"
      in bijection_on_LT)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
    apply(rule AX_relation_label_bijection_on)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
   apply(rule GR.AX_step_relation_preserves_belongsE)
     apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
     apply(rule AX_relation_TSstructure_closed2)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
   apply (metis AX_relation_configuration_closed2)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a a aa)(*strict*)
  apply(rename_tac e1' e2')
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2')(*strict*)
   prefer 2
   apply(rule_tac
      b="c1"
      and B="configurations2 G2"
      in bijection_on_LT)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2')(*strict*)
    apply(rule AX_relation_configuration_bijection_on)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2')(*strict*)
   apply (metis GR.AX_step_relation_preserves_belongsC AX_relation_configuration_closed2 AX_relation_TSstructure_closed2)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2')(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a)(*strict*)
   prefer 2
   apply(rule_tac
      b="c2"
      and B="configurations2 G2"
      in bijection_on_LT)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a)(*strict*)
    apply(rule AX_relation_configuration_bijection_on)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a)(*strict*)
   apply (metis GR.AX_step_relation_preserves_belongsC AX_relation_configuration_closed2 AX_relation_TSstructure_closed2)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' a aa)(*strict*)
  apply(rename_tac c1' c2')
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
  apply(erule_tac
      x="c1'"
      in allE)
  apply(erule_tac
      x="c2'"
      in allE)
  apply(erule_tac
      x="e1'"
      in allE)
  apply(erule_tac
      x="e2'"
      in allE)
  apply(erule impE)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
   apply(rule conjI)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
    apply(rule_tac
      ?c2.0="c"
      in AX_step_preservation2)
        apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
        apply(force)
       apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
       apply(force)
      apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
   apply(rule_tac
      ?c2.0="c"
      and c2'="c2"
      in AX_step_preservation2)
       apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
       apply(force)
      apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
     apply(force)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
    apply(force)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
  apply(rule_tac
      a="e1'"
      and ?b1.0="e1"
      and ?b2.0="e2"
      in bijection_on_RU)
       apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
       apply(rule AX_relation_label_bijection_on)
       apply(force)
      apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
      apply(force)
     apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
     apply (metis AX_relation_label_closed2)
    apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
    apply (metis AX_relation_label_closed2)
   apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
   apply(force)
  apply(rename_tac c d c1 c2 e1 e2 i e d1 e1a c1a e1' e2' c1' c2')(*strict*)
  apply(force)
  done

theorem Nonblockingness_branching_preservation: "
  relation_TSstructure G1 G2
  \<Longrightarrow> GL.Nonblockingness_branching G1
  \<Longrightarrow> GR.Nonblockingness_branching G2"
  apply(simp add: GR.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule_tac
      MAXval="Suc n"
      in preserve_initial_derivation2)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1)(*strict*)
  apply(simp add: GL.Nonblockingness_branching_def maximum_of_domain_def)
  apply(erule_tac
      x="d1"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n d1 y)(*strict*)
  apply(case_tac y)
  apply(rename_tac dh n d1 y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1 option conf)(*strict*)
  apply(rename_tac e1 c1)
  apply(rename_tac dh n d1 e1 c1)(*strict*)
  apply(erule_tac
      x="n"
      and P="\<lambda>n. (\<exists>y. d1 n = Some y) \<and> d1 (Suc n) = None \<longrightarrow> (\<exists>dc. ATS.derivation step_relation1 G1 dc \<and> ATS.belongs configurations1 step_labels1 G1 dc \<and> (\<exists>n'. (\<exists>y. dc n' = Some y) \<and> dc (Suc n') = None \<and> derivation_append_fit d1 dc n \<and> marking_condition1 G1 (derivation_append d1 dc n)))"
      in allE)
  apply(erule impE)
   apply(rename_tac dh n d1 e1 c1)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n d1 e1 c1)(*strict*)
    apply(erule_tac
      x="n"
      in allE)
    apply(force)
   apply(rename_tac dh n d1 e1 c1)(*strict*)
   apply(erule_tac
      x="Suc n"
      in allE)
   apply(force)
  apply(rename_tac dh n d1 e1 c1)(*strict*)
  apply(erule_tac x="n" in allE')
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' y)(*strict*)
  apply(case_tac y)
  apply(rename_tac dh n d1 e1 c1 dc n' y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' option conf)(*strict*)
  apply(rename_tac e2 c2)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="G1"
      and ?d1.0="(derivation_append d1 dc n)"
      in AX_marking_configuration1_equivalent)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
    apply(rule AX_relation_TSstructure_closed1)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
   apply(rule GL.derivation_append_preserves_derivation_initial)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
     apply(rule AX_relation_TSstructure_closed1)
     apply(force)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
   apply(rule GL.derivation_append_preserves_derivation)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
   apply(case_tac "d1 n")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="n"
      in allE)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf)(*strict*)
    apply(clarsimp)
    apply(simp add: GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf a optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf optiona confa)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf optiona confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf confa)(*strict*)
    apply(simp add: derivation_append_fit_def)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf optiona confa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 option conf confa a)(*strict*)
   apply(simp add: GL.derivation_def)
   apply(erule_tac
      x="0"
      in allE)+
   apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
  apply(subgoal_tac "(\<exists>i c1. get_configuration (derivation_append d1 dc n i) = Some c1 \<and> marking_configuration1 G1 c1)")
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2)(*strict*)
  apply(thin_tac "marking_condition1 G1 (derivation_append d1 dc n)")
  apply(thin_tac "marking_condition1 G1 (derivation_append d1 dc n) = (\<exists>i c1. get_configuration (derivation_append d1 dc n i) = Some c1 \<and> marking_configuration1 G1 c1)")
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
   apply(subgoal_tac "\<exists>j. i+j=n")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
    prefer 2
    apply(rule_tac
      x="n-i"
      in exI)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
    prefer 2
    apply(rule_tac
      g="dh"
      and n="i"
      and m="i+j"
      in GR.pre_some_position_is_some_position)
      apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
      apply(simp add: GR.derivation_initial_def)
      apply(force)
     apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
     apply(force)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
    apply(force)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule_tac
      x="der1 c1"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule GR.der1_is_derivation)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule GR.der1_belongs)
    apply (metis (full_types) GR.derivation_initial_configurations AX_relation_TSstructure_closed2)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: maximum_of_domain_def der1_def)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule_tac
      t="marking_condition2 G2 (derivation_append dh (der1 c1) (i + j))"
      in ssubst)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule AX_marking_configuration2_equivalent)
     apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
     apply(rule AX_relation_TSstructure_closed2)
     apply(force)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
      apply(rule AX_relation_TSstructure_closed2)
      apply(force)
     apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
     apply(force)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation)
      apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
      apply(simp add: GR.derivation_initial_def)
     apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
     apply(rule GR.der1_is_derivation)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(clarsimp)
    apply(simp add: der1_def)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule_tac
      P="\<lambda>X. X"
      in subst)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(rule AX_relation_configuration_preserves_marking_configuration)
     apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
     apply(force)
    apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
    apply(force)
   apply(rename_tac dh d1 e1 c1 dc n' e2 c2 i c1a j e c e1a c1b)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
  apply(subgoal_tac "n<i")
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
  apply(subgoal_tac "\<exists>j. n+Suc j=i")
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
   prefer 2
   apply(rule_tac
      x="i-Suc n"
      in exI)
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 i c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j)(*strict*)
  apply(subgoal_tac "\<exists>e. dc (Suc j) = Some (pair e c1a)")
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def get_configuration_def)
   apply(case_tac "dc (Suc j)")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j a option conf)(*strict*)
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
  apply(thin_tac "get_configuration (derivation_append d1 dc n (Suc (n + j))) = Some c1a")
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="dc"
      and MAXval="Suc n'"
      in preserve_derivation1)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
     apply(force)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(rule_tac
      x="n'"
      in exI)
   apply(simp add: maximum_of_domain_def)
   apply(erule_tac
      x="n'"
      in allE)+
   apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac "d2 0")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
    apply(clarsimp)
    apply(simp add: GR.derivation_def GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 option conf)(*strict*)
    prefer 2
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 option conf a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf a)(*strict*)
    apply(simp add: GR.derivation_def GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b)(*strict*)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b y)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b y option confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b option confa)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b option confa)(*strict*)
    apply(simp add: GR.derivation_def GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(clarsimp)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
    apply(rule_tac
      a="confa"
      in bijection_on_RU)
         apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
         apply(rule AX_relation_configuration_bijection_on)
         apply(force)
        apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
        apply (metis AX_relation_configuration_closed1)
       apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
       apply (metis AX_relation_configuration_closed2)
      apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
      apply (metis AX_relation_configuration_closed2)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
     apply(force)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a confa)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 conf e1a c1b option confa a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
  apply(rule_tac
      P="\<lambda>x. x"
      in ssubst)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(rule AX_marking_configuration2_equivalent)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
    apply(rule AX_relation_TSstructure_closed2)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation_initial)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
     apply(rule AX_relation_TSstructure_closed2)
     apply(force)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(erule_tac
      x="n"
      in allE)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b)(*strict*)
    apply(clarsimp)
    apply(simp add: GR.derivation_def GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b a y)(*strict*)
   apply(case_tac a)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b a y option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b y option conf)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b y option conf optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b option conf optiona confa)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b option conf optiona confa)(*strict*)
    prefer 2
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b option conf optiona confa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa a)(*strict*)
    apply(simp add: GR.derivation_def GL.derivation_def)
    apply(erule_tac
      x="0"
      in allE)+
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b option conf optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
    prefer 2
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
   apply(rule_tac
      a="confa"
      in bijection_on_RU)
        apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
        apply(rule AX_relation_configuration_bijection_on)
        apply(force)
       apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
       apply (metis AX_relation_configuration_closed1)
      apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
      apply (metis AX_relation_configuration_closed2)
     apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
     apply (metis AX_relation_configuration_closed2)
    apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
    apply(force)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e1a c1b conf optiona confa)(*strict*)
   apply(force)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
  apply(rule_tac
      x="n+Suc j"
      in exI)
  apply(erule_tac
      P="\<lambda>i. (i\<le>Suc n' \<longrightarrow> ((dc i = None \<longrightarrow> d2 i = None) \<and> (\<forall>e1 c1. dc i = Some (pair e1 c1) \<longrightarrow> (\<exists>e2 c2. d2 i = Some (pair e2 c2) \<and> relation_configuration G1 G2 c1 c2 \<and> (case e1 of None \<Rightarrow> (case e2 of None \<Rightarrow> True | Some e2' \<Rightarrow> False) | Some e1' \<Rightarrow> (case e2 of None \<Rightarrow> False | Some x \<Rightarrow> relation_label G1 G2 e1' x))))))"
      and x="Suc j"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2 e2a c2a)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
   apply (metis AX_relation_configuration_preserves_marking_configuration)
  apply(rename_tac dh n d1 e1 c1 dc n' e2 c2 c1a j e d2)(*strict*)
  apply (metis GL.allPreMaxDomSome_prime GL.derivationNoFromNone_prime maximum_of_domain_def)
  done

end

end
