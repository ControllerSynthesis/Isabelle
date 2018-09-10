section {*L\_ATS\_Simulation\_Configuration\_Weak\_Plain*}
theory
  L_ATS_Simulation_Configuration_Weak_Plain

imports
  PRJ_06_06__PRE

begin

(*
translation of
  marked language
  unmarked language
using
  simulation relation on configuration where steps are mimicked weakly.
*)

locale ATS_Simulation_Configuration_Weak_Plain =
  GL:
  ATS_Language_by_Finite_Derivations
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
  ATS_Language_by_Finite_Derivations
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

context ATS_Simulation_Configuration_Weak_Plain
begin

definition preserve_effect :: "bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool" where
  "preserve_effect ANY ACCEPT GL GR OR SR ISR d2L d2R \<equiv>
  \<forall>dL d1L n1L dR d1R n1R.
  ((the(get_configuration (d1L 0)),the(get_configuration (d1R 0))) \<in> ISR)
  \<and> GL.derivation GL d1L
  \<and> maximum_of_domain d1L n1L
  \<and> dL = derivation_append d1L d2L n1L
  \<and> GL.derivation_initial GL dL
  \<and> derivation_append_fit d1L d2L n1L
  \<and> GR.derivation GR d1R
  \<and> maximum_of_domain d1R n1R
  \<and> dR = derivation_append d1R d2R n1R
  \<and> GR.derivation_initial GR dR
  \<and> derivation_append_fit d1R d2R n1R
  \<longrightarrow> (
  (ANY \<longrightarrow> (LT_ON OR (unmarked_effect1 GL d1L) (unmarked_effect2 GR d1R) \<longrightarrow> (LT_ON OR (unmarked_effect1 GL dL) (unmarked_effect2 GR dR))))
  \<and> (ACCEPT \<longrightarrow> (
  (((marking_condition1 GL d1L) \<longrightarrow> (marking_condition2 GR d1R))
  \<and> (LT_ON OR (marked_effect1 GL d1L) (marked_effect2 GR d1R)))
  \<longrightarrow>
  (((marking_condition1 GL dL) \<longrightarrow> (marking_condition2 GR dR))
  \<and> (LT_ON OR (marked_effect1 GL dL) (marked_effect2 GR dR)))
  ))
  )"

definition preserve_effect_initial :: "bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool" where
  "preserve_effect_initial ANY ACCEPT GL GR OR dL dR \<equiv>
  (ANY \<longrightarrow> LT_ON OR (unmarked_effect1 GL dL) (unmarked_effect2 GR dR))
  \<and> (ACCEPT \<longrightarrow> (
  (LT_ON OR (marked_effect1 GL dL) (marked_effect2 GR dR))
  \<and> ((marking_condition1 GL dL) \<longrightarrow> (marking_condition2 GR dR))
  ))
  "

definition initial_simulation :: "bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> bool" where
  "initial_simulation ANY ACCEPT GL GR SR OR ISR \<equiv> (
  \<forall>c0L\<in> (initial_configurations1 GL).
  \<exists>cnR dR nR eR.
  (c0L,cnR) \<in> SR
  \<and> (\<exists>c0R \<in> (initial_configurations2 GR).
  (c0L,c0R) \<in> ISR
  \<and> GR.derivation GR dR
  \<and> dR 0 = Some (pair None c0R)
  \<and> dR nR = Some (pair eR cnR)
  \<and> maximum_of_domain dR nR
  \<and> preserve_effect_initial ANY ACCEPT GL GR OR (der1 c0L) dR))"

lemma preserve_effect_weakening: "
  preserve_effect p1 p2 GL GR OR SR ISR d2L d2R
  \<Longrightarrow> q1\<longrightarrow>p1
  \<Longrightarrow> q2\<longrightarrow>p2
  \<Longrightarrow> preserve_effect q1 q2 GL GR OR SR ISR d2L d2R"
  apply(simp add: preserve_effect_def)
  apply(force)
  done

lemma preserve_effect_initial_weakening: "
  preserve_effect_initial p1 p2 GL GR OR d2L d2R
  \<Longrightarrow> q1\<longrightarrow>p1
  \<Longrightarrow> q2\<longrightarrow>p2
  \<Longrightarrow> preserve_effect_initial q1 q2 GL GR OR d2L d2R"
  apply(simp add: preserve_effect_initial_def)
  done

lemma initial_simulation_weakening: "
  initial_simulation p1 p2 GL GR SR OR ISR
  \<Longrightarrow> q1\<longrightarrow>p1
  \<Longrightarrow> q2\<longrightarrow>p2
  \<Longrightarrow> initial_simulation q1 q2 GL GR SR OR ISR"
  apply(simp only: initial_simulation_def)
  apply(clarsimp)
  apply(rename_tac c0L)(*strict*)
  apply(erule_tac
      x="c0L"
      in ballE)
   apply(rename_tac c0L)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c0L)(*strict*)
  apply(clarsimp)
  apply(rename_tac c0L cnR dR nR eR c0R)(*strict*)
  apply(rule_tac
      x="cnR"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="dR"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="nR"
      in exI)
  apply(clarsimp)
  apply(rule preserve_effect_initial_weakening)
    apply(rename_tac c0L cnR dR nR eR c0R)(*strict*)
    apply(force)
   apply(rename_tac c0L cnR dR nR eR c0R)(*strict*)
   apply(force)
  apply(rename_tac c0L cnR dR nR eR c0R)(*strict*)
  apply(force)
  done

definition step_simulation :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> bool" where
  "step_simulation BELONGS ACCEPT ANY GL GR SR OR ISR \<equiv>
  (BELONGS \<longrightarrow> (SR \<subseteq> (configurations1 GL)\<times>(configurations2 GR)))
  \<and> (\<forall>cnL cnR cn'L eL.
  (cnL,cnR) \<in> SR
  \<and> step_relation1 GL cnL eL cn'L
  \<longrightarrow> (
  \<exists>eR cn'R dR nR.
  GR.derivation GR dR
  \<and> dR 0 = Some (pair None cnR)
  \<and> dR nR = Some (pair eR cn'R)
  \<and> maximum_of_domain dR nR
  \<and> (cn'L,cn'R) \<in> SR
  \<and> preserve_effect ANY ACCEPT GL GR OR SR ISR (der2 cnL eL cn'L) dR))"

lemma step_simulation_weakening: "
  step_simulation p1 p2 p3 GL GR SR ISR OR
  \<Longrightarrow> q1\<longrightarrow>p1
  \<Longrightarrow> q2\<longrightarrow>p2
  \<Longrightarrow> q3\<longrightarrow>p3
  \<Longrightarrow> step_simulation q1 q2 q3 GL GR SR ISR OR"
  apply(simp only: step_simulation_def)
  apply(rule conjI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(erule_tac
      x="cnL"
      in allE)
  apply(erule_tac
      x="cnR"
      in allE)
  apply(erule_tac
      x="cn'L"
      in allE)
  apply(erule_tac
      x="eL"
      in allE)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL eR cn'R dR nR)(*strict*)
  apply(rule_tac
      x="eR"
      in exI)
  apply(rule_tac
      x="cn'R"
      in exI)
  apply(rule_tac
      x="dR"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="nR"
      in exI)
  apply(clarsimp)
  apply(rule preserve_effect_weakening)
    apply(rename_tac cnL cnR cn'L eL eR cn'R dR nR)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL eR cn'R dR nR)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL eR cn'R dR nR)(*strict*)
  apply(force)
  done

definition simulating_der :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> nat \<Rightarrow> (nat\<Rightarrow>nat) \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool" where
  "simulating_der P_INITIAL P_LANG P_ULANG GL GR SR OR ISR dL nL f dR \<equiv> (
  (if P_INITIAL then
  GL.derivation_initial GL dL \<longrightarrow> GR.derivation_initial GR dR
  else GR.derivation GR dR)
  \<and> mono f
  \<and> ((the(get_configuration (dL 0)),the(get_configuration (dR 0))) \<in> ISR)
  \<and> (\<forall>i eL cL. dL i = Some (pair eL cL) \<longrightarrow>
  (\<exists>eR cR. dR (f i) = Some (pair eR cR) \<and> (cL,cR) \<in> SR)
  \<and> (P_ULANG \<longrightarrow> (LT_ON OR (unmarked_effect1 GL (derivation_take dL i)) (unmarked_effect2 GR (derivation_take dR (f i)))))
  \<and> (P_LANG \<longrightarrow> (
  (marking_condition1 GL (derivation_take dL i)) \<longrightarrow>
  (
  LT_ON OR (marked_effect1 GL (derivation_take dL i)) (marked_effect2 GR (derivation_take dR (f i)))
  \<and> marking_condition2 GR (derivation_take dR (f i))
  ))))
  \<and> maximum_of_domain dR (f nL)
  )"

definition stronger_simulating_der :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'TSstructure1 \<Rightarrow> 'TSstructure2 \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> ('event1 \<times> 'event2) set \<Rightarrow> ('conf1 \<times> 'conf2) set \<Rightarrow> (nat \<Rightarrow> ('label1, 'conf1) derivation_configuration option) \<Rightarrow> nat \<Rightarrow> (nat\<Rightarrow>nat) \<Rightarrow> (nat \<Rightarrow> ('label2, 'conf2) derivation_configuration option) \<Rightarrow> bool" where
  "stronger_simulating_der P_INITIAL P_LANG P_ULANG GL GR SR OR ISR dL nL f dR \<equiv> (
  (if P_INITIAL then
  GL.derivation_initial GL dL \<longrightarrow> GR.derivation_initial GR dR
  else GR.derivation GR dR)
  \<and> ((the(get_configuration (dL 0)),the(get_configuration (dR 0))) \<in> ISR)
  \<and> mono f
  \<and> (\<forall>i eL cL.
  dL i = Some (pair eL cL)
  \<longrightarrow> (\<exists>eR cR.
  dR (f i) = Some (pair eR cR)
  \<and> (cL,cR) \<in> SR)
  \<and> (P_ULANG \<longrightarrow> (LT_ON OR (unmarked_effect1 GL (derivation_take dL i)) (unmarked_effect2 GR (derivation_take dR (f i)))))
  \<and> (P_LANG \<longrightarrow> (
  (LT_ON OR (marked_effect1 GL (derivation_take dL i)) (marked_effect2 GR (derivation_take dR (f i))))
  \<and> ((marking_condition1 GL (derivation_take dL i)) \<longrightarrow> (marking_condition2 GR (derivation_take dR (f i))))
  )))
  \<and> maximum_of_domain dR (f nL)
  )"

lemma simulation_der_weakening: "
  stronger_simulating_der P_INITIAL P_LANG P_ULANG GL GR SR OR ISR dL nL f dR
  \<Longrightarrow> simulating_der P_INITIAL P_LANG P_ULANG GL GR SR OR ISR dL nL f dR"
  apply(simp add: stronger_simulating_der_def simulating_der_def)
  done

lemma generate_simulating_derivation2: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> initial_simulation False True GL GR SR OR ISR
  \<Longrightarrow> step_simulation True True False GL GR SR OR ISR
  \<Longrightarrow> dL 0 = Some (pair None c0L)
  \<Longrightarrow> (c0L,c0R) \<in> SR
  \<Longrightarrow> GL.derivation_initial GL dL
  \<Longrightarrow> maximum_of_domain dL nL
  \<Longrightarrow> \<exists>dR f. stronger_simulating_der True True False GL GR SR OR ISR dL nL f dR"
  apply(simp only: stronger_simulating_der_def)
  apply(clarsimp)
  apply(induct nL arbitrary: dL)
   apply(rename_tac dL)(*strict*)
   apply(simp add: initial_simulation_def)
   apply(erule_tac
      x="c0L"
      in ballE)
    apply(rename_tac dL)(*strict*)
    apply(clarsimp)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    prefer 2
    apply(rename_tac dL)(*strict*)
    apply(simp add: GL.derivation_initial_def)
   apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
   apply(rule_tac
      x="dR"
      in exI)
   apply(rule conjI)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    apply(simp add: GR.derivation_initial_def)
   apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
   apply(rule conjI)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
   apply(rule_tac
      x="\<lambda>n. nR"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    apply(simp add: mono_def)
   apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
   apply(rule_tac
      t="derivation_take dR nR"
      and s="dR"
      in ssubst)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    apply(rule GR.derivation_take_id_prime_prime)
      apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
      apply(force)
     apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
     apply(force)
    apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
    apply(force)
   apply(rename_tac dL cnR dR nR eR c0Ra)(*strict*)
   apply(rule allI)+
   apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(rule impI)+
   apply(subgoal_tac "i\<le>0")
    apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
    prefer 2
    apply(rule_tac
      d="dL"
      in GL.allPreMaxDomSome_prime)
      apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
     apply(force)
    apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
    apply(force)
   apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(clarify)
   apply(rule_tac
      t="derivation_take dL 0"
      and s="dL"
      in ssubst)
    apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
    apply(simp add: derivation_take_def)
    apply(rename_tac dL cnR dR nR eR c0Ra eL cL)(*strict*)
    apply(rule ext)
    apply(rename_tac dL cnR dR nR eR c0Ra eL cL n)(*strict*)
    apply(clarsimp)
    apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
    apply(subgoal_tac "\<forall>m>0. dL m = None")
     apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
     apply(force)
    apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
    apply(rule_tac
      d="dL"
      in GL.noSomeAfterMaxDom)
     apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(force)
    apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
    apply(force)
   apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(subgoal_tac "preserve_effect_initial False True GL GR OR dL dR")
    apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
    prefer 2
    apply(rule_tac
      t="dL"
      and s="der1 c0L"
      in ssubst)
     apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
     apply(simp add: der1_def)
     apply(rename_tac dL cnR dR nR eR c0Ra eL cL)(*strict*)
     apply(rule ext)
     apply(rename_tac dL cnR dR nR eR c0Ra eL cL n)(*strict*)
     apply(clarsimp)
     apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
     apply(subgoal_tac "\<forall>m>0. dL m = None")
      apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
      apply(force)
     apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
     apply(rule_tac
      d="dL"
      in GL.noSomeAfterMaxDom)
      apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac dL cnR dR nR eR c0Ra n)(*strict*)
     apply(force)
    apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
    apply(force)
   apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(thin_tac "preserve_effect_initial False True GL GR OR (der1 c0L) dR")
   apply(rename_tac dL cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(simp only: preserve_effect_initial_def)
   apply(clarsimp)
  apply(rename_tac nL dL)(*strict*)
  apply(erule_tac
      x="derivation_take dL nL"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac nL dL)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nL dL)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac nL dL)(*strict*)
   apply(simp add: GL.derivation_take_preserves_derivation_initial)
  apply(rename_tac nL dL)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac nL dL)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(case_tac "dL nL")
    apply(rename_tac nL dL)(*strict*)
    apply(rule_tac d="dL" in GL.maximum_of_domainSmaller)
       apply(rename_tac nL dL)(*strict*)
       apply(force)
      apply(rename_tac nL dL)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac nL dL)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nL dL)(*strict*)
    apply(force)
   apply(rename_tac nL dL a)(*strict*)
   apply(force)
  apply(rename_tac nL dL)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dL nL = Some (pair e1 c1) \<and> dL (Suc nL) = Some (pair (Some e2) c2) \<and> step_relation1 GL c1 e2 c2")
   apply(rename_tac nL dL dR f)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nL"
      in GL.step_detail_before_some_position)
     apply(rename_tac nL dL dR f)(*strict*)
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac nL dL dR f)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac nL dL dR f)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 c2)(*strict*)
  apply(thin_tac "initial_simulation False True GL GR SR OR ISR")
  apply(subgoal_tac "\<exists>eR cR. dR (f nL) = Some (pair eR cR) \<and> (c1, cR) \<in> SR")
   apply(rename_tac nL dL dR f e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(erule_tac
      x="nL"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule impE)
    apply(rename_tac nL dL dR f e1 e2 c1 c2)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR)(*strict*)
  apply(simp add: step_simulation_def)
  apply(erule conjE)+
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="cR"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule_tac
      x="derivation_append dR dRa (f nL)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation_initial)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(simp add: GR.derivation_initial_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: derivation_append_def)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule_tac
      x="\<lambda>n. if (n\<le>nL) then f n else (f nL + nR)"
      in exI)
  apply(rule conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(simp only: mono_def)
   apply(clarsimp)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR x y)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(subgoal_tac "derivation_append (derivation_take dL nL) (der2 c1 e2 c2) nL = dL")
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      nL="nL"
      in GL.derivation_append_extend_crop_with_last_step)
       apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
       apply(simp add: GL.derivation_initial_def)
       apply(force)
      apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
      apply(force)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule propSym)
  apply(rule conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(clarsimp)
   apply(rule concat_has_max_dom)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(simp add: preserve_effect_def)
  apply(erule_tac
      x="derivation_take dL nL"
      in allE)
  apply(erule_tac
      x="nL"
      and P="\<lambda>n1L. \<forall>d1R n1R. (the (get_configuration (derivation_take dL nL 0)), the (get_configuration (d1R 0))) \<in> ISR \<and> ATS.derivation step_relation1 GL (derivation_take dL nL) \<and> maximum_of_domain (derivation_take dL nL) n1L \<and> ATS.derivation_initial initial_configurations1 step_relation1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) n1L) \<and> derivation_append_fit (derivation_take dL nL) (der2 c1 e2 c2) n1L \<and> ATS.derivation step_relation2 GR d1R \<and> maximum_of_domain d1R n1R \<and> ATS.derivation_initial initial_configurations2 step_relation2 GR (derivation_append d1R dRa n1R) \<and> derivation_append_fit d1R dRa n1R \<longrightarrow> (marking_condition1 GL (derivation_take dL nL) \<longrightarrow> marking_condition2 GR d1R) \<and> LT_ON OR (marked_effect1 GL (derivation_take dL nL)) (marked_effect2 GR d1R) \<longrightarrow> (marking_condition1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) n1L) \<longrightarrow> marking_condition2 GR (derivation_append d1R dRa n1R)) \<and> LT_ON OR (marked_effect1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) n1L)) (marked_effect2 GR (derivation_append d1R dRa n1R))"
      in allE)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(erule_tac
      x="dR"
      in allE)
  apply(erule_tac
      x="f nL"
      and P="\<lambda>n1R. (the (get_configuration (derivation_take dL nL 0)), the (get_configuration (dR 0))) \<in> ISR \<and> ATS.derivation step_relation1 GL (derivation_take dL nL) \<and> maximum_of_domain (derivation_take dL nL) nL \<and> ATS.derivation_initial initial_configurations1 step_relation1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) nL) \<and> derivation_append_fit (derivation_take dL nL) (der2 c1 e2 c2) nL \<and> ATS.derivation step_relation2 GR dR \<and> maximum_of_domain dR n1R \<and> ATS.derivation_initial initial_configurations2 step_relation2 GR (derivation_append dR dRa n1R) \<and> derivation_append_fit dR dRa n1R \<longrightarrow> (marking_condition1 GL (derivation_take dL nL) \<longrightarrow> marking_condition2 GR dR) \<and> LT_ON OR (marked_effect1 GL (derivation_take dL nL)) (marked_effect2 GR dR) \<longrightarrow> (marking_condition1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) nL) \<longrightarrow> marking_condition2 GR (derivation_append dR dRa n1R)) \<and> LT_ON OR (marked_effect1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 c2) nL)) (marked_effect2 GR (derivation_append dR dRa n1R))"
      in allE)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(erule impE)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(rule GL.derivation_take_preserves_derivation)
    apply(simp add: GL.derivation_initial_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule conjI)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule conjI)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_take_def der2_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule conjI)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(simp add: GR.derivation_initial_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule_tac
      t="(derivation_take (derivation_append dR dRa (f nL)) (f nL + nR))"
      and s="(derivation_append dR dRa (f nL))"
      in ssubst)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule_tac
      m="(f nL + nR)"
      and G="GR"
      in GR.derivation_take_id_prime_prime)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(rule concat_has_max_dom)
      apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
      apply(force)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(rule GR.derivation_append_preserves_derivation)
      apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
      apply(simp add: GR.derivation_initial_def)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule allI)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
  apply(rule conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
   apply(clarsimp)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(erule_tac
      x="eL"
      in allE)
   apply(erule_tac
      x="cL"
      in allE)
   apply(erule_tac
      P="derivation_take dL nL i = Some (pair eL cL)"
      in impE)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(clarsimp)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
   apply(rule_tac
      t="derivation_append dR dRa (f nL) (f i)"
      and s="dR (f i)"
      in ssubst)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(subgoal_tac "f i \<le> f nL")
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(simp add: mono_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(derivation_take (derivation_append dR dRa (f nL)) (f i))"
      and s="(derivation_take dR (f i))"
      in ssubst)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(simp add: mono_def)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
   apply(subgoal_tac "derivation_take dL i = (derivation_take (derivation_take dL nL) i)")
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    prefer 2
    apply(rule_tac
      t="derivation_take dL i"
      and s="(derivation_take (derivation_take dL nL) i)"
      in subst)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
     apply(rule derivation_take_twice)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
  apply(subgoal_tac "i=Suc nL")
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   prefer 2
   apply(subgoal_tac "i\<le>Suc nL")
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(rule GL.allPreMaxDomSome_prime)
     apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(simp add: derivation_append_def)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
  apply(subgoal_tac "derivation_take dL (Suc nL) = dL")
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
   prefer 2
   apply(rule GL.derivation_take_id_prime_prime)
     apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
     apply(force)
    apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
    apply(simp add: GL.derivation_initial_def)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="nL"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      P="derivation_take dL nL nL = Some (pair e1 c1)"
      in impE)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "derivation_take (derivation_take dL nL) nL = derivation_take dL nL")
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
   prefer 2
   apply(rule derivation_take_twice)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "derivation_take dR (f nL) = dR")
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
   prefer 2
   apply(rule ext)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(subgoal_tac "\<forall>m>(f nL). dR m = None")
    apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa x)(*strict*)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa x)(*strict*)
   apply(rule_tac
      d="dR"
      in GR.noSomeAfterMaxDom)
    apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa x)(*strict*)
    apply(simp add: GR.derivation_initial_def)
    apply(force)
   apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa x)(*strict*)
   apply(force)
  apply(rename_tac nL dL dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL eRb cRa)(*strict*)
  apply(clarsimp)
  done

lemma generate_simulating_derivation: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> initial_simulation True False GL GR SR OR ISR
  \<Longrightarrow> step_simulation False False True GL GR SR OR ISR
  \<Longrightarrow> dL 0 = Some (pair None c0L)
  \<Longrightarrow> (c0L,c0R) \<in> SR
  \<Longrightarrow> GL.derivation_initial GL dL
  \<Longrightarrow> maximum_of_domain dL nL
  \<Longrightarrow> \<exists>dR f. simulating_der True False True GL GR SR OR ISR dL nL f dR"
  apply(simp only: simulating_der_def)
  apply(induct nL arbitrary: dL c0L c0R)
   apply(rename_tac dL c0L c0R)(*strict*)
   apply(clarsimp)
   apply(simp add: initial_simulation_def)
   apply(erule_tac
      x="c0L"
      in ballE)
    apply(rename_tac dL c0L c0R)(*strict*)
    apply(clarsimp)
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
    prefer 2
    apply(rename_tac dL c0L c0R)(*strict*)
    apply(simp add: GL.derivation_initial_def)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
   apply(rule_tac
      x="dR"
      in exI)
   apply(rule conjI)
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
    apply(simp add: GR.derivation_initial_def)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
   apply(rule_tac
      x="\<lambda>n. nR"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
    apply(simp add: mono_def)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
   apply(rule conjI)
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(subgoal_tac "i\<le>0")
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
    prefer 2
    apply(rule GL.allPreMaxDomSome_prime)
      apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
     apply(force)
    apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
    apply(force)
   apply(rename_tac dL c0L c0R cnR dR nR eR c0Ra i eL cL)(*strict*)
   apply(clarsimp)
   apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
   apply(simp add: preserve_effect_initial_def)
   apply(subgoal_tac "derivation_take dL 0 = dL")
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
    prefer 2
    apply(rule ext)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(simp add: derivation_take_def)
    apply(clarsimp)
    apply(subgoal_tac "\<forall>m>0. dL m = None")
     apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
     apply(force)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(rule_tac
      d="dL"
      in GL.noSomeAfterMaxDom)
     apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(force)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(force)
   apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "derivation_take dR nR = dR")
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
    prefer 2
    apply(rule GR.derivation_take_id_prime_prime)
      apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
      apply(force)
     apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
     apply(force)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
    apply(force)
   apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "der1 cL = dL")
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
    prefer 2
    apply(rule ext)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(simp add: der1_def)
    apply(clarsimp)
    apply(subgoal_tac "\<forall>m>0. dL m = None")
     apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
     apply(force)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(rule_tac
      d="dL"
      in GL.noSomeAfterMaxDom)
     apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(force)
    apply(rename_tac dL c0R cnR dR nR eR c0Ra cL x)(*strict*)
    apply(force)
   apply(rename_tac dL c0R cnR dR nR eR c0Ra cL)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R)(*strict*)
  apply(erule_tac
      x="derivation_take dL nL"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c0L"
      in meta_allE)
  apply(erule_tac
      x="c0R"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac nL dL c0L c0R)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nL dL c0L c0R)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac nL dL c0L c0R)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac nL dL c0L c0R)(*strict*)
   apply(simp add: GL.derivation_take_preserves_derivation_initial)
  apply(rename_tac nL dL c0L c0R)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac nL dL c0L c0R)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(case_tac "dL nL")
    apply(rename_tac nL dL c0L c0R)(*strict*)
    apply(rule GL.maximum_of_domainSmaller)
       apply(rename_tac nL dL c0L c0R)(*strict*)
       apply(force)
      apply(rename_tac nL dL c0L c0R)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac nL dL c0L c0R)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nL dL c0L c0R)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R a)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL c0L c0R dR f)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dL nL = Some (pair e1 c1) \<and> dL (Suc nL) = Some (pair (Some e2) c2) \<and> step_relation1 GL c1 e2 c2")
   apply(rename_tac nL dL c0L c0R dR f)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nL"
      in GL.step_detail_before_some_position)
     apply(rename_tac nL dL c0L c0R dR f)(*strict*)
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac nL dL c0L c0R dR f)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac nL dL c0L c0R dR f)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "derivation_take dL nL nL = Some (pair e1 c1) \<longrightarrow> (\<exists>eR cR. dR (f nL) = Some (pair eR cR) \<and> (c1, cR) \<in> SR)")
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(erule_tac
      x="nL"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(erule_tac
      x="c1"
      in allE)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2)(*strict*)
  apply(erule impE)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR)(*strict*)
  apply(simp add: step_simulation_def)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="cR"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR)(*strict*)
  apply(clarsimp)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule_tac
      x="derivation_append dR dRa (f nL)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation_initial)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(rule GR.derivation_append_preserves_derivation)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
    apply(simp add: GR.derivation_initial_def)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule_tac
      x="\<lambda>n. if (n\<le>nL) then f n else (f nL + nR)"
      in exI)
  apply(rule conjI)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(simp only: mono_def)
   apply(clarsimp)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR x y)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule conjI)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(rule conjI)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(clarsimp)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
   apply(case_tac "i\<le>nL")
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
    apply(clarsimp)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(simp add: derivation_append_def)
     apply(rule conjI)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
      apply(clarsimp)
      apply(erule_tac
      x="i"
      in allE)
      apply(erule_tac
      x="eL"
      in allE)
      apply(erule_tac
      x="cL"
      in allE)
      apply(erule impE)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
       apply(simp add: derivation_take_def)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(simp add: mono_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(erule_tac
      x="eL"
      in allE)
    apply(erule_tac
      x="cL"
      in allE)
    apply(erule impE)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(clarsimp)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(rule_tac
      t="(derivation_take (derivation_append dR dRa (f nL)) (f i))"
      and s="(derivation_take dR (f i))"
      in ssubst)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
     apply(rule derivation_take_derivation_append_ignore)
     apply(simp add: mono_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(subgoal_tac "(derivation_take (derivation_take dL nL) i) = (derivation_take dL i)")
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL eRb cRa)(*strict*)
    apply(rule derivation_take_twice)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i)(*strict*)
   apply(clarsimp)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(subgoal_tac "i=Suc nL")
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    prefer 2
    apply(subgoal_tac "i\<le>Suc nL")
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(rule GL.allPreMaxDomSome_prime)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
      apply(simp add: GL.derivation_initial_def)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(rule conjI)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
    apply(simp add: derivation_append_def)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR i eL cL)(*strict*)
   apply(clarsimp)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(simp add: preserve_effect_def)
   apply(subgoal_tac "derivation_take dL nL nL = Some (pair e1 c1) \<longrightarrow> (\<exists>eR cR. dR (f nL) = Some (pair eR cR) \<and> (c1, cR) \<in> SR) \<and> LT_ON OR (unmarked_effect1 GL (derivation_take (derivation_take dL nL) nL)) (unmarked_effect2 GR (derivation_take dR (f nL)))")
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    prefer 2
    apply(erule_tac
      x="nL"
      in allE)
    apply(erule_tac
      x="e1"
      in allE)
    apply(erule_tac
      x="c1"
      in allE)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(erule impE)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="derivation_take dL nL"
      in allE)
   apply(erule_tac
      x="nL"
      and P="\<lambda>n1L. \<forall>d1R n1R. (the (get_configuration (derivation_take dL nL 0)), the (get_configuration (d1R 0))) \<in> ISR \<and> ATS.derivation step_relation1 GL (derivation_take dL nL) \<and> maximum_of_domain (derivation_take dL nL) n1L \<and> ATS.derivation_initial initial_configurations1 step_relation1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) n1L) \<and> derivation_append_fit (derivation_take dL nL) (der2 c1 e2 cL) n1L \<and> ATS.derivation step_relation2 GR d1R \<and> maximum_of_domain d1R n1R \<and> ATS.derivation_initial initial_configurations2 step_relation2 GR (derivation_append d1R dRa n1R) \<and> derivation_append_fit d1R dRa n1R \<longrightarrow> LT_ON OR (unmarked_effect1 GL (derivation_take dL nL)) (unmarked_effect2 GR d1R) \<longrightarrow> LT_ON OR (unmarked_effect1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) n1L)) (unmarked_effect2 GR (derivation_append d1R dRa n1R))"
      in allE)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(erule_tac
      x="derivation_take dR (f nL)"
      in allE)
   apply(erule_tac
      x="(f nL)"
      and P="\<lambda>n1R. (the (get_configuration (derivation_take dL nL 0)), the (get_configuration (derivation_take dR (f nL) 0))) \<in> ISR \<and> ATS.derivation step_relation1 GL (derivation_take dL nL) \<and> maximum_of_domain (derivation_take dL nL) nL \<and> ATS.derivation_initial initial_configurations1 step_relation1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) nL) \<and> derivation_append_fit (derivation_take dL nL) (der2 c1 e2 cL) nL \<and> ATS.derivation step_relation2 GR (derivation_take dR (f nL)) \<and> maximum_of_domain (derivation_take dR (f nL)) n1R \<and> ATS.derivation_initial initial_configurations2 step_relation2 GR (derivation_append (derivation_take dR (f nL)) dRa n1R) \<and> derivation_append_fit (derivation_take dR (f nL)) dRa n1R \<longrightarrow> LT_ON OR (unmarked_effect1 GL (derivation_take dL nL)) (unmarked_effect2 GR (derivation_take dR (f nL))) \<longrightarrow> LT_ON OR (unmarked_effect1 GL (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) nL)) (unmarked_effect2 GR (derivation_append (derivation_take dR (f nL)) dRa n1R))"
      in allE)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(erule impE)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(subgoal_tac "GL.derivation_initial GL (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) nL)")
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     prefer 2
     apply(rule GL.derivation_append_preserves_derivation_initial)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(force)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(rule GL.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GL.derivation_append_preserves_derivation)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(rule GL.derivation_take_preserves_derivation)
       apply(simp add: GL.derivation_initial_def)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(rule GL.der2_is_derivation)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: derivation_take_def der2_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GL.derivation_take_preserves_derivation)
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GL.derivation_append_preserves_derivation_initial)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(force)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(rule GL.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GL.derivation_append_preserves_derivation)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(rule GL.derivation_take_preserves_derivation)
       apply(simp add: GL.derivation_initial_def)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(rule GL.der2_is_derivation)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: derivation_take_def der2_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_take_def der2_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GR.derivation_take_preserves_derivation)
     apply(simp add: GR.derivation_initial_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GR.derivation_append_preserves_derivation_initial)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(force)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(rule GR.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule GR.derivation_append_preserves_derivation)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(rule GR.derivation_take_preserves_derivation)
       apply(simp add: GR.derivation_initial_def)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_take_def)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(erule impE)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(simp add: LT_ON_def)
    apply(rule_tac
      t="derivation_take dL nL"
      and s="derivation_take (derivation_take dL nL) nL"
      in subst)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(rule derivation_take_twice)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(rule_tac
      t="(derivation_take (derivation_append dR dRa (f nL)) (f nL + nR))"
      and s="(derivation_append (derivation_take dR (f nL)) dRa (f nL))"
      in ssubst)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule GR.derivation_take_derivation_append_distrib)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(subgoal_tac "derivation_take dL (Suc nL) = (derivation_append (derivation_take dL nL) (der2 c1 e2 cL) nL)")
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(rule_tac
      t="derivation_take dL (Suc nL)"
      and s="dL"
      in ssubst)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(rule_tac
      G="GL"
      in GL.derivation_take_id_prime_prime)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(simp add: GL.derivation_initial_def)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(rule GL.derivation_append_extend_crop_with_last_step)
       apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
       apply(simp add: GL.derivation_initial_def)
       apply(force)
      apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
      apply(force)
     apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
     apply(force)
    apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
    apply(force)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 eR cR eRa cn'R dRa nR cL)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(clarsimp)
  apply(rule concat_has_max_dom)
   apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
   apply(force)
  apply(rename_tac nL dL c0L c0R dR f e1 e2 c1 c2 eR cR eRa cn'R dRa nR)(*strict*)
  apply(force)
  done

theorem simulation_implies_unmarked_effect_subset: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> initial_simulation True MARKED GL GR SR OR ISR
  \<Longrightarrow> step_simulation True MARKED True GL GR SR OR ISR
  \<Longrightarrow> w \<in> GL.unmarked_language GL
  \<Longrightarrow> \<exists>v. (w,v)\<in> OR \<and> v \<in> GR.unmarked_language GR"
  apply(subgoal_tac "initial_simulation True False GL GR SR OR ISR")
   prefer 2
   apply(rule initial_simulation_weakening)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "initial_simulation True MARKED GL GR SR OR ISR")
  apply(subgoal_tac "step_simulation True False True GL GR SR OR ISR")
   prefer 2
   apply(rule step_simulation_weakening)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "step_simulation True MARKED True GL GR SR OR ISR")
  apply(subgoal_tac "w \<in> GL.finite_unmarked_language GL")
   prefer 2
   apply(rule_tac
      s="GL.unmarked_language GL"
      and t="GL.finite_unmarked_language GL"
      in ssubst)
    apply(rule GL.AX_unmarked_language_finite)
    apply(force)
   apply(force)
  apply(thin_tac "w \<in> GL.unmarked_language GL")
  apply(rule_tac
      t="GR.unmarked_language GR"
      and s="GR.finite_unmarked_language GR"
      in subst)
   apply(rule GR.AX_unmarked_language_finite)
   apply(force)
  apply(simp add: GL.finite_unmarked_language_def GR.finite_unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule GL.some_position_has_details_at_0)
   apply(simp add: GL.derivation_initial_def)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c)(*strict*)
  apply(subgoal_tac "\<exists>c'. (c,c') \<in> SR")
   apply(rename_tac d x c)(*strict*)
   prefer 2
   apply(simp add: initial_simulation_def)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac d x c)(*strict*)
    apply(clarsimp)
    apply(rename_tac d x c cnR dR nR eR c0R)(*strict*)
    apply(force)
   apply(rename_tac d x c)(*strict*)
   apply(simp add: GL.derivation_initial_def)
  apply(rename_tac d x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c')(*strict*)
  apply(subgoal_tac "\<exists>dR f. simulating_der True False True GL GR SR OR ISR d x f dR")
   apply(rename_tac d x c c')(*strict*)
   prefer 2
   apply(rule generate_simulating_derivation)
          apply(rename_tac d x c c')(*strict*)
          apply(force)+
       apply(rename_tac d x c c')(*strict*)
       apply(rule step_simulation_weakening)
          apply(rename_tac d x c c')(*strict*)
          apply(force)+
  apply(rename_tac d x c c')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c' dR f)(*strict*)
  apply(simp add: simulating_der_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in allE)
  apply(subgoal_tac "\<exists>e c. d x = Some (pair e c)")
   apply(rename_tac d x c c' dR f)(*strict*)
   prefer 2
   apply(rule GL.some_position_has_details_before_max_dom)
     apply(rename_tac d x c c' dR f)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(blast)
    apply(rename_tac d x c c' dR f)(*strict*)
    apply(blast)
   apply(rename_tac d x c c' dR f)(*strict*)
   apply(force)
  apply(rename_tac d x c c' dR f)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(simp add: LT_ON_def)
  apply(erule_tac
      x="w"
      in ballE)
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   apply(clarsimp)
   apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
   apply(rule_tac
      x="y"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_take dR (f x)"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
    apply(rule GR.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
   apply(rule_tac
      x="f x"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(subgoal_tac "derivation_take d x = d")
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   apply(force)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(rule GL.derivation_take_id_prime_prime)
    apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
    apply(force)
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   apply(simp add: GL.derivation_initial_def)
   apply(force)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(force)
  done

theorem simulation_implies_marked_effect_subset: "
  TSstructure1 GL
  \<Longrightarrow> TSstructure2 GR
  \<Longrightarrow> initial_simulation ANY True GL GR SR OR ISR
  \<Longrightarrow> step_simulation True True ANY GL GR SR OR ISR
  \<Longrightarrow> w \<in> GL.marked_language GL
  \<Longrightarrow> \<exists>v. (w,v)\<in> OR \<and> v \<in> GR.marked_language GR"
  apply(subgoal_tac "initial_simulation False True GL GR SR OR ISR")
   prefer 2
   apply(rule initial_simulation_weakening)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "initial_simulation ANY True GL GR SR OR ISR")
  apply(subgoal_tac "step_simulation True True False GL GR SR OR ISR")
   prefer 2
   apply(rule step_simulation_weakening)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "step_simulation True True ANY GL GR SR OR ISR")
  apply(subgoal_tac "w \<in> GL.finite_marked_language GL")
   prefer 2
   apply(rule_tac
      s="GL.marked_language GL"
      and t="GL.finite_marked_language GL"
      in ssubst)
    apply(rule GL.AX_marked_language_finite)
    apply(force)
   apply(force)
  apply(thin_tac "w \<in> GL.marked_language GL")
  apply(rule_tac
      t="GR.marked_language GR"
      and s="GR.finite_marked_language GR"
      in subst)
   apply(rule GR.AX_marked_language_finite)
   apply(force)
  apply(simp add: GL.finite_marked_language_def GR.finite_marked_language_def)
  apply(clarsimp)
  apply(rename_tac d x)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac d x)(*strict*)
   prefer 2
   apply(rule GL.some_position_has_details_at_0)
   apply(simp add: GL.derivation_initial_def)
   apply(force)
  apply(rename_tac d x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c)(*strict*)
  apply(subgoal_tac "\<exists>c'. (c,c') \<in> SR")
   apply(rename_tac d x c)(*strict*)
   prefer 2
   apply(simp add: initial_simulation_def)
   apply(erule_tac
      x="c"
      in ballE)
    apply(rename_tac d x c)(*strict*)
    apply(clarsimp)
    apply(rename_tac d x c cnR dR nR eR c0R)(*strict*)
    apply(force)
   apply(rename_tac d x c)(*strict*)
   apply(simp add: GL.derivation_initial_def)
  apply(rename_tac d x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c')(*strict*)
  apply(subgoal_tac "\<exists>dR f. simulating_der True True False GL GR SR OR ISR d x f dR")
   apply(rename_tac d x c c')(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>dR f. stronger_simulating_der True True False GL GR SR OR ISR d x f dR")
    apply(rename_tac d x c c')(*strict*)
    prefer 2
    apply(rule generate_simulating_derivation2)
           apply(rename_tac d x c c')(*strict*)
           apply(force)+
   apply(rename_tac d x c c')(*strict*)
   apply(clarsimp)
   apply(rename_tac d x c c' dR f)(*strict*)
   apply(rule_tac
      x="dR"
      in exI)
   apply(rule_tac
      x="f"
      in exI)
   apply(rule simulation_der_weakening)
   apply(force)
  apply(rename_tac d x c c')(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c' dR f)(*strict*)
  apply(simp add: simulating_der_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in allE)
  apply(subgoal_tac "\<exists>e c. d x = Some (pair e c)")
   apply(rename_tac d x c c' dR f)(*strict*)
   prefer 2
   apply(rule GL.some_position_has_details_before_max_dom)
     apply(rename_tac d x c c' dR f)(*strict*)
     apply(simp add: GL.derivation_initial_def)
     apply(blast)
    apply(rename_tac d x c c' dR f)(*strict*)
    apply(blast)
   apply(rename_tac d x c c' dR f)(*strict*)
   apply(force)
  apply(rename_tac d x c c' dR f)(*strict*)
  apply(clarsimp)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(subgoal_tac "derivation_take d x = d")
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   prefer 2
   apply(rule GL.derivation_take_id_prime_prime)
     apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
     apply(force)
    apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
    apply(simp add: GL.derivation_initial_def)
    apply(force)
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   apply(force)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(clarsimp)
  apply(simp add: LT_ON_def)
  apply(erule_tac
      x="w"
      in ballE)
   apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
   apply(clarsimp)
   apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
   apply(rule_tac
      x="y"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_take dR (f x)"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
    apply(rule GR.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d x c c' dR f e ca eR cR y)(*strict*)
   apply(rule_tac
      x="f x"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d x c c' dR f e ca eR cR)(*strict*)
  apply(force)
  done

end

end

