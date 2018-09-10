section {*L\_ATS\_Language0*}
theory
  L_ATS_Language0

imports
  L_ATS

begin

locale ATS_Language0 =
  ATS
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  for
    TSstructure configurations initial_configurations step_labels step_relation
    +
  fixes effects :: "'TSstructure \<Rightarrow> 'event set"
  fixes marking_condition :: "'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  fixes marked_effect :: "'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"
  fixes unmarked_effect :: "'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event set"

context ATS_Language0
begin

definition marked_language :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "marked_language G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> marked_effect G d
    \<and> derivation G d
    \<and> marking_condition G d}"

definition marked_languageALT :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "marked_languageALT G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> marked_effect G d
    \<and> marking_condition G d}"

lemma marked_languageALT_equals_marked_language: "
  marked_languageALT G = marked_language G"
  apply(simp add: marked_languageALT_def marked_language_def derivation_initial_def)
  apply(force)
  done

definition finite_marked_language :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "finite_marked_language G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> marked_effect G d
    \<and> marking_condition G d
    \<and> (\<exists>n. maximum_of_domain d n)}"

definition unmarked_language :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "unmarked_language G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> unmarked_effect G d
    \<and> derivation G d}"

definition unmarked_languageALT :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "unmarked_languageALT G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> unmarked_effect G d}"

lemma unmarked_languageALT_equals_unmarked_language: "
  unmarked_languageALT G = unmarked_language G"
  apply(simp add: unmarked_languageALT_def unmarked_language_def derivation_initial_def)
  apply(force)
  done

definition finite_unmarked_language :: "
  'TSstructure
  \<Rightarrow> 'event set"
  where
    "finite_unmarked_language G \<equiv>
  {w. \<exists>d.
    derivation_initial G d
    \<and> w \<in> unmarked_effect G d
    \<and> (\<exists>n. maximum_of_domain d n)}"

definition Nonblockingness_pattern :: "
  'TSstructure
  \<Rightarrow> ('TSstructure \<Rightarrow> ('label,'conf) derivation \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ('TSstructure \<Rightarrow> ('label,'conf) derivation \<Rightarrow> nat \<Rightarrow> ('label,'conf) derivation \<Rightarrow> nat \<Rightarrow> ('label,'conf) derivation \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "Nonblockingness_pattern M Rest Adapt \<equiv>
  \<forall>dh n.
  derivation_initial M dh
  \<longrightarrow> maximum_of_domain dh n
  \<longrightarrow> Rest M dh n
  \<longrightarrow> (\<exists>dh' dc n'.
  Adapt M dh n dc n' dh'
  \<and> derivation M dc
  \<and> belongs M dc
  \<and> maximum_of_domain dc n'
  \<and> derivation_append_fit dh' dc n
  \<and> marking_condition M (derivation_append dh' dc n))"

definition PB_Nonblockingness_NoRest :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_NoRest M dh n \<equiv>
  True"

definition PB_Nonblockingness_NoAdapt :: "
  'TSstructure
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf) derivation
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_NoAdapt G dh nh dc nc dh' \<equiv>
  dh' = dh"

definition PB_Nonblockingness_branching :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "PB_Nonblockingness_branching M \<equiv>
  Nonblockingness_pattern M PB_Nonblockingness_NoRest PB_Nonblockingness_NoAdapt"

definition Nonblockingness_branching :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "Nonblockingness_branching M \<equiv>
  \<forall>dh n.
  derivation_initial M dh
  \<longrightarrow> maximum_of_domain dh n
  \<longrightarrow> (\<exists>dc n'.
        derivation M dc
        \<and> belongs M dc
        \<and> maximum_of_domain dc n'
        \<and> derivation_append_fit dh dc n
        \<and> marking_condition M (derivation_append dh dc n))"

corollary Nonblockingness_branching_vs_PB_Nonblockingness_branching: "
  Nonblockingness_branching M = PB_Nonblockingness_branching M"
  apply(simp add: Nonblockingness_branching_def Nonblockingness_pattern_def PB_Nonblockingness_branching_def PB_Nonblockingness_NoRest_def PB_Nonblockingness_NoAdapt_def)
  done

definition Nonblockingness_configuration :: "
  'TSstructure
  \<Rightarrow> 'conf
  \<Rightarrow> bool"
  where
    "Nonblockingness_configuration M c \<equiv>
  \<exists>d.
  derivation M d
  \<and> belongs M d
  \<and> d 0 = Some (pair None c)
  \<and> marking_condition M d"

definition derivation_livelock :: "'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  where
    "derivation_livelock G d \<equiv>
  derivation_initial G d
  \<and> (\<forall>n. d n \<noteq> None)
  \<and> (\<exists>N. \<forall>n\<ge>N.
  unmarked_effect G (derivation_take d N)
  = unmarked_effect G (derivation_take d n))"

definition has_livelock :: "'TSstructure \<Rightarrow> bool"
  where
    "has_livelock G \<equiv>
  \<exists>d. derivation_livelock G d"

definition initial_marking_derivations :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation set"
  where
    "initial_marking_derivations G \<equiv>
  {d. derivation_initial G d \<and> marking_condition G d}"

lemma initial_marking_derivations_equal_implies_marked_language_equal: "
  generator Gi
  \<Longrightarrow> generator Go
  \<Longrightarrow> initial_marking_derivations Go = initial_marking_derivations Gi
  \<Longrightarrow> (\<And>d. derivation_initial Go d \<Longrightarrow> derivation_initial Gi d \<Longrightarrow> marked_effect Go d = marked_effect Gi d)
  \<Longrightarrow> marked_language Go = marked_language Gi"
  apply(simp add: marked_language_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(subgoal_tac "d \<in> initial_marking_derivations Gi")
    prefer 2
    apply(rule_tac A="initial_marking_derivations Go" in set_mp)
     apply(force)
    apply(simp add: initial_marking_derivations_def)
    apply(force)
   apply(simp add: initial_marking_derivations_def)
   apply(simp add: derivation_initial_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(subgoal_tac "d \<in> initial_marking_derivations Go")
   prefer 2
   apply(rule_tac A="initial_marking_derivations Gi" in set_mp)
    apply(force)
   apply(simp add: initial_marking_derivations_def)
  apply(thin_tac "initial_marking_derivations Go =
           initial_marking_derivations Gi")
  apply(simp add: initial_marking_derivations_def)
  apply(simp add: derivation_initial_def)
  done

end

end
