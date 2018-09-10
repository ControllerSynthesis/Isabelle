section {*L\_ATS*}
theory
  L_ATS

imports
  Derivations_Basics

begin

locale ATS =
  fixes TSstructure :: "'TSstructure \<Rightarrow> bool"
  fixes configurations :: "'TSstructure \<Rightarrow> 'conf set"
  fixes initial_configurations :: "'TSstructure \<Rightarrow> 'conf set"
  fixes step_labels :: "'TSstructure \<Rightarrow> 'label set"
  fixes step_relation :: "'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"

assumes AX_initial_configuration_belongs: "
  TSstructure G
  \<Longrightarrow> initial_configurations G \<subseteq> configurations G"

assumes AX_step_relation_preserves_belongs: "
  TSstructure G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> e \<in> step_labels G \<and> c2 \<in> configurations G"

context ATS
begin

definition is_forward_target_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_target_deterministic G \<equiv>
  \<forall>c c1 c2 e.
  step_relation G c e c1
  \<and> step_relation G c e c2
  \<longrightarrow> c1 = c2"

definition is_forward_edge_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_edge_deterministic G \<equiv>
  \<forall>c c1 c2 e1 e2.
  step_relation G c e1 c1
  \<and> step_relation G c e2 c2
  \<longrightarrow> e1 = e2"

definition is_forward_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_deterministic G \<equiv>
  is_forward_target_deterministic G \<and> is_forward_edge_deterministic G"

definition is_backward_target_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_backward_target_deterministic G \<equiv>
  \<forall>c c1 c2 e.
  step_relation G c1 e c
  \<and> step_relation G c2 e c
  \<longrightarrow> c1 = c2"

definition is_backward_edge_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_backward_edge_deterministic G \<equiv>
  \<forall>c c1 c2 e1 e2.
  step_relation G c1 e1 c
  \<and> step_relation G c2 e2 c
  \<longrightarrow> e1 = e2"

definition is_backward_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_backward_deterministic G \<equiv>
  is_backward_target_deterministic G \<and> is_backward_edge_deterministic G"

definition is_entirely_deterministic :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_entirely_deterministic G \<equiv>
  is_forward_deterministic G \<and> is_backward_deterministic G"

definition derivation :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "derivation G d \<equiv>
  \<forall>i.
  case i of
  0 \<Rightarrow> (
    case d 0 of
    None \<Rightarrow> False
    | Some (pair None c) \<Rightarrow> True
    | Some (pair (Some e) c) \<Rightarrow> False)
  | Suc j \<Rightarrow> (
    case d i of
    None \<Rightarrow> True
    | Some (pair ei ci) \<Rightarrow> (
      case d j of
      None \<Rightarrow> False
      | Some (pair ej cj) \<Rightarrow> (
        case ei of
        None \<Rightarrow> False
        | Some eiv \<Rightarrow> step_relation G cj eiv ci
  )))"

definition derivation_ALT :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "derivation_ALT G d \<equiv>
  (\<exists>c. d 0 = Some (pair None c))
  \<and> (\<forall>j. \<forall>i<j. d j \<noteq> None \<longrightarrow> d i \<noteq> None)
  \<and> (\<forall>i>0. d i \<noteq> None \<longrightarrow> (get_label (d i) \<noteq> None))
  \<and> (\<forall>i e1 c1 e2 c2.
        d i = Some (pair e1 c1)
        \<longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
        \<longrightarrow> step_relation G c1 e2 c2)"

lemma derivation_ALT_vs_derivation_hlp: "
  derivation G d
  \<Longrightarrow> i < j
  \<Longrightarrow> d i = None
  \<Longrightarrow> d j = None"
  apply(induct "j-i" arbitrary: i j)
   apply(rename_tac i j)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac x i j)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i nat)(*strict*)
  apply(erule_tac x="i" in meta_allE)
  apply(erule_tac x="nat" in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i nat)(*strict*)
   apply(force)
  apply(rename_tac x i nat)(*strict*)
  apply(case_tac "i=nat")
   apply(rename_tac x i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac x="Suc nat" in allE)
   apply(clarsimp)
   apply(case_tac "d(Suc nat)")
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac nat a option conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i nat)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_def)
  apply(erule_tac x="Suc nat" in allE)
  apply(clarsimp)
  apply(case_tac "d(Suc nat)")
   apply(rename_tac x i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x i nat a option conf)(*strict*)
  apply(clarsimp)
  done

lemma derivation_ALT_vs_derivation_hlp2: "
  derivation G d
  \<Longrightarrow> i < j
  \<Longrightarrow> d j \<noteq> None
  \<Longrightarrow> d i \<noteq> None"
  apply(induct "j-i" arbitrary: i j)
   apply(rename_tac i j)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y)(*strict*)
  apply(case_tac j)
   apply(rename_tac x i j y)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j y nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i y nat)(*strict*)
  apply(erule_tac x="i" in meta_allE)
  apply(erule_tac x="nat" in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x i y nat)(*strict*)
   apply(force)
  apply(rename_tac x i y nat)(*strict*)
  apply(case_tac "i=nat")
   apply(rename_tac x i y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac y nat)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac x="Suc nat" in allE)
   apply(clarsimp)
   apply(case_tac "d nat")
    apply(rename_tac y nat)(*strict*)
    apply(clarsimp)
    apply(case_tac y)
    apply(rename_tac y nat option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac y nat a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i y nat)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_def)
  apply(erule_tac x="Suc nat" in allE)
  apply(clarsimp)
  apply(case_tac "d nat")
   apply(rename_tac x i y nat)(*strict*)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac x i y nat option conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i y nat a)(*strict*)
  apply(clarsimp)
  done

lemma derivation_ALT_vs_derivation: "
  derivation_ALT G d = derivation G d"
  apply(rule antisym)
   apply(simp add: derivation_ALT_def derivation_def)
   apply(clarsimp)
   apply(rename_tac i c)(*strict*)
   apply(case_tac i)
    apply(rename_tac i c)(*strict*)
    apply(clarsimp)
   apply(rename_tac i c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat)(*strict*)
   apply(case_tac "d(Suc nat)")
    apply(rename_tac c nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac c nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c nat a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat option conf)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac c nat option conf)(*strict*)
    apply(clarsimp)
    apply(erule_tac x="Suc nat" and P="\<lambda>j. \<forall>i. i < j \<longrightarrow> (\<exists>y. d j = Some y) \<longrightarrow> (\<exists>y. d i = Some y)" in allE)
    apply(force)
   apply(rename_tac c nat option conf a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c nat option conf a optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat option conf optiona confa)(*strict*)
   apply(case_tac option)
    apply(rename_tac c nat option conf optiona confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac c nat conf optiona confa)(*strict*)
    apply(erule_tac x="Suc nat" in allE)+
    apply(simp add: get_label_def)
   apply(rename_tac c nat option conf optiona confa a)(*strict*)
   apply(clarsimp)
  apply(simp add: derivation_ALT_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: derivation_def)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac option conf a)(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac j i y)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac j i y)(*strict*)
    prefer 2
    apply(rule derivation_ALT_vs_derivation_hlp2)
      apply(rename_tac j i y)(*strict*)
      apply(force)
     apply(rename_tac j i y)(*strict*)
     apply(force)
    apply(rename_tac j i y)(*strict*)
    apply(force)
   apply(rename_tac j i y)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac i y)(*strict*)
   apply(case_tac i)
    apply(rename_tac i y)(*strict*)
    apply(clarsimp)
   apply(rename_tac i y nat)(*strict*)
   apply(simp add: derivation_def)
   apply(clarsimp)
   apply(rename_tac y nat)(*strict*)
   apply(erule_tac x="Suc nat" in allE)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac y nat option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat option conf)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac nat option conf)(*strict*)
    apply(force)
   apply(rename_tac nat option conf a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac nat option conf a optiona confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat option conf optiona confa)(*strict*)
   apply(case_tac option)
    apply(rename_tac nat option conf optiona confa)(*strict*)
    apply(force)
   apply(rename_tac nat option conf optiona confa a)(*strict*)
   apply(simp add: get_label_def)
  apply(clarsimp)
  apply(rename_tac i e1 c1 e2 c2)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac x="Suc i" in allE)
  apply(clarsimp)
  done

lemma derivation_append_fit_ALT_vs_derivation_append_fit: "
  derivation G g
  \<Longrightarrow>derivation_append_fit_ALT f g n = derivation_append_fit f g n"
  apply(simp add: derivation_append_fit_ALT_def derivation_append_fit_def)
  apply(simp add: get_configuration_def)
  apply(case_tac "f n")
   apply(clarsimp)
   apply(case_tac "g 0")
    apply(clarsimp)
    apply(simp add: derivation_def)
    apply(erule_tac x="0" in allE)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac option conf)(*strict*)
  apply(case_tac "g 0")
   apply(rename_tac option conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac option conf a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac option conf a optiona confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac option conf optiona confa)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac option conf optiona confa)(*strict*)
   apply(clarsimp)
  apply(rename_tac option conf optiona confa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac option confa a)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac x="0" in allE)
  apply(clarsimp)
  done

corollary derivation_introduction: "
  (d 0 \<noteq> None)
  \<Longrightarrow> (\<And>e c. d 0 \<noteq> Some (pair (Some e) c))
  \<Longrightarrow> (\<And>i c. d (Suc i) \<noteq> Some (pair None c))
  \<Longrightarrow> (\<And>i. d (Suc i) \<noteq> None \<longrightarrow> d i \<noteq> None)
  \<Longrightarrow> (\<And>i e1 c1 e2 c2.
        d i = Some (pair e1 c1)
        \<Longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
        \<Longrightarrow> step_relation G c1 e2 c2)
  \<Longrightarrow> derivation G d"
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(case_tac i)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(case_tac y)
   apply(rename_tac y option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac option conf)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac e c)(*strict*)
   apply(case_tac e)
    apply(rename_tac e c)(*strict*)
    apply(force)
   apply(rename_tac e c a)(*strict*)
   apply(force)
  apply(rename_tac y i nat)(*strict*)
  apply(rename_tac y i j)
  apply(rename_tac y i j)(*strict*)
  apply(clarsimp)
  apply(rename_tac y j)(*strict*)
  apply(case_tac "d(Suc j)")
   apply(rename_tac y j)(*strict*)
   apply(force)
  apply(rename_tac y j a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac y j a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac y j option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac y j e c)(*strict*)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac y j e c ya)(*strict*)
  apply(rename_tac ya)
  apply(case_tac "ya")
  apply(rename_tac y j e c ya option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac y j e c option conf)(*strict*)
  apply(rename_tac e1 c1)
  apply(rename_tac y j e c e1 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(thin_tac "(\<And>e c. y \<noteq> pair (Some e) c)")
  apply(case_tac e)
   apply(rename_tac y j e c e1 c1)(*strict*)
   apply(force)
  apply(rename_tac y j e c e1 c1 a)(*strict*)
  apply(clarsimp)
  done

definition derivation_to :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> (('label,'conf)derivation_configuration set)
  \<Rightarrow> bool"
  where
    "derivation_to M f S \<equiv>
  derivation M f
  \<and> (\<exists>n. f (Suc n) = None \<and> (\<exists>y\<in> S. f n = Some y))"

definition derivation_from :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> (('label,'conf)derivation_configuration set)
  \<Rightarrow> bool"
  where
    "derivation_from M f S \<equiv>
  derivation M f
  \<and> (case f 0 of
     None \<Rightarrow> False
     | Some x \<Rightarrow> x \<in> S
  )"

definition derivation_from_to :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> (('label,'conf)derivation_configuration set)
  \<Rightarrow> (('label,'conf)derivation_configuration set)
  \<Rightarrow> bool"
  where
    "derivation_from_to M f S E \<equiv>
  derivation_from M f S
  \<and> derivation_to M f E"

definition derivation_initial :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool" where
  "derivation_initial G d \<equiv>
  derivation G d
  \<and> (case d 0 of
     None \<Rightarrow> False
     | Some (pair e c) \<Rightarrow>
       c \<in> initial_configurations G
       \<and> e = None
  )"

definition derivation_initial_ALT :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool" where
  "derivation_initial_ALT G d \<equiv>
  derivation G d
  \<and> the (get_configuration (d 0)) \<in> initial_configurations G"

lemma derivation_initial_ALT_vs_derivation_initial: "
  derivation_initial_ALT G d = derivation_initial G d"
  apply(rule antisym)
   apply(simp add: derivation_initial_ALT_def derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(simp add: derivation_def)
    apply(erule_tac x="0" in allE)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac option conf)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: derivation_def)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
   apply(case_tac option)
    apply(rename_tac option conf)(*strict*)
    apply(force)
   apply(rename_tac option conf a)(*strict*)
   apply(force)
  apply(simp add: derivation_initial_ALT_def derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac x="0" in allE)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac conf)(*strict*)
  apply(simp add: get_configuration_def)
  done

definition maximal :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "maximal M d \<equiv>
  (\<not>(\<exists>n. maximum_of_domain d n))
  \<or> (\<exists>n e c.
      maximum_of_domain d n
      \<and> d n = Some (pair e c)
      \<and> (\<forall>e' c'. \<not>(step_relation M c e' c')))"

definition belongs :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "belongs M f \<equiv>
  \<forall>i. case f i of
    None \<Rightarrow> True
    | Some (pair e c) \<Rightarrow>
        (case e of
         None \<Rightarrow> True
         | Some e' \<Rightarrow>
           e' \<in> step_labels M)
        \<and> c \<in> configurations M"

definition belongs_ALT :: "
  'TSstructure
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> bool"
  where
    "belongs_ALT G d \<equiv>
  (\<forall>i e c. d i = Some (pair (Some e) c) \<longrightarrow> e \<in> step_labels G)
  \<and> (\<forall>i e c. d i = Some (pair e c) \<longrightarrow> c \<in> configurations G)"

lemma belongs_ALT_vs_belongs: "
  belongs_ALT G d = belongs G d"
  apply(rule antisym)
   apply(simp add: belongs_ALT_def belongs_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac "d i")
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac i a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac i option conf)(*strict*)
   apply(erule_tac x="i" in allE)+
   apply(clarsimp)
   apply(case_tac option)
    apply(rename_tac i option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac i option conf a)(*strict*)
   apply(clarsimp)
  apply(simp add: belongs_ALT_def belongs_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac i e c)(*strict*)
   apply(erule_tac x="i" in allE)+
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(erule_tac x="i" in allE)+
  apply(clarsimp)
  done

definition some_step_from_every_configuration :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "some_step_from_every_configuration M \<equiv>
  \<forall>c\<in> configurations M.
  \<exists>e\<in> step_labels M.
  \<exists>c'\<in> configurations M.
  step_relation M c e c'"

lemma initialNotNone: "
  derivation M f
  \<Longrightarrow> f 0\<noteq>None"
  apply(simp add: derivation_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(auto)
  apply(case_tac "f 0")
   apply(auto)
  done

lemma initialNotNone_prime: "
  derivation M f
  \<Longrightarrow> f 0=None
  \<Longrightarrow>P"
  apply(subgoal_tac "f 0\<noteq>None")
   apply(blast)
  apply(rule initialNotNone)
  apply(blast)
  done

lemma initialNotEdgeSome: "
  derivation M f
  \<Longrightarrow> f 0\<noteq>Some (pair (Some e) c)"
  apply(simp add: derivation_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(auto)
  done

lemma initialNotEdgeSome_prime: "
  derivation M f
  \<Longrightarrow> f 0=Some (pair (Some e) c)
  \<Longrightarrow>P"
  apply(subgoal_tac "f 0\<noteq>Some (pair (Some e) c)")
   apply(blast)
  apply(rule initialNotEdgeSome)
  apply(blast)
  done

lemma some_position_has_details_at_0: "
  derivation M g
  \<Longrightarrow> \<exists>c. g 0 = Some (pair None c)"
  apply(case_tac "g 0")
   apply(rule initialNotNone_prime)
    apply(blast)+
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
  apply(rename_tac b a)(*strict*)
  apply(rule initialNotEdgeSome_prime)
   apply(rename_tac b a)(*strict*)
   apply(blast)+
  done

lemma AX_step_relation_preserves_belongsC: "
  TSstructure G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> c2 \<in> configurations G"
  apply(simp add: AX_step_relation_preserves_belongs)
  done

lemma AX_step_relation_preserves_belongsE: "
  TSstructure G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> e \<in> step_labels G"
  apply(simp add: AX_step_relation_preserves_belongs)
  done

definition get_accessible_configurations :: "
  'TSstructure
  \<Rightarrow> 'conf set"
  where
    "get_accessible_configurations M \<equiv>
  {c. \<exists>d i.
    derivation_initial M d
    \<and> get_configuration (d i) = Some c}"

definition is_forward_target_deterministic_accessible :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_target_deterministic_accessible G \<equiv>
  \<forall>c\<in> get_accessible_configurations G.
  \<forall>c1 c2 e.
  step_relation G c e c1
  \<and> step_relation G c e c2
  \<longrightarrow> c1 = c2"

definition is_forward_edge_deterministic_accessible :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_edge_deterministic_accessible G \<equiv>
  \<forall>c\<in> get_accessible_configurations G.
  \<forall>c1 c2 e1 e2.
  step_relation G c e1 c1
  \<and> step_relation G c e2 c2
  \<longrightarrow> e1 = e2"

definition is_forward_deterministic_accessible :: "
  'TSstructure
  \<Rightarrow> bool"
  where
    "is_forward_deterministic_accessible G \<equiv>
  is_forward_target_deterministic_accessible G \<and> is_forward_edge_deterministic_accessible G"

lemma is_forward_edge_deterministic_implies_is_forward_edge_deterministic_accessible: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministic G
  \<Longrightarrow> is_forward_edge_deterministic_accessible G"
  apply(simp add: is_forward_edge_deterministic_accessible_def is_forward_edge_deterministic_def)
  done

lemma is_forward_target_deterministic_implies_is_forward_target_deterministic_accessible: "
  TSstructure G
  \<Longrightarrow> is_forward_target_deterministic G
  \<Longrightarrow> is_forward_target_deterministic_accessible G"
  apply(simp add: is_forward_target_deterministic_accessible_def is_forward_target_deterministic_def)
  done

lemma is_forward_deterministic_implies_is_forward_deterministic_accessible: "
  TSstructure G
  \<Longrightarrow> is_forward_deterministic G
  \<Longrightarrow> is_forward_deterministic_accessible G"
  apply (metis is_forward_edge_deterministic_implies_is_forward_edge_deterministic_accessible is_forward_target_deterministic_implies_is_forward_target_deterministic_accessible is_forward_deterministic_accessible_def is_forward_deterministic_def)
  done

lemma derivationNoFromNone_prime: "
  derivation M d
  \<Longrightarrow> d (Suc n)=Some a \<longrightarrow> d n\<noteq>None"
  apply(induct n)
   apply(rule impI)
   apply(rule initialNotNone)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc(Suc n)"
      in allE)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(auto)
  apply(rename_tac n)(*strict*)
  apply(case_tac a)
  apply(rename_tac n option b)(*strict*)
  apply(auto)
  done

lemma derivationNoFromNone: "
  derivation M d
  \<Longrightarrow> d (Suc n)=Some a
  \<Longrightarrow> d n=None
  \<Longrightarrow> P"
  apply(subgoal_tac "d (Suc n)=Some a \<longrightarrow> d n\<noteq>None")
   apply(blast)
  apply(rule derivationNoFromNone_prime)
  apply(auto)
  done

lemma noSomeAfterMaxDom: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<forall>m>n. d m = None"
  apply(rule allI)
  apply(rename_tac m)(*strict*)
  apply(induct_tac m)
   apply(rename_tac m)(*strict*)
   apply(auto)
   apply(rename_tac na)(*strict*)
   apply(subgoal_tac "n=na")
    apply(rename_tac na)(*strict*)
    apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac na)(*strict*)
  apply(case_tac "d (Suc na)")
   apply(rename_tac na)(*strict*)
   apply(auto)
  apply(rename_tac na a)(*strict*)
  apply(rule derivationNoFromNone)
    apply(rename_tac na a)(*strict*)
    apply(simp add: derivation_to_def)
   apply(rename_tac na a)(*strict*)
   apply(blast)
  apply(rename_tac na a)(*strict*)
  apply(blast)
  done

lemma none_position_after_max_dom: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> n<m
  \<Longrightarrow> d m = None"
  apply(subgoal_tac "\<forall>m>n. d m=None")
   apply(clarsimp)
  apply(rule noSomeAfterMaxDom)
   apply(force)
  apply(force)
  done

lemma derivationNoFromNone2_prime: "
  derivation M d
  \<Longrightarrow> d n\<noteq>None
  \<Longrightarrow> i<n
  \<Longrightarrow> d i\<noteq>None"
  apply(subgoal_tac "\<forall>i. i\<le>n \<longrightarrow> d (n-i) \<noteq> None")
   apply(subgoal_tac "\<exists>x. i+x=n")
    apply(clarsimp)
    apply(rename_tac y x)(*strict*)
    apply(erule_tac
      x="x"
      in allE)
    apply(clarsimp)
   apply (metis add_diff_inverse order_less_asym)
  apply(rule allI)
  apply(rename_tac ia)(*strict*)
  apply(induct_tac ia)
   apply(rename_tac ia)(*strict*)
   apply(force)
  apply(rename_tac ia na)(*strict*)
  apply(auto)
  apply(rename_tac na y ya)(*strict*)
  apply(case_tac "d (n-Suc na)")
   apply(rename_tac na y ya)(*strict*)
   apply(rule_tac
      a="ya"
      and n="n-Suc na"
      in derivationNoFromNone)
     apply(rename_tac na y ya)(*strict*)
     apply(blast)
    apply(rename_tac na y ya)(*strict*)
    apply(rule_tac
      s="n-na"
      and t="Suc (n - Suc na)"
      in ssubst)
     apply(rename_tac na y ya)(*strict*)
     apply(arith)
    apply(rename_tac na y ya)(*strict*)
    apply(blast)
   apply(rename_tac na y ya)(*strict*)
   apply(blast)
  apply(rename_tac na y ya a)(*strict*)
  apply(blast)
  done

lemma derivationNoFromNone2: "
  derivation M d
  \<Longrightarrow> d n\<noteq>None
  \<Longrightarrow> i<n
  \<Longrightarrow> d i=None
  \<Longrightarrow> P"
  apply(subgoal_tac "d i \<noteq> None")
   apply(force)
  apply(rule derivationNoFromNone2_prime)
    apply(force)+
  done

lemma maximum_of_domainSmaller: "
  maximum_of_domain d m
  \<Longrightarrow> derivation G d
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> d n=None
  \<Longrightarrow> P"
  apply(case_tac "n=m")
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(simp add: maximum_of_domain_def)
  apply(rule_tac
      i="n"
      in derivationNoFromNone2)
     apply(blast)+
   apply(arith)
  apply(blast)
  done

lemma allPreMaxDomSome: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<forall>i\<le>n. d i \<noteq> None"
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i)(*strict*)
   apply(rule maximum_of_domainSmaller)
      apply(rename_tac i)(*strict*)
      apply(blast)+
  done

lemma allPreMaxDomSome_prime: "
  derivation M d
  \<Longrightarrow> d i \<noteq> None
  \<Longrightarrow> maximum_of_domain d (n::nat)
  \<Longrightarrow> i\<le>n"
  apply(subgoal_tac "\<forall>i>n. d i = None")
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac "n<i")
    apply(clarsimp)
   apply(clarsimp)
  apply(rule noSomeAfterMaxDom)
   apply(blast)+
  done

lemma derivation_Always_PreEdge: "
  derivation M d
  \<Longrightarrow> \<forall>c. d(Suc n)\<noteq>Some (pair None c)"
  apply(induct_tac n)
   apply(auto)
   apply(rename_tac c)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc 0"
      in allE)
   apply(auto)
   apply(case_tac "d 0")
    apply(rename_tac c)(*strict*)
    apply(auto)
   apply(rename_tac c a)(*strict*)
   apply(case_tac a)
   apply(rename_tac c a option b)(*strict*)
   apply(auto)
  apply(rename_tac n c)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc (Suc n)"
      in allE)
  apply(auto)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n c)(*strict*)
   apply(auto)
  apply(rename_tac n c a)(*strict*)
  apply(case_tac a)
  apply(rename_tac n c a option b)(*strict*)
  apply(auto)
  done

lemma derivation_Always_PreEdge_prime: "
  derivation M d
  \<Longrightarrow> d (Suc n)=Some (pair None c)
  \<Longrightarrow> P"
  apply(subgoal_tac "\<forall>c. d(Suc n)\<noteq>Some (pair None c)")
   apply(blast)
  apply(rule derivation_Always_PreEdge)
  apply(auto)
  done

lemma pre_some_position_is_some_position: "
  derivation M g
  \<Longrightarrow> g m = Some c
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> \<exists>e c. g n = Some (pair e c)"
  apply(case_tac "n=m")
   apply(auto)
   apply(case_tac m)
    apply(clarsimp)
    apply(case_tac c)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(case_tac c)
   apply(auto)
  apply(subgoal_tac "g n\<noteq>None")
   defer
   apply(rule derivationNoFromNone2_prime)
     apply(blast)+
   apply(arith)
  apply(auto)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(clarsimp)
  done

lemma pre_some_position_is_some_position_prime: "
  derivation M g
  \<Longrightarrow> g m = Some c
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> 0<n
  \<Longrightarrow> \<exists>e c. g n = Some (pair (Some e) c)"
  apply(subgoal_tac "\<exists>e c. g n = Some (pair e c)")
   prefer 2
   apply(rule pre_some_position_is_some_position)
     apply(blast)+
  apply(auto)
  apply(rename_tac e ca)(*strict*)
  apply(case_tac e)
   apply(rename_tac e ca)(*strict*)
   apply(auto)
  apply(rename_tac ca)(*strict*)
  apply(case_tac n)
   apply(rename_tac ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ca nat)(*strict*)
  apply(rule derivation_Always_PreEdge_prime)
   apply(rename_tac ca nat)(*strict*)
   apply(force)
  apply(rename_tac ca nat)(*strict*)
  apply(force)
  done

lemma some_position_has_details_after_0: "
  derivation M g
  \<Longrightarrow> g (Suc n) = Some a
  \<Longrightarrow> \<exists>e c. a = pair (Some e) c"
  apply(case_tac a)
  apply(rename_tac option b)(*strict*)
  apply(auto)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(auto)
  apply(rename_tac b)(*strict*)
  apply(rule derivation_Always_PreEdge_prime)
   apply(rename_tac b)(*strict*)
   apply(blast)+
  done

lemma some_position_has_details_anywhere: "
  derivation M g
  \<Longrightarrow> g n = Some a
  \<Longrightarrow> \<exists>e c. a = pair e c"
  apply(case_tac a)
  apply(rename_tac option b)(*strict*)
  apply(auto)
  done

lemma some_position_at_max_dom: "
  derivation M g
  \<Longrightarrow> maximum_of_domain g n
  \<Longrightarrow> \<exists>e c. g n = Some (pair e c)"
  apply(case_tac "g n")
   apply(rule_tac
      n="n"
      in maximum_of_domainSmaller)
      apply(blast)+
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rule some_position_has_details_anywhere)
   apply(rename_tac a)(*strict*)
   apply(blast)+
  done

lemma some_position_has_details_before_max_dom: "
  derivation M g
  \<Longrightarrow> maximum_of_domain g n
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> \<exists>e c. g m = Some (pair e c)"
  apply(subgoal_tac "\<exists>e c. g n = Some (pair e c)")
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(rule_tac
      m="n"
      in pre_some_position_is_some_position)
     apply(rename_tac e c)(*strict*)
     apply(blast)+
  apply(rule some_position_at_max_dom)
   apply(blast)+
  done

lemma some_position_has_details_before_max_dom_after_0: "
  derivation M g
  \<Longrightarrow> maximum_of_domain g n
  \<Longrightarrow> Suc m\<le>n
  \<Longrightarrow> \<exists>e c. g (Suc m) = Some (pair (Some e) c)"
  apply(subgoal_tac "\<exists>e c. g n=Some (pair e c)")
   apply(subgoal_tac "\<exists>e c. g (Suc m) = Some (pair e c)")
    apply(clarsimp)
    apply(rename_tac e ea c ca)(*strict*)
    apply(case_tac ea)
     apply(rename_tac e ea c ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac e c ca)(*strict*)
     apply(rule derivation_Always_PreEdge_prime)
      apply(rename_tac e c ca)(*strict*)
      apply(blast)+
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(rule_tac
      m="n"
      in pre_some_position_is_some_position)
     apply(rename_tac e c)(*strict*)
     apply(blast)+
  apply(rule some_position_at_max_dom)
   apply(blast)+
  done

lemma hasPreciseElem: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> Suc k\<le>n
  \<Longrightarrow> \<exists>e1 c1. d (Suc k)=Some (pair (Some e1) c1)"
  apply(rule some_position_has_details_before_max_dom_after_0)
    apply(blast)+
  apply(arith)
  done

lemma sameget_configurationigSame: "
  d i = Some (pair e1 x)
  \<Longrightarrow> d i = Some (pair e2 y)
  \<Longrightarrow> x=y"
  apply(force)
  done

lemma existence_of_earliest_satisfaction_point: "
  derivation M d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> P c
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not>(\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P c)) i) & ((\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P c)))k"
  apply(case_tac "d 0")
   apply(rule initialNotNone_prime)
    apply(force)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "P b")
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(rule ex_least_nat_le)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(force)
  done

lemma position_change_due_to_step_relation: "
  derivation M d
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d (Suc n) = Some (pair (Some e2) c2)
  \<Longrightarrow> step_relation M c1 e2 c2"
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(auto)
  done

lemma step_detail_before_some_position: "
  derivation G d
  \<Longrightarrow> d m \<noteq> None
  \<Longrightarrow> Suc n \<le> m
  \<Longrightarrow> \<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2"
  apply(case_tac "d m")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(rename_tac a e ea c ca)(*strict*)
    apply(rule position_change_due_to_step_relation)
      apply(rename_tac a e ea c ca)(*strict*)
      apply(force)+
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      m="m"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac a)(*strict*)
      apply(force)+
  apply(rename_tac a)(*strict*)
  apply(rule_tac
      m="m"
      in pre_some_position_is_some_position)
    apply(rename_tac a)(*strict*)
    apply(force)+
  done

lemma noDeadEndBeforeMaxDom: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d m=Some (pair e1 c1)
  \<Longrightarrow> m<n
  \<Longrightarrow> \<forall>e2 c2. \<not>(step_relation M c1 e2 c2)
  \<Longrightarrow> P"
  apply(case_tac "d (Suc m)")
   apply(rule_tac
      n="Suc m"
      in maximum_of_domainSmaller)
      apply(blast)
     apply(blast)
    apply(arith)
   apply(blast)
  apply(rename_tac a)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc m"
      in allE)
  apply(auto)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(auto)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(auto)
  done

lemma stepOnlyDueToStepRelation: "
  maximum_of_domain d n
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d i = Some (pair e1 c1)
  \<Longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
  \<Longrightarrow> step_relation G c1 e2 c2"
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(auto)
  done

lemma use_is_forward_deterministic_E: "
  is_forward_deterministic M
  \<Longrightarrow> step_relation M c1 e1 c2
  \<Longrightarrow> step_relation M c1 e2 c3
  \<Longrightarrow> e1=e2"
  apply(simp add: is_forward_deterministic_def is_forward_edge_deterministic_def)
  done

lemma use_is_forward_deterministic_T: "
  is_forward_deterministic M
  \<Longrightarrow> step_relation M c1 e1 c2
  \<Longrightarrow> step_relation M c1 e2 c3
  \<Longrightarrow> c2=c3"
  apply(subgoal_tac "e1=e2")
   prefer 2
   apply(rule use_is_forward_deterministic_E)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: is_forward_deterministic_def is_forward_target_deterministic_def)
  apply(auto)
  done

lemma supCFGhasAllFromToDerisOfsub: "
  \<forall>c1 e c2. step_relation M1 c1 e c2 \<longrightarrow> step_relation M2 c1 e c2
  \<Longrightarrow> derivation M1 d
  \<Longrightarrow> derivation M2 d"
  apply(simp add: derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat option b)(*strict*)
   apply(auto)
  apply(rename_tac nat option b a)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac "option")
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  done

lemma derivationsCoincide: "
  is_forward_deterministic M
  \<Longrightarrow> derivation M d1
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> d1 0=Some (pair None c)
  \<Longrightarrow> d1 n=Some (pair e1 c1)
  \<Longrightarrow> derivation M d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> d2 0=Some (pair None c)
  \<Longrightarrow> d2 n=Some (pair e2 c2)
  \<Longrightarrow> d1=d2"
  apply(rule HOL.ext)
  apply(rename_tac x)(*strict*)
  apply(induct_tac x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x na)(*strict*)
  apply(subgoal_tac "\<forall>m>n. d1 m = None")
   apply(rename_tac x na)(*strict*)
   prefer 2
   apply(rule noSomeAfterMaxDom)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(blast)
  apply(rename_tac x na)(*strict*)
  apply(subgoal_tac "\<forall>m>n. d2 m = None")
   apply(rename_tac x na)(*strict*)
   prefer 2
   apply(rule noSomeAfterMaxDom)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(blast)
  apply(rename_tac x na)(*strict*)
  apply(case_tac "Suc na\<le>n")
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 na = Some (pair e c)")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom)
      apply(rename_tac x na)(*strict*)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(force)
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e1'' c1''. d1 (Suc na) = Some (pair (Some e1'') c1'')")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x na)(*strict*)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e2'' c2''. d2 (Suc na) = Some (pair (Some e2'') c2'')")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x na)(*strict*)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(erule exE)+
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(subgoal_tac "step_relation M ca e1'' c1''")
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    prefer 2
    apply(rule_tac
      n="na"
      in position_change_due_to_step_relation)
      apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
      apply(blast)
     apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
     apply(blast)
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(force)
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(subgoal_tac "step_relation M ca e2'' c2''")
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="na"
      and ?e1.0="e"
      in position_change_due_to_step_relation)
      apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
      apply(blast)
     apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
     apply(force)
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(blast)
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(simp add: is_forward_deterministic_def)
   apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(simp add: is_forward_edge_deterministic_def)
   apply(erule conjE)
   apply(erule_tac
      x="ca"
      in allE)
   apply(erule_tac
      x="c1''"
      in allE)
   apply(erule_tac
      x="c2''"
      in allE)
   apply(erule_tac
      x="e1''"
      in allE)
   apply(erule_tac
      x="e2''"
      in allE)
   apply(erule impE)
    apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(clarsimp)
   apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(clarsimp)
   apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
   apply(simp add: is_forward_target_deterministic_def)
   apply(erule_tac
      x="ca"
      in allE)
   apply(erule_tac
      x="c1''"
      in allE)
   apply(erule_tac
      x="c2''"
      in allE)
   apply(erule impE)
    apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
    apply(rule_tac
      x="e2''"
      in exI)
    apply(clarsimp)
   apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
   apply(clarsimp)
  apply(rename_tac x na)(*strict*)
  apply(erule_tac
      x="Suc na"
      in allE)+
  apply(force)
  done

lemma derivation_initial_is_derivation: "
  derivation_initial G d
  \<Longrightarrow> derivation G d"
  apply(simp add: derivation_initial_def)
  done

lemma derivationsCoincideR: "
  is_forward_deterministic_accessible M
  \<Longrightarrow> derivation M d1
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> d1 0=Some (pair None c)
  \<Longrightarrow> d1 n=Some (pair e1 c1)
  \<Longrightarrow> derivation_initial M d2
  \<Longrightarrow> maximum_of_domain d2 n
  \<Longrightarrow> d2 0=Some (pair None c)
  \<Longrightarrow> d2 n=Some (pair e2 c2)
  \<Longrightarrow> d1=d2"
  apply(rule HOL.ext)
  apply(rename_tac x)(*strict*)
  apply(induct_tac x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x na)(*strict*)
  apply(subgoal_tac "\<forall>m>n. d1 m = None")
   apply(rename_tac x na)(*strict*)
   prefer 2
   apply(rule noSomeAfterMaxDom)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(blast)
  apply(rename_tac x na)(*strict*)
  apply(subgoal_tac "\<forall>m>n. d2 m = None")
   apply(rename_tac x na)(*strict*)
   prefer 2
   apply(rule noSomeAfterMaxDom)
    apply(rename_tac x na)(*strict*)
    apply(rule derivation_initial_is_derivation)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(blast)
  apply(rename_tac x na)(*strict*)
  apply(case_tac "Suc na\<le>n")
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 na = Some (pair e c)")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom)
      apply(rename_tac x na)(*strict*)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(force)
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e1'' c1''. d1 (Suc na) = Some (pair (Some e1'') c1'')")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x na)(*strict*)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(subgoal_tac "\<exists>e2'' c2''. d2 (Suc na) = Some (pair (Some e2'') c2'')")
    apply(rename_tac x na)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x na)(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(blast)
     apply(rename_tac x na)(*strict*)
     apply(blast)
    apply(rename_tac x na)(*strict*)
    apply(blast)
   apply(rename_tac x na)(*strict*)
   apply(erule exE)+
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(subgoal_tac "step_relation M ca e1'' c1''")
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    prefer 2
    apply(rule_tac
      n="na"
      in position_change_due_to_step_relation)
      apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
      apply(blast)
     apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
     apply(blast)
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(force)
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(subgoal_tac "step_relation M ca e2'' c2''")
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    prefer 2
    apply(rule_tac
      d="d2"
      and n="na"
      and ?e1.0="e"
      in position_change_due_to_step_relation)
      apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
      apply(rule derivation_initial_is_derivation)
      apply(blast)
     apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
     apply(force)
    apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(blast)
   apply(rename_tac x na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(simp add: is_forward_deterministic_accessible_def)
   apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(simp add: is_forward_edge_deterministic_accessible_def)
   apply(erule conjE)
   apply(erule_tac
      x="ca"
      in ballE)
    apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(erule_tac
      x="c1''"
      in allE)
    apply(erule_tac
      x="c2''"
      in allE)
    apply(erule_tac
      x="e1''"
      in allE)
    apply(erule_tac
      x="e2''"
      in allE)
    apply(erule impE)
     apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
     apply(clarsimp)
    apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(clarsimp)
    apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
    apply(simp add: is_forward_target_deterministic_accessible_def)
    apply(erule_tac
      x="ca"
      in ballE)
     apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
     apply(erule_tac
      x="c1''"
      in allE)
     apply(erule_tac
      x="c2''"
      in allE)
     apply(erule impE)
      apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
      apply(rule_tac
      x="e2''"
      in exI)
      apply(clarsimp)
     apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
     apply(clarsimp)
    apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
    apply(simp add: get_accessible_configurations_def)
    apply(erule_tac
      x="d2"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="na"
      and P="\<lambda>i. get_configuration (d2 i) \<noteq> Some ca"
      in allE)
    apply(simp add: get_configuration_def)
    apply(case_tac "d2 na")
     apply(rename_tac na e e2'' ca c1'' c2'')(*strict*)
     apply(force)
    apply(rename_tac na e e2'' ca c1'' c2'' a)(*strict*)
    apply(force)
   apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
   apply(simp add: get_accessible_configurations_def)
   apply(erule_tac
      x="d2"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="na"
      and P="\<lambda>i. get_configuration (d2 i) \<noteq> Some ca"
      in allE)
   apply(simp add: get_configuration_def)
   apply(case_tac "d2 na")
    apply(rename_tac na e e1'' e2'' ca c1'' c2'')(*strict*)
    apply(force)
   apply(rename_tac na e e1'' e2'' ca c1'' c2'' a)(*strict*)
   apply(force)
  apply(rename_tac x na)(*strict*)
  apply(force)
  done

lemma property_preseved_under_steps_is_invariant2: "
  derivation G d
  \<Longrightarrow> P (d m)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<forall>i. m\<le>i \<and> i<m + n \<and> P (d i) \<longrightarrow> P (d (Suc i))
  \<Longrightarrow> P (d x)"
  apply(subgoal_tac "\<forall>k. (k\<ge>m \<and> k \<le> m+n \<longrightarrow> P (d k))")
   apply(blast)
  apply(rule allI)
  apply(rename_tac k)(*strict*)
  apply(induct_tac k)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
  apply(rename_tac k na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na)(*strict*)
  apply(case_tac "m \<le> na")
   apply(rename_tac na)(*strict*)
   apply(auto)
  apply(rename_tac na)(*strict*)
  apply(subgoal_tac "m=Suc na")
   apply(rename_tac na)(*strict*)
   defer
   apply(auto)
  done

lemma later_in_configuration_label: "
  TSstructure M
  \<Longrightarrow> derivation M d
  \<Longrightarrow> d m = Some (pair me mc)
  \<Longrightarrow> mc \<in> configurations M
  \<Longrightarrow> m<n
  \<Longrightarrow> d n = Some (pair (Some ne) nc)
  \<Longrightarrow> ne \<in> step_labels M \<and> nc \<in> configurations M"
  apply(subgoal_tac "\<forall>nc ne. d n = Some (pair (Some ne) nc) \<longrightarrow> (ne \<in> step_labels M \<and> nc\<in> configurations M)")
   apply(force)
  apply(rule_tac
      m="Suc m"
      and x="n"
      and n="n"
      in property_preseved_under_steps_is_invariant2)
      apply(force)
     apply(clarsimp)
     apply(rename_tac nca nea)(*strict*)
     apply(subgoal_tac "step_relation M mc nea nca")
      apply(rename_tac nca nea)(*strict*)
      prefer 2
      apply(rule position_change_due_to_step_relation)
        apply(rename_tac nca nea)(*strict*)
        apply(blast)+
     apply(rename_tac nca nea)(*strict*)
     apply(rule AX_step_relation_preserves_belongs)
       apply(rename_tac nca nea)(*strict*)
       apply(force)
      apply(rename_tac nca nea)(*strict*)
      apply(force)
     apply(rename_tac nca nea)(*strict*)
     apply(force)
    apply(arith)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i nca nea)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i nca nea)(*strict*)
   apply(rule_tac
      i="i"
      and n="Suc i"
      in derivationNoFromNone2)
      apply(rename_tac i nca nea)(*strict*)
      apply(force)
     apply(rename_tac i nca nea)(*strict*)
     apply(force)
    apply(rename_tac i nca nea)(*strict*)
    apply(force)
   apply(rename_tac i nca nea)(*strict*)
   apply(force)
  apply(rename_tac i nca nea a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i nca nea a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i nca nea option b)(*strict*)
  apply(case_tac i)
   apply(rename_tac i nca nea option b)(*strict*)
   apply(force)
  apply(rename_tac i nca nea option b nat)(*strict*)
  apply(case_tac option)
   apply(rename_tac i nca nea option b nat)(*strict*)
   apply(rule_tac derivation_Always_PreEdge_prime)
    apply(rename_tac i nca nea option b nat)(*strict*)
    apply(force)
   apply(rename_tac i nca nea option b nat)(*strict*)
   apply(force)
  apply(rename_tac i nca nea option b nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nca nea b nat a)(*strict*)
  apply(subgoal_tac "step_relation M b nea nca")
   apply(rename_tac nca nea b nat a)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac nca nea b nat a)(*strict*)
     apply(blast)+
  apply(rename_tac nca nea b nat a)(*strict*)
  apply(rule AX_step_relation_preserves_belongs)
    apply(rename_tac nca nea b nat a)(*strict*)
    apply(force)
   apply(rename_tac nca nea b nat a)(*strict*)
   apply(force)
  apply(rename_tac nca nea b nat a)(*strict*)
  apply(force)
  done

lemma stays_in_configuration: "
  TSstructure M
  \<Longrightarrow> derivation M d
  \<Longrightarrow> d m = Some (pair me mc)
  \<Longrightarrow> mc \<in> configurations M
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> d n = Some (pair ne nc)
  \<Longrightarrow> nc \<in> configurations M"
  apply(subgoal_tac "\<forall>nc ne. d n = Some (pair ne nc) \<longrightarrow> nc \<in> configurations M")
   apply(force)
  apply(rule_tac
      m="m"
      and x="n"
      and n="n"
      in property_preseved_under_steps_is_invariant2)
      apply(force)
     apply(clarsimp)
    apply(blast)
   apply(arith)
  apply(clarsimp)
  apply(rename_tac i nca nea)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i nca nea)(*strict*)
   apply(rule_tac
      i="i"
      and n="Suc i"
      in derivationNoFromNone2)
      apply(rename_tac i nca nea)(*strict*)
      apply(force)
     apply(rename_tac i nca nea)(*strict*)
     apply(force)
    apply(rename_tac i nca nea)(*strict*)
    apply(force)
   apply(rename_tac i nca nea)(*strict*)
   apply(force)
  apply(rename_tac i nca nea a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i nca nea a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i nca nea option b)(*strict*)
  apply(case_tac nea)
   apply(rename_tac i nca nea option b)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac i nca nea option b)(*strict*)
    apply(force)
   apply(rename_tac i nca nea option b)(*strict*)
   apply(force)
  apply(rename_tac i nca nea option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i nca option b a)(*strict*)
  apply(subgoal_tac "step_relation M b a nca")
   apply(rename_tac i nca option b a)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac i nca option b a)(*strict*)
     apply(blast)+
  apply(rename_tac i nca option b a)(*strict*)
  apply(subgoal_tac "a \<in> step_labels M \<and> nca \<in> configurations M")
   apply(rename_tac i nca option b a)(*strict*)
   apply(force)
  apply(rename_tac i nca option b a)(*strict*)
  apply(rule AX_step_relation_preserves_belongs)
    apply(rename_tac i nca option b a)(*strict*)
    apply(force)
   apply(rename_tac i nca option b a)(*strict*)
   apply(force)
  apply(rename_tac i nca option b a)(*strict*)
  apply(force)
  done

lemma property_preseved_under_steps_is_invariant2_rev: "
  derivation G d
  \<Longrightarrow> P (d m)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<forall>i. m\<le>i \<and> i<m + n \<and> P (d i) \<longrightarrow> P (d (Suc i))
  \<Longrightarrow> P (d x)"
  apply(subgoal_tac "\<forall>k. (k\<ge>m \<and> k \<le> m+n \<longrightarrow> P (d k))")
   apply(blast)
  apply(rule allI)
  apply(rename_tac k)(*strict*)
  apply(induct_tac k)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
  apply(rename_tac k na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na)(*strict*)
  apply(case_tac "m \<le> na")
   apply(rename_tac na)(*strict*)
   apply(auto)
  apply(rename_tac na)(*strict*)
  apply(subgoal_tac "m=Suc na")
   apply(rename_tac na)(*strict*)
   defer
   apply(auto)
  done

lemma derivation_injective: "
  is_backward_target_deterministic M
  \<Longrightarrow> derivation M d1
  \<Longrightarrow> derivation M d2
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> d1 0 = Some (pair None c1)
  \<Longrightarrow> d2 0 = Some (pair None c2)
  \<Longrightarrow> c1 \<in> configurations M
  \<Longrightarrow> c2 \<in> configurations M
  \<Longrightarrow> d1 n1 = Some (pair e1 cfin)
  \<Longrightarrow> d2 n2 = Some (pair e2 cfin)
  \<Longrightarrow> \<forall>c c1 c2 e1 e2. (Some c \<in> set(get_configurations d1 n1)) \<and> (step_relation M c1 e1 c) \<and> (step_relation M c2 e2 c) \<longrightarrow> e1=e2
  \<Longrightarrow> \<forall>c' e. \<not> (step_relation M c' e c1)
  \<Longrightarrow> \<forall>c' e. \<not> (step_relation M c' e c2)
  \<Longrightarrow> c1=c2"
  apply(subgoal_tac "\<forall>i. i\<le>n1 \<and> i\<le>n2 \<longrightarrow> get_configuration (d1 (n1-i)) = get_configuration (d2 (n2-i))")
   apply(case_tac "n1=n2")
    apply(erule_tac
      x="n1"
      in allE)
    apply(simp add: get_configuration_def)
   apply(subgoal_tac "n1<n2 \<or> n2<n1")
    prefer 2
    apply(clarsimp)
   apply(erule disjE)
    apply(erule_tac
      x="n1"
      in allE)
    apply(erule impE)
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>npre. Suc npre=n2-n1")
     prefer 2
     apply (metis gr0_conv_Suc zero_less_diff)
    apply(erule exE)+
    apply(rename_tac npre)(*strict*)
    apply(subgoal_tac "\<exists>e c. d2 (Suc npre) = Some (pair (Some e) c)")
     apply(rename_tac npre)(*strict*)
     prefer 2
     apply(rule_tac some_position_has_details_before_max_dom_after_0)
       apply(rename_tac npre)(*strict*)
       apply(force)
      apply(rename_tac npre)(*strict*)
      apply(force)
     apply(rename_tac npre)(*strict*)
     apply(force)
    apply(rename_tac npre)(*strict*)
    apply(erule exE)+
    apply(rename_tac npre e c)(*strict*)
    apply(subgoal_tac "\<exists>e c. d2 npre = Some (pair e c)")
     apply(rename_tac npre e c)(*strict*)
     prefer 2
     apply(rule_tac some_position_has_details_before_max_dom)
       apply(rename_tac npre e c)(*strict*)
       apply(force)
      apply(rename_tac npre e c)(*strict*)
      apply(force)
     apply(rename_tac npre e c)(*strict*)
     apply(force)
    apply(rename_tac npre e c)(*strict*)
    apply(erule exE)+
    apply(rename_tac npre e c ea ca)(*strict*)
    apply(subgoal_tac "step_relation M ca e c")
     apply(rename_tac npre e c ea ca)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2"
      in position_change_due_to_step_relation)
       apply(rename_tac npre e c ea ca)(*strict*)
       apply(force)
      apply(rename_tac npre e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac npre e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac npre e c ea ca)(*strict*)
    apply(erule_tac
      x="ca"
      and P="\<lambda>ca. \<forall>e. \<not> step_relation M ca e c1"
      in allE)
    apply(erule_tac
      x="e"
      in allE)
    apply(simp add: get_configuration_def)
   apply(erule_tac
      x="n2"
      in allE)
   apply(erule impE)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>npre. Suc npre=n1-n2")
    prefer 2
    apply (metis gr0_conv_Suc zero_less_diff)
   apply(erule exE)+
   apply(rename_tac npre)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 (Suc npre) = Some (pair (Some e) c)")
    apply(rename_tac npre)(*strict*)
    prefer 2
    apply(rule_tac some_position_has_details_before_max_dom_after_0)
      apply(rename_tac npre)(*strict*)
      apply(force)
     apply(rename_tac npre)(*strict*)
     apply(force)
    apply(rename_tac npre)(*strict*)
    apply(force)
   apply(rename_tac npre)(*strict*)
   apply(erule exE)+
   apply(rename_tac npre e c)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 npre = Some (pair e c)")
    apply(rename_tac npre e c)(*strict*)
    prefer 2
    apply(rule_tac some_position_has_details_before_max_dom)
      apply(rename_tac npre e c)(*strict*)
      apply(force)
     apply(rename_tac npre e c)(*strict*)
     apply(force)
    apply(rename_tac npre e c)(*strict*)
    apply(force)
   apply(rename_tac npre e c)(*strict*)
   apply(erule exE)+
   apply(rename_tac npre e c ea ca)(*strict*)
   apply(subgoal_tac "step_relation M ca e c")
    apply(rename_tac npre e c ea ca)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      in position_change_due_to_step_relation)
      apply(rename_tac npre e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac npre e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac npre e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac npre e c ea ca)(*strict*)
   apply(erule_tac
      x="ca"
      and P="\<lambda>ca. \<forall>e. \<not> step_relation M ca e c1"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(simp add: get_configuration_def)
  apply(rule allI)
  apply(rename_tac i)(*strict*)
  apply(induct_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac i n)(*strict*)
  apply(rule impI)
  apply(erule conjE)
  apply(erule impE)
   apply(rename_tac i n)(*strict*)
   apply(clarsimp)
  apply(rename_tac i n)(*strict*)
  apply(subgoal_tac "\<exists>n1p. Suc n1p=n1-n")
   apply(rename_tac i n)(*strict*)
   prefer 2
   apply (metis Suc_le_lessD gr0_conv_Suc zero_less_diff)
  apply(rename_tac i n)(*strict*)
  apply(subgoal_tac "\<exists>n2p. Suc n2p=n2-n")
   apply(rename_tac i n)(*strict*)
   prefer 2
   apply(case_tac "n2-n")
    apply(rename_tac i n)(*strict*)
    apply(clarsimp)
   apply(rename_tac i n nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i n)(*strict*)
  apply(erule exE)+
  apply(rename_tac i n n1p n2p)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 (Suc n1p) = Some (pair (Some e) c)")
   apply(rename_tac i n n1p n2p)(*strict*)
   prefer 2
   apply(rule_tac some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i n n1p n2p)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p)(*strict*)
   apply(force)
  apply(rename_tac i n n1p n2p)(*strict*)
  apply(erule exE)+
  apply(rename_tac i n n1p n2p e c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 n1p = Some (pair e c)")
   apply(rename_tac i n n1p n2p e c)(*strict*)
   prefer 2
   apply(rule_tac some_position_has_details_before_max_dom)
     apply(rename_tac i n n1p n2p e c)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p e c)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c)(*strict*)
   apply(force)
  apply(rename_tac i n n1p n2p e c)(*strict*)
  apply(erule exE)+
  apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (Suc n2p) = Some (pair (Some e) c)")
   apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
   prefer 2
   apply(rule_tac some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac i n n1p n2p e c ea ca)(*strict*)
  apply(erule exE)+
  apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 n2p = Some (pair e c)")
   apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
   prefer 2
   apply(rule_tac some_position_has_details_before_max_dom)
     apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
   apply(force)
  apply(rename_tac i n n1p n2p e c ea ca eb cb)(*strict*)
  apply(erule exE)+
  apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
  apply(erule_tac
      x="c"
      and P="\<lambda>c. \<forall>c1 c2 e1 e2. Some c \<in> set (get_configurations d1 n1) \<and> step_relation M c1 e1 c \<and> step_relation M c2 e2 c \<longrightarrow> e1 = e2"
      in allE)
  apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
  apply(erule_tac
      x="ca"
      and P="\<lambda>ca. \<forall>c2 e1 e2. Some c \<in> set (get_configurations d1 n1) \<and> step_relation M ca e1 c \<and> step_relation M c2 e2 c \<longrightarrow> e1 = e2"
      in allE)
  apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
  apply(erule_tac
      x="cc"
      and P="\<lambda>cc. \<forall>e1 e2. Some c \<in> set (get_configurations d1 n1) \<and> step_relation M ca e1 c \<and> step_relation M cc e2 c \<longrightarrow> e1 = e2"
      in allE)
  apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="eb"
      in allE)
  apply(erule impE)
   apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(simp add: get_configurations_def)
    apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="Suc n1p"
      in bexI)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(rule_tac
      t="Suc n1p \<in> set (nat_seq 0 n1)"
      and s="(\<exists>i<length (nat_seq 0 n1). (nat_seq 0 n1) ! i = Suc n1p)"
      in ssubst)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(rule in_set_conv_nth)
    apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(rule_tac
      x="Suc n1p"
      in exI)
    apply(rule conjI)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(rule_tac
      t="length (nat_seq 0 n1)"
      and s="n1 - 0 + 1"
      in ssubst)
      apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
      apply(rule nat_seq_length)
      apply(force)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(rule_tac
      t="nat_seq 0 n1 ! (Suc n1p)"
      and s="0 + (Suc n1p)"
      in ssubst)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
      apply(force)
     apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(rule_tac
      d="d1"
      in position_change_due_to_step_relation)
      apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
      apply(force)
     apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
   apply(rule_tac
      d="d2"
      in position_change_due_to_step_relation)
     apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
    apply(force)
   apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac i n n1p n2p e c ea ca eb cb ec cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n n1p n2p c ea ca eb cb ec cc)(*strict*)
  apply(subgoal_tac "n1p=n1 - (Suc n)")
   apply(rename_tac n n1p n2p c ea ca eb cb ec cc)(*strict*)
   prefer 2
   apply(arith)
  apply(rename_tac n n1p n2p c ea ca eb cb ec cc)(*strict*)
  apply(subgoal_tac "n2p=n2 - (Suc n)")
   apply(rename_tac n n1p n2p c ea ca eb cb ec cc)(*strict*)
   prefer 2
   apply(arith)
  apply(rename_tac n n1p n2p c ea ca eb cb ec cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: is_backward_target_deterministic_def)
  apply(erule_tac
      x="cb"
      and P="\<lambda>cb. \<forall>c1 c2. (\<exists>e. step_relation M c1 e cb \<and> step_relation M c2 e cb) \<longrightarrow> c1 = c2"
      in allE)
  apply(erule_tac
      x="ca"
      and P="\<lambda>ca. \<forall>c2. (\<exists>e. step_relation M ca e cb \<and> step_relation M c2 e cb) \<longrightarrow> ca = c2"
      in allE)
  apply(erule_tac
      x="cc"
      and P="\<lambda>cc. (\<exists>e. step_relation M ca e cb \<and> step_relation M cc e cb) \<longrightarrow> ca = cc"
      in allE)
  apply(erule impE)
   apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
   apply(rule_tac
      x="eb"
      in exI)
   apply(rule conjI)
    apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
    apply(rule_tac
      d="d1"
      in position_change_due_to_step_relation)
      apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
      apply(force)
     apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
    apply(force)
   apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
   apply(rule_tac
      d="d2"
      in position_change_due_to_step_relation)
     apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
     apply(force)
    apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
    apply(force)
   apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac n c ea ca eb cb ec cc)(*strict*)
  apply(force)
  done

lemma deterministic_concat: "
  \<forall>a e b. step_relation M a e b \<longrightarrow> step_relation M (C a) e (C b)
  \<Longrightarrow> is_forward_deterministic M
  \<Longrightarrow> derivation M d1
  \<Longrightarrow> derivation M d2
  \<Longrightarrow> derivation M d3
  \<Longrightarrow> derivation M d4
  \<Longrightarrow> maximum_of_domain d1 n1
  \<Longrightarrow> maximum_of_domain d2 n2
  \<Longrightarrow> maximum_of_domain d3 (n1+n2)
  \<Longrightarrow> maximum_of_domain d4 (n1+n2)
  \<Longrightarrow> d3 = derivation_append (derivation_map d1 C) d2 n1
  \<Longrightarrow> d1 0 = Some (pair None c)
  \<Longrightarrow> d4 0 = Some (pair None (C c))
  \<Longrightarrow> n2 > 0
  \<Longrightarrow> d4 (n1+n2) = d2 n2
  \<Longrightarrow> d3=d4"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(induct_tac x)
   apply(rename_tac x)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac x n)(*strict*)
  apply(case_tac "d1 0")
   apply(rename_tac x n)(*strict*)
   apply(clarsimp)
  apply(rename_tac x n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rule conjI)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d1 (Suc n) = Some (pair (Some e) c)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n)(*strict*)
      apply(blast)+
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. d1 n = Some (pair e c)")
    apply(rename_tac n e ca)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc n"
      in pre_some_position_is_some_position)
      apply(rename_tac n e ca)(*strict*)
      apply(force)
     apply(rename_tac n e ca)(*strict*)
     apply(force)
    apply(rename_tac n e ca)(*strict*)
    apply(force)
   apply(rename_tac n e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e ca ea caa)(*strict*)
   apply(subgoal_tac "step_relation M caa e ca")
    apply(rename_tac n e ca ea caa)(*strict*)
    prefer 2
    apply(simp add: derivation_def)
    apply(erule_tac
      x="Suc n"
      and P="\<lambda>x. case x of 0 \<Rightarrow> (case d1 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d1 x of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d1 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
    apply(rename_tac n e ca ea caa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e ca ea caa)(*strict*)
   apply(subgoal_tac "step_relation M (C caa) e (C ca)")
    apply(rename_tac n e ca ea caa)(*strict*)
    apply(subgoal_tac "\<exists>e c. d4 (Suc n) = Some (pair (Some e) c)")
     apply(rename_tac n e ca ea caa)(*strict*)
     prefer 2
     apply(rule_tac
      M="M"
      in some_position_has_details_before_max_dom_after_0)
       apply(rename_tac n e ca ea caa)(*strict*)
       apply(force)
      apply(rename_tac n e ca ea caa)(*strict*)
      apply(force)
     apply(rename_tac n e ca ea caa)(*strict*)
     apply(force)
    apply(rename_tac n e ca ea caa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(subgoal_tac "step_relation M (C caa) eb cb")
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     prefer 2
     apply(simp add: derivation_def)
     apply(erule_tac
      x="Suc n"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d4 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d4 i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d4 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(clarsimp)
     apply(case_tac "d4 n")
      apply(rename_tac n e ca ea caa eb cb)(*strict*)
      apply(clarsimp)
     apply(rename_tac n e ca ea caa eb cb a)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(rule_tac
      ?c1.0="C caa"
      in use_is_forward_deterministic_E)
       apply(rename_tac n e ca ea caa eb cb)(*strict*)
       apply(force)
      apply(rename_tac n e ca ea caa eb cb)(*strict*)
      apply(force)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(force)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(rule_tac
      ?c1.0="C caa"
      in use_is_forward_deterministic_T)
      apply(rename_tac n e ca ea caa eb cb)(*strict*)
      apply(force)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(force)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(force)
   apply(rename_tac n e ca ea caa)(*strict*)
   apply(erule_tac
      x="caa"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="ca"
      in allE)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "n\<le>n1")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "n=n1")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d1 n1 = Some (pair e c)")
    prefer 2
    apply(rule some_position_has_details_before_max_dom)
      apply(blast)
     apply(blast)
    apply(arith)
   apply(clarsimp)
   apply(rename_tac e ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. d4 (Suc n1) = Some (pair (Some e) c)")
    apply(rename_tac e ca)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      in some_position_has_details_before_max_dom_after_0)
      apply(rename_tac e ca)(*strict*)
      apply(force)
     apply(rename_tac e ca)(*strict*)
     apply(force)
    apply(rename_tac e ca)(*strict*)
    apply(force)
   apply(rename_tac e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ca ea caa)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac e ca ea caa)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      in some_position_has_details_before_max_dom_after_0)
      apply(rename_tac e ca ea caa)(*strict*)
      apply(force)
     apply(rename_tac e ca ea caa)(*strict*)
     apply(force)
    apply(rename_tac e ca ea caa)(*strict*)
    apply(arith)
   apply(rename_tac e ca ea caa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ca ea caa eb cb)(*strict*)
   apply(subgoal_tac "step_relation M (C ca) ea caa")
    apply(rename_tac e ca ea caa eb cb)(*strict*)
    prefer 2
    apply(simp add: derivation_def)
    apply(erule_tac
      x="Suc n1"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d4 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d4 i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d4 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
    apply(rename_tac e ca ea caa eb cb)(*strict*)
    apply(clarsimp)
    apply(case_tac "d4 n1")
     apply(rename_tac e ca ea caa eb cb)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ca ea caa eb cb a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ca ea caa eb cb)(*strict*)
   apply(subgoal_tac "step_relation M (C ca) eb cb")
    apply(rename_tac e ca ea caa eb cb)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac e ca ea caa eb cb)(*strict*)
     apply(rule_tac
      ?c1.0="C ca"
      in use_is_forward_deterministic_E)
       apply(rename_tac e ca ea caa eb cb)(*strict*)
       apply(force)
      apply(rename_tac e ca ea caa eb cb)(*strict*)
      apply(force)
     apply(rename_tac e ca ea caa eb cb)(*strict*)
     apply(force)
    apply(rename_tac e ca ea caa eb cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ca ea caa cb)(*strict*)
    apply(rule_tac
      ?c1.0="C ca"
      in use_is_forward_deterministic_T)
      apply(rename_tac e ca ea caa cb)(*strict*)
      apply(force)
     apply(rename_tac e ca ea caa cb)(*strict*)
     apply(force)
    apply(rename_tac e ca ea caa cb)(*strict*)
    apply(force)
   apply(rename_tac e ca ea caa eb cb)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc n1"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case if 0 \<le> n1 then case d1 0 of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (C c)) else d2 (0 - n1) of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case if i \<le> n1 then case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (C c)) else d2 (i - n1) of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case if i' \<le> n1 then case d1 i' of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (C c)) else d2 (i' - n1) of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
   apply(rename_tac e ca ea caa eb cb)(*strict*)
   apply(clarsimp)
   apply(case_tac "d4 n1")
    apply(rename_tac e ca ea caa eb cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ca ea caa eb cb a)(*strict*)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc n\<le>(n1+n2)")
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (n-n1) = Some (pair e c)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom)
      apply(rename_tac n)(*strict*)
      apply(blast)+
    apply(rename_tac n)(*strict*)
    apply(arith)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (Suc(n-n1)) = Some (pair (Some e) c)")
    apply(rename_tac n e ca)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n e ca)(*strict*)
      apply(blast)+
    apply(rename_tac n e ca)(*strict*)
    apply(arith)
   apply(rename_tac n e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e ca ea caa)(*strict*)
   apply(subgoal_tac "\<exists>e c. d4 (Suc n) = Some (pair (Some e) c)")
    apply(rename_tac n e ca ea caa)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n e ca ea caa)(*strict*)
      apply(blast)+
   apply(rename_tac n e ca ea caa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(rule_tac
      t="Suc n - n1"
      and s="Suc(n-n1)"
      in ssubst)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(arith)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "step_relation M ca ea caa")
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    prefer 2
    apply(simp add: derivation_def)
    apply(erule_tac
      x="Suc (n-n1)"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d2 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d2 i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d2 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(subgoal_tac "step_relation M ca eb cb")
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    prefer 2
    apply(simp add: derivation_def)
    apply(erule_tac
      x="Suc n"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d4 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d4 i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d4 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(rule_tac
      ?c1.0="ca"
      in use_is_forward_deterministic_E)
      apply(rename_tac n e ca ea caa eb cb)(*strict*)
      apply(force)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(force)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(force)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(rule_tac
      ?c1.0="ca"
      in use_is_forward_deterministic_T)
     apply(rename_tac n e ca ea caa eb cb)(*strict*)
     apply(force)
    apply(rename_tac n e ca ea caa eb cb)(*strict*)
    apply(force)
   apply(rename_tac n e ca ea caa eb cb)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="d4 (Suc n)"
      and s="None"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule none_position_after_max_dom)
     apply(rename_tac n)(*strict*)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule none_position_after_max_dom)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma final_position_after_every_some_position: "
  derivation M d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> d m = Some (pair e c)
  \<Longrightarrow> (\<forall>e' c'. \<not> step_relation M c e' c')
  \<Longrightarrow> n\<le>m"
  apply(case_tac "n>m")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc m) = Some (pair (Some e) c)")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac y)(*strict*)
      apply(force)
     apply(rename_tac y)(*strict*)
     apply(force)
    apply(rename_tac y)(*strict*)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ea ca)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc m"
      in allE)
  apply(clarsimp)
  done

lemma None_not_in_get_labels: "
  derivation M dP
  \<Longrightarrow> maximum_of_domain dP (Suc n)
  \<Longrightarrow> r#r' = get_labels dP (Suc n)
  \<Longrightarrow> r=None
  \<Longrightarrow> P"
  apply(simp add: get_labels_def)
  apply(auto)
  apply(rename_tac z zs)(*strict*)
  apply(subgoal_tac "z=Suc 0")
   apply(rename_tac z zs)(*strict*)
   apply(clarsimp)
   apply(rename_tac zs)(*strict*)
   apply(simp add: get_label_def)
   apply(subgoal_tac "\<exists>e c. dP (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac zs)(*strict*)
    prefer 2
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac zs)(*strict*)
      apply(blast)+
   apply(rename_tac zs)(*strict*)
   apply(auto)
  apply(rename_tac z zs)(*strict*)
  apply(rule_tac
      t="Suc 0"
      and s="(nat_seq (Suc 0) (Suc n))!0"
      in ssubst)
   apply(rename_tac z zs)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc 0) (Suc n)"
      and s="(if (Suc 0) \<le> (Suc n) then [Suc 0] @ nat_seq (Suc (Suc 0)) (Suc n) else [])"
      in ssubst)
    apply(rename_tac z zs)(*strict*)
    apply(rule nat_seq.psimps)
    apply(rule nat_seq_termination)
   apply(rename_tac z zs)(*strict*)
   apply(clarsimp)
  apply(rename_tac z zs)(*strict*)
  apply(auto)
  done

lemma get_labels_nth_notNone: "
  derivation M dP
  \<Longrightarrow> maximum_of_domain dP n
  \<Longrightarrow> i<n
  \<Longrightarrow> r = get_labels dP n
  \<Longrightarrow> r!i=None
  \<Longrightarrow> P"
  apply(simp add: get_labels_def)
  apply(auto)
  apply(subgoal_tac "map (\<lambda>i. get_label (dP i)) (nat_seq (Suc 0) n) ! i \<noteq> None")
   apply(force)
  apply(rule_tac
      t="map (\<lambda>i. get_label (dP i)) (nat_seq (Suc 0) n) ! i"
      and s="(\<lambda>i. get_label (dP i)) ((nat_seq (Suc 0) n) ! i)"
      in ssubst)
   apply(rule List.nth_map)
   apply(rule_tac
      t="length (nat_seq (Suc 0) n)"
      and s="n - (Suc 0) + 1"
      in ssubst)
    apply(rule nat_seq_length)
    apply(arith)
   apply(arith)
  apply(rule_tac
      t="(nat_seq (Suc 0) n) ! i"
      and s="(Suc 0)+i"
      in ssubst)
   apply(rule nat_seq_nth_compute)
    apply(arith)
   apply(arith)
  apply(subgoal_tac "\<exists>e c. dP (Suc i) = Some (pair (Some e) c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom_after_0)
     apply(blast)+
   apply(arith)
  apply(simp add: get_label_def)
  apply(force)
  done

lemma identify_getLabel_with_derivation_get_label: "
  derivation P d
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> \<pi>' = get_labels d (Suc n)
  \<Longrightarrow> Suc k\<le>Suc n
  \<Longrightarrow> d (Suc k) = Some (pair (Some e) c)
  \<Longrightarrow> Some e=\<pi>'!k"
  apply(auto)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc n)) ! k"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (Suc n)) ! k)"
      in ssubst)
   apply(rule List.nth_map)
   apply(rule_tac
      t="length (nat_seq (Suc 0) (Suc n))"
      and s="(Suc n) - (Suc 0) + 1"
      in ssubst)
    apply(rule nat_seq_length)
    apply(arith)
   apply(arith)
  apply(rule_tac
      t="(nat_seq (Suc 0) (Suc n)) ! k"
      and s="(Suc 0)+k"
      in ssubst)
   apply(rule nat_seq_nth_compute)
    apply(arith)
   apply(arith)
  apply(simp add: get_label_def)
  done

lemma get_configurations_not_none: "
  derivation M d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> i\<le>m
  \<Longrightarrow> (get_configurations d m)!i = None
  \<Longrightarrow> P"
  apply(subgoal_tac "get_configurations d m ! i \<noteq> None")
   apply(blast)
  apply(thin_tac "get_configurations d m ! i = None")
  apply(simp add: get_configurations_def)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t="map (\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c) (nat_seq 0 m) ! i"
      and s = "(\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c) ((nat_seq 0 m) ! i) "
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(rule nth_map)
   apply(subgoal_tac "length (nat_seq 0 m) = m - 0 + 1")
    apply(rename_tac y)(*strict*)
    prefer 2
    apply(rule nat_seq_length)
    apply(blast)
   apply(rename_tac y)(*strict*)
   apply(arith)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t="nat_seq 0 m ! i"
      and s = "0 + i"
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac y)(*strict*)
    apply(blast)
   apply(rename_tac y)(*strict*)
   apply(arith)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(rule pre_some_position_is_some_position)
    apply(rename_tac y)(*strict*)
    apply(blast)+
  apply(rename_tac y)(*strict*)
  apply(arith)
  done

lemma get_labels_prefixes: "
  derivation M d
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> take k (get_labels d n) = take k (get_labels d (n+m))"
  apply(subgoal_tac "length (get_labels d n)=n")
   prefer 2
   apply(rule get_labels_length)
   apply(force)
  apply(subgoal_tac "length (get_labels d (n+m))=n+m")
   prefer 2
   apply(rule get_labels_length)
   apply(force)
  apply(rule listEqI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="get_labels d n ! i"
      and s="None"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule get_labels_None)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="get_labels d (n + m) ! i"
      and s= "None"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule get_labels_None)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(rename_tac i x b)
  apply(rename_tac i x b)(*strict*)
  apply(rule_tac
      t="get_labels d n ! i"
      and s="x"
      in ssubst)
   apply(rename_tac i x b)(*strict*)
   apply(rule get_labels_Not_None)
    apply(rename_tac i x b)(*strict*)
    apply(force)
   apply(rename_tac i x b)(*strict*)
   apply(force)
  apply(rename_tac i x b)(*strict*)
  apply(rule_tac
      t="get_labels d (n + m) ! i"
      and s= "x"
      in ssubst)
   apply(rename_tac i x b)(*strict*)
   apply(rule get_labels_Not_None)
    apply(rename_tac i x b)(*strict*)
    apply(force)
   apply(rename_tac i x b)(*strict*)
   apply(force)
  apply(rename_tac i x b)(*strict*)
  apply(force)
  done

lemma derivation_preserves_step_labels: "
  TSstructure M
  \<Longrightarrow> derivation M d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> c \<in> configurations M
  \<Longrightarrow> Some x\<in> set(get_labels d n)
  \<Longrightarrow> x \<in> step_labels M"
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b)(*strict*)
  apply(subgoal_tac "i>0")
   apply(rename_tac i b)(*strict*)
   apply(subgoal_tac "\<exists>j. Suc j=i")
    apply(rename_tac i b)(*strict*)
    prefer 2
    apply(case_tac i)
     apply(rename_tac i b)(*strict*)
     apply(force)
    apply(rename_tac i b nat)(*strict*)
    apply(force)
   apply(rename_tac i b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b j)(*strict*)
   apply(subgoal_tac "\<exists>e c. d j = Some (pair e c)")
    apply(rename_tac b j)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc j"
      in pre_some_position_is_some_position)
      apply(rename_tac b j)(*strict*)
      apply(force)
     apply(rename_tac b j)(*strict*)
     apply(force)
    apply(rename_tac b j)(*strict*)
    apply(force)
   apply(rename_tac b j)(*strict*)
   apply(clarsimp)
   apply(rename_tac b j e ca)(*strict*)
   apply(subgoal_tac "x \<in> step_labels M \<and> b \<in> configurations M")
    apply(rename_tac b j e ca)(*strict*)
    prefer 2
    apply(rule_tac
      m="0"
      in later_in_configuration_label)
         apply(rename_tac b j e ca)(*strict*)
         apply(force)
        apply(rename_tac b j e ca)(*strict*)
        apply(force)
       apply(rename_tac b j e ca)(*strict*)
       apply(force)
      apply(rename_tac b j e ca)(*strict*)
      apply(force)
     apply(rename_tac b j e ca)(*strict*)
     apply(force)
    apply(rename_tac b j e ca)(*strict*)
    apply(force)
   apply(rename_tac b j e ca)(*strict*)
   apply(force)
  apply(rename_tac i b)(*strict*)
  apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> n")
   apply(rename_tac i b)(*strict*)
   apply(force)
  apply(rename_tac i b)(*strict*)
  apply(rule nat_seq_in_interval)
  apply(force)
  done

lemma derivation_initialI: "
  derivation G d
  \<Longrightarrow> (\<exists>c. d 0 = Some (pair None c) \<Longrightarrow> the(get_configuration(d 0)) \<in> initial_configurations G)
  \<Longrightarrow> derivation_initial G d"
  apply(simp add: derivation_initial_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b a)(*strict*)
  apply(force)
  done

lemma get_labels_only_Some: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> None \<notin> set (get_labels d n)"
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> n")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_in_interval)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(thin_tac "i \<in> set (nat_seq (Suc 0) n)")
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
   apply(rename_tac i nat)(*strict*)
   prefer 2
   apply(rule some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i nat)(*strict*)
     apply(blast)
    apply(rename_tac i nat)(*strict*)
    apply(blast)
   apply(rename_tac i nat)(*strict*)
   apply(arith)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  done

lemma belongs_getLabel_are_in_step_labels: "
  derivation M d
  \<Longrightarrow> belongs M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> None \<notin> set (get_labels d n)
  \<Longrightarrow> set (get_labels d n) \<subseteq> Some ` step_labels M"
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>i<length (get_labels d n). get_labels d n ! i = x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule set_elem_nth)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length (get_labels d n) = n")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule get_labels_length)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i)(*strict*)
     apply(blast)
    apply(rename_tac i)(*strict*)
    apply(blast)
   apply(rename_tac i)(*strict*)
   apply(arith)
  apply(rename_tac i)(*strict*)
  apply(auto)
  apply(rename_tac i e c)(*strict*)
  apply(rule_tac
      t="get_labels d n ! i"
      and s="Some e"
      in ssubst)
   apply(rename_tac i e c)(*strict*)
   apply(rule get_labels_Not_None)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="e"
      in bexI)
   apply(rename_tac i e c)(*strict*)
   apply(auto)
  apply(rename_tac i e c)(*strict*)
  apply(simp add: belongs_def)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(auto)
  done

lemma derivation_drop_preserves_belongs: "
  derivation M d
  \<Longrightarrow> belongs M d
  \<Longrightarrow> d n\<noteq>None
  \<Longrightarrow> belongs M (derivation_drop d n)"
  apply(simp add: belongs_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(erule_tac
      x="i+n"
      in allE)
  apply(simp add: derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma belongs_step_labels: "
  belongs P d
  \<Longrightarrow> d i = Some (pair (Some e) c)
  \<Longrightarrow> e \<in> step_labels P"
  apply(simp add: belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(auto)
  done

lemma derivation_belongs: "
  TSstructure P
  \<Longrightarrow> d 0 = Some (pair None ca)
  \<Longrightarrow> ca \<in> configurations P
  \<Longrightarrow> derivation P d
  \<Longrightarrow> belongs P d"
  apply(simp only: belongs_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac nat option b)(*strict*)
    apply(force)
   apply(rename_tac nat option b)(*strict*)
   apply(force)
  apply(rename_tac nat option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b a)(*strict*)
  apply(rule later_in_configuration_label)
       apply(rename_tac nat b a)(*strict*)
       apply(force)
      apply(rename_tac nat b a)(*strict*)
      apply(force)
     apply(rename_tac nat b a)(*strict*)
     apply(force)
    apply(rename_tac nat b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat b a)(*strict*)
   apply(force)
  apply(rename_tac nat b a)(*strict*)
  apply(force)
  done

lemma derivation_initial_belongs: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> belongs G d"
  apply(simp add: derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(rule derivation_belongs)
     apply(rename_tac b)(*strict*)
     apply(force)
    apply(rename_tac b)(*strict*)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(rule_tac
      A="initial_configurations G"
      in set_mp)
    apply(rename_tac b)(*strict*)
    apply(rule AX_initial_configuration_belongs)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply(force)
  done

lemma belongs_configurations: "
  belongs M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> c \<in> configurations M"
  apply(simp add: belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  done

lemma get_accessible_configurations_are_configurations: "
  TSstructure M
  \<Longrightarrow> get_accessible_configurations M \<subseteq> configurations M"
  apply(simp add: get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d i)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d i")
   apply(rename_tac x d i)(*strict*)
   apply(force)
  apply(rename_tac x d i a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x d i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i option)(*strict*)
  apply(rule belongs_configurations)
   apply(rename_tac x d i option)(*strict*)
   apply(rule derivation_initial_belongs)
    apply(rename_tac x d i option)(*strict*)
    apply(force)
   apply(rename_tac x d i option)(*strict*)
   apply(force)
  apply(rename_tac x d i option)(*strict*)
  apply(force)
  done

lemma maximum_of_domain_not_0_position_at_Suc0: "
  derivation M d
  \<Longrightarrow> \<not> maximum_of_domain d 0
  \<Longrightarrow> \<exists>e c. d (Suc 0) = Some (pair (Some e) c)"
  apply(subgoal_tac "\<exists>c0. d 0 = Some (pair None c0)")
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac c0 y)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac c0 y)(*strict*)
    apply(force)
   apply(rename_tac c0 y)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac c0 y)(*strict*)
      apply(force)
     apply(rename_tac c0 y)(*strict*)
     apply(force)
    apply(rename_tac c0 y)(*strict*)
    apply(force)
   apply(rename_tac c0 y)(*strict*)
   apply(force)
  apply(rule some_position_has_details_at_0)
  apply(force)
  done

lemma no_some_beyond_maximum_of_domain: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d m \<noteq> None
  \<Longrightarrow> m>n
  \<Longrightarrow> P"
  apply(subgoal_tac "\<forall>m>n. d m = None")
   apply(force)
  apply(rule noSomeAfterMaxDom)
   apply(force)
  apply(force)
  done

lemma dead_end_at_some_is_max_dom2: "
  derivation M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> \<forall>e c'. \<not>(step_relation M c e c')
  \<Longrightarrow> maximum_of_domain d i"
  apply(simp add: maximum_of_domain_def)
  apply(case_tac "d (Suc i)")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac a)(*strict*)
      apply(blast)
     apply(rename_tac a)(*strict*)
     apply(blast)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea ca)(*strict*)
  apply(subgoal_tac "step_relation M c ea ca")
   apply(rename_tac ea ca)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac ea ca)(*strict*)
     apply(force)
    apply(rename_tac ea ca)(*strict*)
    apply(force)
   apply(rename_tac ea ca)(*strict*)
   apply(force)
  apply(rename_tac ea ca)(*strict*)
  apply(force)
  done

lemma maximum_of_domainUnique: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> n=m"
  apply(subgoal_tac "m\<le>n \<and> n\<le>m")
   apply(clarsimp)
  apply(rule conjI)
   apply(rule allPreMaxDomSome_prime)
     apply(blast)+
    apply(simp add: maximum_of_domain_def)
   apply(blast)
  apply(rule allPreMaxDomSome_prime)
    apply(blast)+
   apply(simp add: maximum_of_domain_def)
  apply(blast)
  done

lemma noStepsOnlyZeroLength: "
  \<forall>x e y. \<not>(step_relation M x e y)
  \<Longrightarrow> derivation M d
  \<Longrightarrow> maximum_of_domain d 0"
  apply(subgoal_tac "d 0\<noteq>None")
   prefer 2
   apply(rule initialNotNone)
   apply(blast)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(auto)
  apply(rename_tac y)(*strict*)
  apply(case_tac "d (Suc 0)")
   apply(rename_tac y)(*strict*)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac y a)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(case_tac a)
  apply(rename_tac y a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y option b)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac option b optiona ba a)(*strict*)
  apply(clarsimp)
  done

lemma dead_end_at_some_is_max_dom: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> \<forall>e c'. \<not>(step_relation M c e c')
  \<Longrightarrow> i=n"
  apply(subgoal_tac "i\<le>n")
   prefer 2
   apply(rule allPreMaxDomSome_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "i<n")
   prefer 2
   apply(force)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom_after_0)
     apply(blast)
    apply(blast)
   apply(arith)
  apply(clarsimp)
  apply(rename_tac ea ca)(*strict*)
  apply(rule noDeadEndBeforeMaxDom)
      apply(rename_tac ea ca)(*strict*)
      apply(force)
     apply(rename_tac ea ca)(*strict*)
     apply(force)
    apply(rename_tac ea ca)(*strict*)
    apply(force)
   apply(rename_tac ea ca)(*strict*)
   apply(force)
  apply(rename_tac ea ca)(*strict*)
  apply(force)
  done

lemma dead_end_at_some_is_max_dom_prime: "
  derivation M d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> \<forall>e c. \<not>(step_relation M ci e c)
  \<Longrightarrow> \<forall>e c. \<not>(step_relation M cj e c)
  \<Longrightarrow> i\<le>j"
  apply(case_tac "i\<le>j")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "j<i")
   prefer 2
   apply(force)
  apply(case_tac "Suc j<i")
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "Suc j=i")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(case_tac ei)
    apply(rule derivation_Always_PreEdge_prime)
     apply(force)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "step_relation M cj a ci")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule_tac
      n="j"
      in position_change_due_to_step_relation)
      apply(rename_tac a)(*strict*)
      apply(blast)
     apply(rename_tac a)(*strict*)
     apply(blast)
    apply(rename_tac a)(*strict*)
    apply(blast)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "d (Suc j) \<noteq> None ")
   prefer 2
   apply(rule derivationNoFromNone2_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "d (Suc j)")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac option b)(*strict*)
    apply(force)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac b a)(*strict*)
  apply(subgoal_tac "step_relation M cj a b")
   apply(rename_tac b a)(*strict*)
   prefer 2
   apply(rule_tac
      n="j"
      in position_change_due_to_step_relation)
     apply(rename_tac b a)(*strict*)
     apply(blast)
    apply(rename_tac b a)(*strict*)
    apply(blast)
   apply(rename_tac b a)(*strict*)
   apply(blast)
  apply(rename_tac b a)(*strict*)
  apply(force)
  done

lemma somewhere_none_maximum_of_domain: "
  derivation M d
  \<Longrightarrow> d i = None
  \<Longrightarrow> \<exists>x<i. maximum_of_domain d x"
  apply(induct i)
   apply(clarsimp)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "d i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def)
  apply(force)
  done

lemma certain_measure_decreasement: "
  derivation M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> P c = n
  \<Longrightarrow> (\<And>c e c' n. P c = n \<Longrightarrow> step_relation M c e c' \<Longrightarrow> \<exists>m. P c' = m \<and> m < n)
  \<Longrightarrow> \<forall>e c. d (i + k) = Some (pair e c) \<longrightarrow> (\<exists>m. P c = m \<and> m \<le> n - k)"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (i+k) = Some (pair e c)")
   apply(rename_tac k ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+k)"
      in pre_some_position_is_some_position)
     apply(rename_tac k ea ca)(*strict*)
     apply(force)
    apply(rename_tac k ea ca)(*strict*)
    apply(force)
   apply(rename_tac k ea ca)(*strict*)
   apply(force)
  apply(rename_tac k ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ea ca eaa caa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc (i+k)) = Some (pair (Some e) c)")
   apply(rename_tac k ea ca eaa caa)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+k)"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac k ea ca eaa caa)(*strict*)
      apply(force)
     apply(rename_tac k ea ca eaa caa)(*strict*)
     apply(force)
    apply(rename_tac k ea ca eaa caa)(*strict*)
    apply(force)
   apply(rename_tac k ea ca eaa caa)(*strict*)
   apply(force)
  apply(rename_tac k ea ca eaa caa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ca ea caa eb)(*strict*)
  apply(subgoal_tac "step_relation M caa eb ca")
   apply(rename_tac k ca ea caa eb)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac k ca ea caa eb)(*strict*)
     apply(force)
    apply(rename_tac k ca ea caa eb)(*strict*)
    apply(force)
   apply(rename_tac k ca ea caa eb)(*strict*)
   apply(force)
  apply(rename_tac k ca ea caa eb)(*strict*)
  apply(erule_tac
      x="caa"
      in meta_allE)
  apply(erule_tac
      x="eb"
      in meta_allE)
  apply(erule_tac
      x="ca"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac k ca ea caa eb)(*strict*)
  apply(erule_tac
      x="P caa"
      in meta_allE)
  apply(force)
  done

lemma termination_using_measure: "
  derivation M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> P c = (n::nat)
  \<Longrightarrow> (\<And>c e c' n. P c = n \<Longrightarrow> step_relation M c e c' \<Longrightarrow> \<exists>m. P c' = m \<and> m<n)
  \<Longrightarrow> (\<And>c e c'. P c = 0 \<Longrightarrow> step_relation M c e c' \<Longrightarrow> False)
  \<Longrightarrow> \<exists>x\<le>n+i. maximum_of_domain d x"
  apply(subgoal_tac "d (i+n+1)=None")
   apply(subgoal_tac "\<exists>x<(i+n+1). maximum_of_domain d x")
    prefer 2
    apply(rule somewhere_none_maximum_of_domain)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(force)
  apply(case_tac "d (i+n)")
   apply(case_tac "d (i+n+1)")
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      n="i+n"
      in derivationNoFromNone)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac "d (i+n+1)")
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a aa)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac a aa)(*strict*)
   apply(force)
  apply(rename_tac a aa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>(k::nat) e c'. d (i+k) = Some (pair e c') \<longrightarrow> (\<exists>m. P c' = m \<and> m\<le>P c-k)")
   apply(rename_tac a aa)(*strict*)
   prefer 2
   apply(rule allI)
   apply(rename_tac a aa k)(*strict*)
   apply(rule certain_measure_decreasement)
      apply(rename_tac a aa k)(*strict*)
      apply(force)
     apply(rename_tac a aa k)(*strict*)
     apply(force)
    apply(rename_tac a aa k)(*strict*)
    apply(force)
   apply(rename_tac a aa k c' ea c'a n)(*strict*)
   apply(force)
  apply(rename_tac a aa)(*strict*)
  apply(erule_tac
      x="P c"
      in allE)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac aa option b optiona ba)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac aa option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b ba)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac option b ba)(*strict*)
    apply(force)
   apply(rename_tac option b ba)(*strict*)
   apply(force)
  apply(rename_tac aa option b optiona ba a)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b ba a)(*strict*)
  apply(subgoal_tac "step_relation M b a ba")
   apply(rename_tac option b ba a)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac option b ba a)(*strict*)
     apply(force)
    apply(rename_tac option b ba a)(*strict*)
    apply(force)
   apply(rename_tac option b ba a)(*strict*)
   apply(force)
  apply(rename_tac option b ba a)(*strict*)
  apply(force)
  done

lemma certain_measure_decreasement2: "
  derivation M d
  \<Longrightarrow> belongs M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> P c = (n::nat)
  \<Longrightarrow> (\<And>c e c' n. P c = n \<Longrightarrow> step_relation M c e c' \<Longrightarrow> \<exists>m. P c' = m \<and> m\<ge>n - 1)
  \<Longrightarrow> maximal M d
  \<Longrightarrow> (\<And>c. c \<in> configurations M \<Longrightarrow> P c >0 \<Longrightarrow> \<exists>e c'. step_relation M c e c')
  \<Longrightarrow> k\<le>P c
  \<Longrightarrow> \<exists>e c'. d (i+k) = Some (pair e c') \<and> (P c-k\<le>P c')"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(erule meta_impE)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(subgoal_tac "\<exists>e c'. d (i + k) = Some (pair e c') \<and> P c - k \<le> P c'")
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(erule meta_impE)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(thin_tac "\<exists>e c'. d (i + k) = Some (pair e c') \<and> P c - k \<le> P c'")
  apply(clarsimp)
  apply(rename_tac k ea c')(*strict*)
  apply(case_tac "d (Suc (i+k))")
   apply(rename_tac k ea c')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e. Ex (step_relation M c' e)")
    apply(rename_tac k ea c')(*strict*)
    prefer 2
    apply(erule_tac
      x="c'"
      and P="\<lambda>c'. (c' \<in> configurations M \<Longrightarrow> 0 < P c' \<Longrightarrow> \<exists>e. Ex (step_relation M c' e))"
      in meta_allE)
    apply(erule meta_impE)
     apply(rename_tac k ea c')(*strict*)
     apply(rule belongs_configurations)
      apply(rename_tac k ea c')(*strict*)
      apply(force)
     apply(rename_tac k ea c')(*strict*)
     apply(force)
    apply(rename_tac k ea c')(*strict*)
    apply(force)
   apply(rename_tac k ea c')(*strict*)
   apply(clarsimp)
   apply(rename_tac k ea c' eaa x)(*strict*)
   apply(simp add: maximal_def)
   apply(subgoal_tac "maximum_of_domain d (i+k)")
    apply(rename_tac k ea c' eaa x)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac k ea c' eaa x)(*strict*)
   apply(erule disjE)
    apply(rename_tac k ea c' eaa x)(*strict*)
    apply(force)
   apply(rename_tac k ea c' eaa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
   apply(subgoal_tac "i+k=n")
    apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
    prefer 2
    apply(rule maximum_of_domainUnique)
      apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
      apply(force)
     apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
     apply(force)
    apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
    apply(force)
   apply(rename_tac k ea c' eaa x n eb ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac k ea c' a)(*strict*)
  apply(subgoal_tac "\<exists>e c. a = pair (Some e) c")
   apply(rename_tac k ea c' a)(*strict*)
   prefer 2
   apply(rule some_position_has_details_after_0)
    apply(rename_tac k ea c' a)(*strict*)
    apply(force)
   apply(rename_tac k ea c' a)(*strict*)
   apply(force)
  apply(rename_tac k ea c' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ea c' eaa ca)(*strict*)
  apply(erule_tac
      x="c'"
      and P="\<lambda>c'. (\<And>e c'a n. P c' = n \<Longrightarrow> step_relation M c' e c'a \<Longrightarrow> n - Suc 0 \<le> P c'a)"
      in meta_allE)
  apply(erule_tac
      x="eaa"
      in meta_allE)
  apply(erule_tac
      x="ca"
      and P="\<lambda>ca. (\<And>n. P c' = n \<Longrightarrow> step_relation M c' eaa ca \<Longrightarrow> n - Suc 0 \<le> P ca)"
      in meta_allE)
  apply(erule_tac
      x="P c'"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac meta_impE)
   apply(rename_tac k ea c' eaa ca)(*strict*)
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac k ea c' eaa ca)(*strict*)
     apply(force)
    apply(rename_tac k ea c' eaa ca)(*strict*)
    apply(force)
   apply(rename_tac k ea c' eaa ca)(*strict*)
   apply(force)
  apply(rename_tac k ea c' eaa ca)(*strict*)
  apply(arith)
  done

lemma minimum_runtime_using_measure: "
  derivation M d
  \<Longrightarrow> belongs M d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> P c = (n::nat)
  \<Longrightarrow> (\<And>c e c' n. P c = n \<Longrightarrow> step_relation M c e c' \<Longrightarrow> \<exists>m. P c' = m \<and> m\<ge>n - 1)
  \<Longrightarrow> (\<And>c. c\<in> configurations M \<Longrightarrow> P c >0 \<Longrightarrow> \<exists>e c'. step_relation M c e c')
  \<Longrightarrow> maximum_of_domain d z
  \<Longrightarrow> maximal M d
  \<Longrightarrow> z\<ge>i+n"
  apply(subgoal_tac "d (i+n)\<noteq>None")
   apply(subgoal_tac "\<forall>m>z. d m = None")
    prefer 2
    apply(rule noSomeAfterMaxDom)
     apply(force)
    apply(force)
   apply(case_tac "i+n>z")
    apply(erule_tac
      x="i+n"
      in allE)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>k\<le>P c. \<exists>e c'. d (i+k) = Some (pair e c') \<and> (P c-k\<le>P c')")
   prefer 2
   apply(rule allI)
   apply(rename_tac k)(*strict*)
   apply(rule impI)
   apply(rule certain_measure_decreasement2)
          apply(rename_tac k)(*strict*)
          apply(force)
         apply(rename_tac k)(*strict*)
         apply(force)
        apply(rename_tac k)(*strict*)
        apply(force)
       apply(rename_tac k)(*strict*)
       apply(force)
      apply(rename_tac k ca ea c' n)(*strict*)
      apply(force)
     apply(rename_tac k)(*strict*)
     apply(force)
    apply(rename_tac k ca)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(erule_tac
      x="P c"
      in allE)
  apply(clarsimp)
  done

lemma derivation_map_preserves_derivation2: "
  derivation M f
  \<Longrightarrow> \<forall>a e b. step_relation M a e b \<longrightarrow> step_relation M (C a) e (C b)
  \<Longrightarrow> derivation M (derivation_map f C)"
  apply(unfold derivation_map_def)
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
   apply(case_tac "f 0")
    apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "f (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "f nat")
   apply(rename_tac nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "f nat")
   apply(rename_tac nat a aa)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat a aa option b)(*strict*)
  apply(auto)
  apply(rename_tac nat aa option b)(*strict*)
  apply(case_tac "aa")
  apply(rename_tac nat aa option b optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  done

lemma derivation_map_preserves_derivation: "
  derivation G d
  \<Longrightarrow> (\<And>i e c. d i=Some (pair e c) \<Longrightarrow> P c)
  \<Longrightarrow> (\<And>c1 e c2.
    P c1
    \<Longrightarrow> P c2
    \<Longrightarrow> step_relation G c1 e c2
    \<Longrightarrow> step_relation G (f c1) e (f c2))
  \<Longrightarrow> derivation G (derivation_map d f)"
  apply(unfold derivation_map_def)
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
   apply(case_tac "d 0")
    apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat a aa)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat a aa option b)(*strict*)
  apply(auto)
  apply(rename_tac nat aa option b)(*strict*)
  apply(case_tac "aa")
  apply(rename_tac nat aa option b optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  done

lemma derivation_take_preserves_derivation: "
  derivation M d
  \<Longrightarrow> derivation M (derivation_take d n)"
  apply(simp add: derivation_take_def)
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  done

lemma derivation_take_preserves_generates_maximum_of_domain: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d (n+m)
  \<Longrightarrow> maximum_of_domain (derivation_take d n) n"
  apply(simp add: derivation_take_def)
  apply(simp (no_asm) add: maximum_of_domain_def)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(clarsimp)
  apply(rule_tac
      n="n+m"
      in some_position_has_details_before_max_dom)
    apply(blast)+
  apply(arith)
  done

lemma derivation_take_preserves_belongs: "
  belongs G d
  \<Longrightarrow> belongs G (derivation_take d i)"
  apply(simp add: belongs_def derivation_take_def)
  done

lemma derivation_drop_preserves_derivation: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d (n+m)
  \<Longrightarrow> derivation M (derivation_drop d n)"
  apply(simp (no_asm) add: derivation_def derivation_drop_def)
  apply(auto)
   apply(case_tac "d n")
    apply(auto)
    apply(simp add: maximum_of_domain_def)
    apply(auto)
    apply(rename_tac y)(*strict*)
    apply(case_tac m)
     apply(rename_tac y)(*strict*)
     apply(auto)
    apply(rename_tac y nat)(*strict*)
    apply(rule_tac
      n="Suc (n+nat)"
      and i="n"
      in derivationNoFromNone2)
       apply(rename_tac y nat)(*strict*)
       apply(blast)
      apply(rename_tac y nat)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac y nat)(*strict*)
     apply(arith)
    apply(rename_tac y nat)(*strict*)
    apply(blast)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
   apply(case_tac "d (Suc n)")
    apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
   apply(rename_tac option b)(*strict*)
   defer
   apply(rename_tac nat)(*strict*)
   apply(case_tac "d (Suc (nat+n))")
    apply(rename_tac nat)(*strict*)
    apply(auto)
   apply(rename_tac nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat a option b)(*strict*)
   apply(auto)
   apply(rename_tac nat option b)(*strict*)
   apply(case_tac "d (nat+n)")
    apply(rename_tac nat option b)(*strict*)
    apply(auto)
    apply(rule_tac
      n="Suc (nat+n)"
      and i="nat+n"
      in derivationNoFromNone2)
       apply(rename_tac nat option b)(*strict*)
       apply(blast)+
   apply(rename_tac nat option b a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat option b a optiona ba)(*strict*)
   apply(auto)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(case_tac option)
    apply(rename_tac nat option b optiona ba)(*strict*)
    apply(auto)
    apply(rename_tac nat b optiona ba)(*strict*)
    apply(rule derivation_Always_PreEdge_prime)
     apply(rename_tac nat b optiona ba)(*strict*)
     apply(blast)
    apply(rename_tac nat b optiona ba)(*strict*)
    apply(blast)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc(nat+n)"
      in allE)
   apply(auto)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac option b)(*strict*)
   apply(rule_tac
      n="Suc n"
      and i="n"
      in derivationNoFromNone2)
      apply(rename_tac option b)(*strict*)
      apply(blast)+
  apply(rename_tac option b a)(*strict*)
  apply(auto)
  apply(case_tac a)
  apply(rename_tac option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(auto)
   apply(rename_tac b optiona ba)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac b optiona ba)(*strict*)
    apply(blast)
   apply(rename_tac b optiona ba)(*strict*)
   apply(blast)
  apply(rename_tac b optiona ba a)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(auto)
  done

lemma derivation_drop_preserves_derivation_prime: "
  derivation M d
  \<Longrightarrow> d (n+m) \<noteq> None
  \<Longrightarrow> derivation M (derivation_drop d n)"
  apply(simp (no_asm) add: derivation_def derivation_drop_def)
  apply(auto)
   apply(rename_tac y)(*strict*)
   apply(case_tac "d n")
    apply(rename_tac y)(*strict*)
    apply(auto)
    apply(case_tac m)
     apply(rename_tac y)(*strict*)
     apply(auto)
    apply(rename_tac y nat)(*strict*)
    apply(rule_tac
      n="Suc (n+nat)"
      and i="n"
      in derivationNoFromNone2)
       apply(rename_tac y nat)(*strict*)
       apply(blast)
      apply(rename_tac y nat)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac y nat)(*strict*)
     apply(arith)
    apply(rename_tac y nat)(*strict*)
    apply(blast)
   apply(rename_tac y a)(*strict*)
   apply(case_tac a)
   apply(rename_tac y a option b)(*strict*)
   apply(auto)
  apply(rename_tac y i)(*strict*)
  apply(case_tac i)
   apply(rename_tac y i)(*strict*)
   apply(auto)
   apply(rename_tac y)(*strict*)
   apply(case_tac "d (Suc n)")
    apply(rename_tac y)(*strict*)
    apply(auto)
   apply(rename_tac y a)(*strict*)
   apply(case_tac a)
   apply(rename_tac y a option b)(*strict*)
   apply(auto)
   apply(rename_tac y option b)(*strict*)
   defer
   apply(rename_tac y nat)(*strict*)
   apply(case_tac "d (Suc (nat+n))")
    apply(rename_tac y nat)(*strict*)
    apply(auto)
   apply(rename_tac y nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac y nat a option b)(*strict*)
   apply(auto)
   apply(rename_tac y nat option b)(*strict*)
   apply(case_tac "d (nat+n)")
    apply(rename_tac y nat option b)(*strict*)
    apply(auto)
    apply(rule_tac
      n="Suc (nat+n)"
      and i="nat+n"
      in derivationNoFromNone2)
       apply(rename_tac y nat option b)(*strict*)
       apply(blast)+
   apply(rename_tac y nat option b a)(*strict*)
   apply(case_tac a)
   apply(rename_tac y nat option b a optiona ba)(*strict*)
   apply(auto)
   apply(rename_tac y nat option b optiona ba)(*strict*)
   apply(case_tac option)
    apply(rename_tac y nat option b optiona ba)(*strict*)
    apply(auto)
    apply(rename_tac y nat b optiona ba)(*strict*)
    apply(rule derivation_Always_PreEdge_prime)
     apply(rename_tac y nat b optiona ba)(*strict*)
     apply(blast)
    apply(rename_tac y nat b optiona ba)(*strict*)
    apply(blast)
   apply(rename_tac y nat b optiona ba a)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc(nat+n)"
      in allE)
   apply(auto)
  apply(rename_tac y option b)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac y option b)(*strict*)
   apply(rule_tac
      n="Suc n"
      and i="n"
      in derivationNoFromNone2)
      apply(rename_tac y option b)(*strict*)
      apply(blast)+
  apply(rename_tac y option b a)(*strict*)
  apply(auto)
  apply(case_tac a)
  apply(rename_tac y option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac y option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac y option b optiona ba)(*strict*)
   apply(auto)
   apply(rename_tac y b optiona ba)(*strict*)
   apply(rule derivation_Always_PreEdge_prime)
    apply(rename_tac y b optiona ba)(*strict*)
    apply(blast)
   apply(rename_tac y b optiona ba)(*strict*)
   apply(blast)
  apply(rename_tac y b optiona ba a)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(auto)
  done

lemma derivation_concat2: "
  derivation M f
  \<Longrightarrow> maximum_of_domain f fn
  \<Longrightarrow> derivation M g
  \<Longrightarrow> (case (f fn) of Some (pair e1 c1) \<Rightarrow> (case (g 0) of Some (pair None c2) \<Rightarrow> (c1=c2)))
  \<Longrightarrow> derivation M (derivation_append f g fn)"
  apply(subgoal_tac "\<exists>cg0. g 0=Some (pair None cg0)")
   apply(subgoal_tac "\<exists>cf0. f 0=Some (pair None cf0)")
    apply(subgoal_tac "\<exists>e cfn. f fn=Some (pair e cfn)")
     apply(simp add: derivation_append_def)
     apply(simp (no_asm) add: derivation_def)
     apply(auto)
      apply(rename_tac cg0 cf0 e i)(*strict*)
      apply(case_tac i)
       apply(rename_tac cg0 cf0 e i)(*strict*)
       apply(auto)
      apply(rename_tac cg0 cf0 e nat)(*strict*)
      apply(subgoal_tac "\<exists>e1 cf1. f nat=Some (pair e1 cf1)")
       apply(rename_tac cg0 cf0 e nat)(*strict*)
       apply(subgoal_tac "\<exists>e2 cf2. f (Suc nat)=Some (pair (Some e2) cf2)")
        apply(rename_tac cg0 cf0 e nat)(*strict*)
        apply(auto)
        apply(rename_tac cg0 cf0 e nat e1 e2 cf1 cf2)(*strict*)
        apply(simp add: derivation_def)
        apply(erule_tac
      x="Suc nat"
      and P="\<lambda>x. case x of 0 \<Rightarrow> (case f 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case f x of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case f i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
        apply(rename_tac cg0 cf0 e nat e1 e2 cf1 cf2)(*strict*)
        apply(clarsimp)
       apply(rename_tac cg0 cf0 e nat e1 cf1)(*strict*)
       defer
       apply(rename_tac cg0 cf0 e nat)(*strict*)
       defer
       apply(rename_tac cg0 cf0 e i)(*strict*)
       apply(case_tac i)
        apply(rename_tac cg0 cf0 e i)(*strict*)
        apply(auto)
        apply(rename_tac cg0 cf0 e nat)(*strict*)
        apply(subgoal_tac "nat=fn")
         apply(rename_tac cg0 cf0 e nat)(*strict*)
         apply(clarsimp)
         apply(rename_tac cg0 cf0 e)(*strict*)
         apply(case_tac "g (Suc 0)")
          apply(rename_tac cg0 cf0 e)(*strict*)
          apply(clarsimp)
         apply(rename_tac cg0 cf0 e a)(*strict*)
         apply(subgoal_tac "\<exists>e c. g (Suc 0)=Some (pair (Some e) c)")
          apply(rename_tac cg0 cf0 e a)(*strict*)
          apply(clarsimp)
          apply(rename_tac cg0 cf0 e ea c)(*strict*)
          apply(simp add: derivation_def)
          apply(erule_tac
      x="Suc 0"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (g 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)) (g i'))) (g i)"
      in allE)
          apply(rename_tac cg0 cf0 e ea c)(*strict*)
          apply(clarsimp)
         apply(rename_tac cg0 cf0 e a)(*strict*)
         defer
         apply(rename_tac cg0 cf0 e nat)(*strict*)
         defer
         apply(case_tac "g (Suc nat - fn)")
          apply(rename_tac cg0 cf0 e nat)(*strict*)
          apply(clarsimp)
         apply(rename_tac cg0 cf0 e nat a)(*strict*)
         apply(subgoal_tac "\<exists>e c. g (Suc nat - fn)=Some (pair (Some e) c)")
          apply(rename_tac cg0 cf0 e nat a)(*strict*)
          apply(subgoal_tac "\<exists>e c. g (nat - fn)=Some (pair e c)")
           apply(rename_tac cg0 cf0 e nat a)(*strict*)
           apply(auto)
          apply(rename_tac cg0 cf0 e nat ea eb c ca)(*strict*)
          apply(simp add: derivation_def)
          apply(erule_tac
      x="Suc nat - fn"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (g 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)) (g i'))) (g i)"
      in allE)
          apply(rename_tac cg0 cf0 e nat ea eb c ca)(*strict*)
          apply(case_tac "Suc nat - fn")
           apply(rename_tac cg0 cf0 e nat ea eb c ca)(*strict*)
           apply(clarsimp)
          apply(rename_tac cg0 cf0 e nat ea eb c ca nata)(*strict*)
          apply(clarsimp)
          apply(subgoal_tac "nata=nat-fn")
           apply(rename_tac cg0 cf0 e nat ea eb c ca nata)(*strict*)
           apply(auto)
         apply(rename_tac cg0 cf0 e nat ea c)(*strict*)
         apply(rule_tac
      m="Suc nat - fn"
      in pre_some_position_is_some_position)
           apply(rename_tac cg0 cf0 e nat ea c)(*strict*)
           apply(blast)+
         apply(rename_tac cg0 cf0 e nat ea c)(*strict*)
         apply(arith)
        apply(rename_tac cg0 cf0 e nat a)(*strict*)
        apply(rule_tac
      g="g"
      and n="nat - fn"
      in some_position_has_details_after_0)
         apply(rename_tac cg0 cf0 e nat a)(*strict*)
         apply(blast)+
        apply(rename_tac cg0 cf0 e nat a)(*strict*)
        apply(rule_tac
      s="Suc nat - fn"
      in ssubst)
         apply(rename_tac cg0 cf0 e nat a)(*strict*)
         apply(arith)
        apply(rename_tac cg0 cf0 e nat a)(*strict*)
        apply(blast)
       apply(rename_tac cg0 cf0)(*strict*)
       apply(rule some_position_has_details_before_max_dom)
         apply(rename_tac cg0 cf0)(*strict*)
         apply(blast)+
      apply(rename_tac cg0)(*strict*)
      apply(rule some_position_has_details_at_0)
      apply(blast)+
     apply(rule some_position_has_details_at_0)
     apply(blast)+
    apply(rename_tac cg0 cf0 e nat e1 cf1)(*strict*)
    apply(rule some_position_has_details_before_max_dom_after_0)
      apply(rename_tac cg0 cf0 e nat e1 cf1)(*strict*)
      apply(blast)+
   apply(rename_tac cg0 cf0 e nat)(*strict*)
   apply(rule_tac
      m="fn"
      in pre_some_position_is_some_position)
     apply(rename_tac cg0 cf0 e nat)(*strict*)
     apply(blast)+
   apply(rename_tac cg0 cf0 e nat)(*strict*)
   apply(arith)
  apply(rename_tac cg0 cf0 e a)(*strict*)
  apply(rule_tac
      g="g"
      and n="0"
      in some_position_has_details_after_0)
   apply(rename_tac cg0 cf0 e a)(*strict*)
   apply(blast)+
  done

corollary derivation_append_generates_derivation: "
  derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d1 n = Some (pair e1 c1)
  \<Longrightarrow> (\<And>e2 c2. d2 (Suc 0) = Some (pair (Some e2) c2)
    \<Longrightarrow> step_relation G c1 e2 c2)
  \<Longrightarrow> derivation G (derivation_append d1 d2 n)"
  apply(subgoal_tac "\<exists>c. d1 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(simp (no_asm) add: derivation_def)
  apply(clarsimp)
  apply(rename_tac c i)(*strict*)
  apply(case_tac i)
   apply(rename_tac c i)(*strict*)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac c i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rule conjI)
   apply(rename_tac c nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 nat = Some (pair e1 c1) \<and> d1 (Suc nat) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
    apply(rename_tac c nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in step_detail_before_some_position)
      apply(rename_tac c nat)(*strict*)
      apply(force)
     apply(rename_tac c nat)(*strict*)
     apply(force)
    apply(rename_tac c nat)(*strict*)
    apply(force)
   apply(rename_tac c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat e1a e2 c1a c2)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "d2 (Suc nat - n)")
   apply(rename_tac c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac c nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat option b)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rule conjI)
   apply(rename_tac c nat option b)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat=n")
    apply(rename_tac c nat option b)(*strict*)
    prefer 2
    apply(arith)
   apply(rename_tac c nat option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac c option b)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac c option b)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in pre_some_position_is_some_position_prime)
       apply(rename_tac c option b)(*strict*)
       apply(force)
      apply(rename_tac c option b)(*strict*)
      apply(force)
     apply(rename_tac c option b)(*strict*)
     apply(force)
    apply(rename_tac c option b)(*strict*)
    apply(force)
   apply(rename_tac c option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac c nat option b)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d2 (nat-n) = Some (pair (Some e) c)")
   apply(rename_tac c nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat-n"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac c nat option b)(*strict*)
      apply(force)
     apply(rename_tac c nat option b)(*strict*)
     apply(force)
    apply(rename_tac c nat option b)(*strict*)
    apply(force)
   apply(rename_tac c nat option b)(*strict*)
   apply(force)
  apply(rename_tac c nat option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat option b e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (Suc nat-n) = Some (pair (Some e) c)")
   apply(rename_tac c nat option b e ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat-n"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac c nat option b e ca)(*strict*)
      apply(force)
     apply(rename_tac c nat option b e ca)(*strict*)
     apply(force)
    apply(rename_tac c nat option b e ca)(*strict*)
    apply(force)
   apply(rename_tac c nat option b e ca)(*strict*)
   apply(force)
  apply(rename_tac c nat option b e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat b e ca ea)(*strict*)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc nat - n"
      and P="\<lambda>i. case i of 0 \<Rightarrow> (case d2 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case d2 i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case d2 i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation G i'2 i1v i2)))"
      in allE)
  apply(rename_tac c nat b e ca ea)(*strict*)
  apply(case_tac "Suc nat - n")
   apply(rename_tac c nat b e ca ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac c nat b e ca ea nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nata = nat-n")
   apply(rename_tac c nat b e ca ea nata)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c nat b e ca ea nata)(*strict*)
  apply(clarsimp)
  done

lemma from_to_is_to: "
  derivation_from_to M f S E
  \<Longrightarrow> derivation_to M f E"
  apply(simp add: derivation_from_to_def derivation_to_def)
  done

lemma from_to_is_from: "
  derivation_from_to M f S E
  \<Longrightarrow> derivation_from M f S"
  apply(simp add: derivation_from_to_def derivation_from_def)
  done

lemma from_to_is_der: "
  derivation_from_to M f S E
  \<Longrightarrow> derivation M f"
  apply(simp add: derivation_from_to_def derivation_to_def)
  done

lemma to_has_maximum_of_domain: "
  derivation_to M f E
  \<Longrightarrow> \<exists>n. maximum_of_domain f n"
  apply(simp add: derivation_to_def maximum_of_domain_def)
  apply(auto)
  done

lemma reachesToAtMaxDom: "
  derivation_to G d {y. \<exists>x. y = pair x c}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> \<exists>e. d m = Some (pair e c)"
  apply(simp add: derivation_to_def)
  apply(auto)
  apply(rename_tac n x)(*strict*)
  apply(subgoal_tac "maximum_of_domain d n")
   apply(rename_tac n x)(*strict*)
   apply(subgoal_tac "n=m")
    apply(rename_tac n x)(*strict*)
    apply(auto)
   apply(rename_tac n x)(*strict*)
   apply(rule maximum_of_domainUnique)
     apply(rename_tac n x)(*strict*)
     apply(auto)
  apply(rename_tac n x)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma reachesToAtMaxDom2: "
  derivation_to G d T
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> \<exists>x\<in> T. d m = Some x"
  apply(simp add: derivation_to_def)
  apply(auto)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "maximum_of_domain d n")
   apply(rename_tac n y)(*strict*)
   apply(subgoal_tac "n=m")
    apply(rename_tac n y)(*strict*)
    apply(auto)
   apply(rename_tac n y)(*strict*)
   apply(rule maximum_of_domainUnique)
     apply(rename_tac n y)(*strict*)
     apply(auto)
  apply(rename_tac n y)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma exEmptyDeri: "
  \<exists>d. derivation_from_to G d {pair None c} {y. \<exists>x. y = pair x c}"
  apply(rule_tac
      x="\<lambda>x. if x=0 then Some (pair None c) else None"
      in exI)
  apply(simp add: derivation_from_to_def)
  apply(auto)
   apply(simp add: derivation_from_def)
   apply(simp add: derivation_def)
   apply(auto)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(auto)
  apply(simp add: derivation_to_def)
  apply(simp add: derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  done

lemma derivation_from_starts_from: "
  derivation_from M d F
  \<Longrightarrow> \<exists>x\<in> F. d 0 = Some x"
  apply(simp add: derivation_from_def)
  apply(auto)
  apply(case_tac "d 0")
   apply(auto)
  done

lemma derivation_from_starts_from2: "
  derivation_from M d {pair None c}
  \<Longrightarrow> d 0 = Some (pair None c)"
  apply(simp add: derivation_from_def)
  apply(auto)
  apply(case_tac "d 0")
   apply(auto)
  done

lemma noStepsFromInterTo: "
  \<forall>x e y. \<not>(step_relation M x e y)
  \<Longrightarrow> derivation_from_to M d S E
  \<Longrightarrow> E\<inter>S={}
  \<Longrightarrow> P"
  apply(subgoal_tac "maximum_of_domain d 0")
   prefer 2
   apply(rule noStepsOnlyZeroLength)
    apply(force)
   apply(rule from_to_is_der)
   apply(blast)
  apply(subgoal_tac "\<exists>c\<in> E. d 0 = Some c")
   apply(subgoal_tac "\<exists>x\<in> S. d 0 = Some x")
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rule derivation_from_starts_from)
   apply(rule from_to_is_from)
   apply(blast)
  apply(rule reachesToAtMaxDom2)
   apply(rule from_to_is_to)
   apply(blast)
  apply(blast)
  done

lemma derivation_drop_preserves_derivation_from_to: "
  derivation_from_to M d F T
  \<Longrightarrow> maximum_of_domain d (n+m)
  \<Longrightarrow> d n=Some (pair e X)
  \<Longrightarrow> derivation_from_to M (derivation_drop d n) {pair None X} (if m=0 then {pair None X} else T)"
  apply(subgoal_tac "derivation M (derivation_drop d n)")
   prefer 2
   apply(rule_tac
      n="n"
      and m="m"
      in derivation_drop_preserves_derivation)
    apply(rule from_to_is_der)
    apply(blast)
   apply(blast)
  apply(simp add: derivation_from_to_def derivation_from_def derivation_to_def)
  apply(auto)
     apply(rename_tac na y)(*strict*)
     apply(case_tac "derivation_drop d n 0")
      apply(rename_tac na y)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_drop_def)
     apply(rename_tac na y a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac na y a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac na y option b)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac na y)(*strict*)
    apply(case_tac "d 0")
     apply(rename_tac na y)(*strict*)
     apply(clarsimp)
    apply(rename_tac na y a)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp (no_asm) add: derivation_drop_def)
    apply(clarsimp)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac na y)(*strict*)
   apply(case_tac "derivation_drop d n 0")
    apply(rename_tac na y)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_drop_def)
   apply(rename_tac na y a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac na y a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac na y option b)(*strict*)
   apply(simp add: derivation_drop_def)
  apply(rename_tac na y)(*strict*)
  apply(subgoal_tac "maximum_of_domain d na")
   apply(rename_tac na y)(*strict*)
   apply(subgoal_tac "na=n+m")
    apply(rename_tac na y)(*strict*)
    apply(clarsimp)
    apply(rename_tac y)(*strict*)
    apply(rule_tac
      x="m"
      in exI)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
    apply(rule conjI)
     apply(rename_tac y)(*strict*)
     apply(rule_tac
      s="Suc (n+m)"
      in ssubst)
      apply(rename_tac y)(*strict*)
      apply(auto)
    apply(rename_tac y)(*strict*)
    apply(rule_tac
      x="y"
      in bexI)
     apply(rename_tac y)(*strict*)
     apply(rule_tac
      s="n+m"
      in ssubst)
      apply(rename_tac y)(*strict*)
      apply(auto)
   apply(rename_tac na y)(*strict*)
   apply(rule_tac
      ?d.0="d"
      in maximum_of_domainUnique)
     apply(rename_tac na y)(*strict*)
     apply(blast)
    apply(rename_tac na y)(*strict*)
    apply(blast)
   apply(rename_tac na y)(*strict*)
   apply(simp add: maximum_of_domain_def)+
  done

lemma derivation_drop_preserves_derivation_from_to2: "
  derivation_from_to M d F T
  \<Longrightarrow> maximum_of_domain d (n+m)
  \<Longrightarrow> d n=Some (pair e X)
  \<Longrightarrow> m=0 \<longrightarrow> (pair None X)\<in> T
  \<Longrightarrow> derivation_from_to M (derivation_drop d n) {pair None X} T"
  apply(subgoal_tac "derivation M (derivation_drop d n)")
   prefer 2
   apply(rule_tac
      n="n"
      and m="m"
      in derivation_drop_preserves_derivation)
    apply(simp add: derivation_from_to_def derivation_from_def derivation_to_def)
   apply(blast)
  apply(simp add: derivation_from_to_def derivation_from_def derivation_to_def)
  apply(rule conjI)
   apply(simp add: derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac na y)(*strict*)
  apply(subgoal_tac "maximum_of_domain d na")
   apply(rename_tac na y)(*strict*)
   apply(subgoal_tac "na=n+m")
    apply(rename_tac na y)(*strict*)
    apply(clarsimp)
    apply(rename_tac y)(*strict*)
    apply(rule_tac
      x="m"
      in exI)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
    apply(rule conjI)
     apply(rename_tac y)(*strict*)
     apply(clarsimp)
    apply(rename_tac y)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac y)(*strict*)
     apply(rule_tac
      s="Suc (n+m)"
      in ssubst)
      apply(rename_tac y)(*strict*)
      apply(auto)
      apply(rule_tac
      x="y"
      in bexI)
       apply(rename_tac y)(*strict*)
       apply(rule_tac
      s="n+m"
      in ssubst)
        apply(rename_tac y)(*strict*)
        apply(auto)
     apply(rename_tac na y)(*strict*)
     apply(rule_tac
      ?d.0="d"
      in maximum_of_domainUnique)
       apply(rename_tac na y)(*strict*)
       apply(blast)
      apply(rename_tac na y)(*strict*)
      apply(blast)
     apply(rename_tac na y)(*strict*)
     apply(simp add: maximum_of_domain_def)+
    apply(rename_tac na y)(*strict*)
    apply(rule_tac
      ?d.0="d"
      in maximum_of_domainUnique)
      apply(rename_tac na y)(*strict*)
      apply(blast)
     apply(rename_tac na y)(*strict*)
     apply(simp add: maximum_of_domain_def)+
  done

lemma noNonEmptyDeriFromEmpty: "
  \<forall>e c2. \<not> (step_relation M c1 e c2)
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> derivation_from M d {pair None c1}
  \<Longrightarrow> P"
  apply(subgoal_tac "d 0\<noteq>None")
   prefer 2
   apply(rule initialNotNone)
   apply(simp add: derivation_from_def)
   apply(blast)
  apply(subgoal_tac "0=Suc n")
   apply(blast)
  apply(rule_tac
      d="d"
      in maximum_of_domainUnique)
    apply(simp add: derivation_from_def)
    apply(blast)
   apply(blast)
  apply(simp add: derivation_from_def derivation_def)
  apply(auto)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(auto)
  apply(case_tac "d (Suc 0)")
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(auto)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(auto)
  done

lemma modifying_derivation_is_not_empty: "
  derivation_from_to G d {pair None c1} {y. \<exists>xa. y = pair xa c2}
  \<Longrightarrow> c1\<noteq>c2
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> n\<noteq>0"
  apply(case_tac n)
   apply(auto)
  apply(subgoal_tac "d 0=Some (pair None c1)")
   apply(subgoal_tac "\<exists>e. d 0=Some (pair e c2)")
    apply(clarsimp)
   apply(rule reachesToAtMaxDom)
    apply(rule from_to_is_to)
    apply(blast)
   apply(clarsimp)
  apply(rule derivation_from_starts_from2)
  apply(rule from_to_is_from)
  apply(blast)
  done

lemma derivation_take_preserves_derivation_from_to: "
  derivation_from_to M d F T
  \<Longrightarrow> maximum_of_domain d (n+m)
  \<Longrightarrow> d n=Some (pair e X)
  \<Longrightarrow> derivation_from_to M (derivation_take d n) F {pair e X}"
  apply(simp (no_asm) add: derivation_from_to_def derivation_from_def derivation_to_def)
  apply(rule conjI)
   apply(rule derivation_take_preserves_derivation)
   apply(rule from_to_is_der)
   apply(blast)+
  apply(rule conjI)
   defer
   apply(rule conjI)
    apply(rule derivation_take_preserves_derivation)
    apply(rule from_to_is_der)
    apply(blast)+
   apply(rule_tac
      x="n"
      in exI)
   apply(simp add: derivation_take_def)+
  apply(simp add: derivation_from_to_def derivation_from_def)
  done

lemma toAtMaxDom: "
  derivation_from_to G d2 {pair None F} {y. \<exists>xa. y = pair xa C}
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> \<exists>e2. d2 m2 = Some (pair e2 C)"
  apply(simp add: derivation_from_to_def)
  apply(simp add: derivation_to_def)
  apply(auto)
  apply(rename_tac n xa)(*strict*)
  apply(subgoal_tac "maximum_of_domain d2 n")
   apply(rename_tac n xa)(*strict*)
   apply(subgoal_tac "m2 = n")
    apply(rename_tac n xa)(*strict*)
    apply(auto)
   apply(rename_tac n xa)(*strict*)
   apply(rule maximum_of_domainUnique)
     apply(rename_tac n xa)(*strict*)
     apply(auto)
  apply(rename_tac n xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma fromAtZero: "
  derivation_from_to G d2 {pair None F} {y. \<exists>xa. y = pair xa C}
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> d2 0 = Some (pair None F)"
  apply(simp add: derivation_from_to_def)
  apply(simp add: derivation_from_def)
  apply(auto)
  apply(case_tac "d2 0")
   apply(auto)
  done

lemma concatIsFromTo: "
  derivation_from_to G d1 {pair None d1F} {y. \<exists>xa. y = pair xa dJ}
  \<Longrightarrow> derivation_from_to G d2 {pair None dJ} {y. \<exists>xa. y = pair xa d2T}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> derivation_from_to G (derivation_append d1 d2 m1) {pair None d1F} {y. \<exists>xa. y = pair xa d2T}"
  apply(subgoal_tac "d1 0 = Some(pair None d1F)")
   apply(subgoal_tac "d2 0 = Some(pair None dJ)")
    apply(subgoal_tac "\<exists>e1. d1 m1 = Some(pair e1 dJ)")
     apply(subgoal_tac "\<exists>e2. d2 m2 = Some(pair e2 d2T)")
      apply(erule_tac exE)+
      apply(rename_tac e1 e2)(*strict*)
      defer
      apply(rule toAtMaxDom)
       apply(blast)+
     apply(rule toAtMaxDom)
      apply(blast)+
    apply(rule fromAtZero)
     apply(blast)+
   apply(rule fromAtZero)
    apply(blast)+
  apply(rename_tac e1 e2)(*strict*)
  apply(simp add: derivation_from_to_def derivation_to_def derivation_from_def)
  apply(auto)
     apply(rename_tac e1 e2 n na xa xaa)(*strict*)
     apply(rule derivation_concat2)
        apply(rename_tac e1 e2 n na xa xaa)(*strict*)
        apply(blast)
       apply(rename_tac e1 e2 n na xa xaa)(*strict*)
       apply(blast)
      apply(rename_tac e1 e2 n na xa xaa)(*strict*)
      apply(blast)
     apply(rename_tac e1 e2 n na xa xaa)(*strict*)
     apply(auto)
    apply(rename_tac e1 e2 n na xa xaa)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac e1 e2 n na xa xaa)(*strict*)
   apply(rule derivation_concat2)
      apply(rename_tac e1 e2 n na xa xaa)(*strict*)
      apply(blast)
     apply(rename_tac e1 e2 n na xa xaa)(*strict*)
     apply(blast)
    apply(rename_tac e1 e2 n na xa xaa)(*strict*)
    apply(blast)
   apply(rename_tac e1 e2 n na xa xaa)(*strict*)
   apply(auto)
  apply(rename_tac e1 e2 n na xa xaa)(*strict*)
  apply(rule_tac
      x = "m1+m2"
      in exI)
  apply(rule conjI)
   apply(rename_tac e1 e2 n na xa xaa)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac e1 e2 n na xa xaa)(*strict*)
  apply(case_tac "m2")
   apply(rename_tac e1 e2 n na xa xaa)(*strict*)
   apply(rule_tac
      x = "pair e1 d2T"
      in exI)
   apply(rule conjI)
    apply(rename_tac e1 e2 n na xa xaa)(*strict*)
    apply(rule_tac
      x = "e1"
      in exI)
    apply(blast)
   apply(rename_tac e1 e2 n na xa xaa)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac e1 e2 n na xa xaa nat)(*strict*)
  apply(rule_tac
      x = "pair e2 d2T"
      in exI)
  apply(rule conjI)
   apply(rename_tac e1 e2 n na xa xaa nat)(*strict*)
   apply(rule_tac
      x = "e2"
      in exI)
   apply(blast)
  apply(rename_tac e1 e2 n na xa xaa nat)(*strict*)
  apply(simp add: derivation_append_def)
  done

lemma consDerivation_From_To: "
  derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e c2)
  \<Longrightarrow> derivation_from_to G d {pair None c1} {y. \<exists>xa. y = pair xa c2}"
  apply(simp add: derivation_from_to_def derivation_from_def derivation_to_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
  apply(simp add: maximum_of_domain_def)
  done

lemma derivation_from_to_from_derivation: "
  derivation M d
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e c2)
  \<Longrightarrow> d (Suc n) = None
  \<Longrightarrow> derivation_from_to M d {pair None c1} {y. \<exists>xa. y = pair xa c2}"
  apply(simp add: derivation_from_to_def derivation_from_def derivation_to_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
  done

lemma get_labelElim1: "
  derivation M d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> get_label (d n) = e"
  apply(simp add: get_label_def)
  done

lemma get_labelElim2: "
  derivation M d
  \<Longrightarrow> get_label (d n) = (Some e)
  \<Longrightarrow> \<exists>c. d n = Some (pair (Some e) c)"
  apply(simp add: get_label_def)
  apply(case_tac "d n")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(auto)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  done

lemma derivation_take_preserves_derivation_initial: "
  derivation_initial M d
  \<Longrightarrow> derivation_initial M (derivation_take d n)"
  apply(simp add: derivation_initial_def)
  apply(rule conjI)
   apply(rule derivation_take_preserves_derivation)
   apply(force)
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_id_prime_prime: "
  maximum_of_domain d m
  \<Longrightarrow> derivation G d
  \<Longrightarrow> n\<ge>m
  \<Longrightarrow> derivation_take d n = d"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<forall>m'>m. d m' = None")
   apply(rename_tac x)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac x)(*strict*)
  apply(rule noSomeAfterMaxDom)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma derivation_take_id_prime: "
  d n=None
  \<Longrightarrow> derivation M d
  \<Longrightarrow> derivation_take d n = d"
  apply(simp add: derivation_take_def)
  apply(rule ext)
  apply(rename_tac na)(*strict*)
  apply(clarsimp)
  apply(case_tac "d na")
   apply(rename_tac na)(*strict*)
   apply(force)
  apply(rename_tac na a)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac na a)(*strict*)
   apply(force)
  apply(rename_tac na a)(*strict*)
  apply(rule_tac
      i="n"
      in derivationNoFromNone2)
     apply(rename_tac na a)(*strict*)
     apply(force)
    apply(rename_tac na a)(*strict*)
    apply(force)
   apply(rename_tac na a)(*strict*)
   apply(force)
  apply(rename_tac na a)(*strict*)
  apply(force)
  done

lemma derivation_drop_makes_maximum_of_domain: "
  derivation M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> n\<ge>m
  \<Longrightarrow> maximum_of_domain (derivation_drop d m) (n-m)"
  apply(simp add: maximum_of_domain_def derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma derivation_append_preserves_belongs: "
  TSstructure G
  \<Longrightarrow> belongs G d1
  \<Longrightarrow> derivation G (derivation_append d1 d2 n)
  \<Longrightarrow> belongs G (derivation_append d1 d2 n)"
  apply(subgoal_tac "\<exists>c. (derivation_append d1 d2 n) 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule derivation_belongs)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(simp add: belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(simp add: derivation_append_def)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma derivation_append_preserves_derivation_initial: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation G (derivation_append d1 d2 n)
  \<Longrightarrow> derivation_initial G (derivation_append d1 d2 n)"
  apply(subgoal_tac "\<exists>c. (derivation_append d1 d2 n) 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: derivation_initial_def)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  done

lemma derivation_append_preserves_derivation_initial_prime: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> derivation_append_fit d1 d2 n
  \<Longrightarrow> derivation_initial G (derivation_append d1 d2 n)"
  apply(subgoal_tac "derivation G (derivation_append d1 d2 n)")
   prefer 2
   apply(rule derivation_concat2)
      apply(simp add: derivation_initial_def)
     apply(force)
    apply(force)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac "d1 n")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac option b)(*strict*)
    apply(force)
   apply(rename_tac option b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac option b a optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(case_tac optiona)
    apply(rename_tac option b optiona ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac option b optiona ba a)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>c. (derivation_append d1 d2 n) 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(simp add: derivation_initial_def derivation_append_fit_def derivation_append_def)
  done

lemma derivation_map_preserves_belongs: "
  TSstructure G
  \<Longrightarrow> belongs G d
  \<Longrightarrow> derivation G d
  \<Longrightarrow> derivation G (derivation_map d C)
  \<Longrightarrow> (\<And>c. c \<in> configurations G \<Longrightarrow> C c \<in> configurations G)
  \<Longrightarrow> belongs G (derivation_map d C)"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule derivation_belongs)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac c)(*strict*)
   apply(erule_tac
      x="c"
      in meta_allE)
   apply(simp add: belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma derivation_map_preserves_derivation_initial: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> derivation G d
  \<Longrightarrow> derivation G (derivation_map d C)
  \<Longrightarrow> (\<And>c. c \<in> initial_configurations G \<Longrightarrow> C c \<in> initial_configurations G)
  \<Longrightarrow> derivation_initial G (derivation_map d C)"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: derivation_initial_def)
  apply(simp add: derivation_map_def)
  done

lemma dead_end_diff: "
  derivation M d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> \<forall>e c. \<not>(step_relation M ci e c)
  \<Longrightarrow> i<j
  \<Longrightarrow> P"
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   prefer 2
   apply(rule_tac
      m="j"
      in pre_some_position_is_some_position_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> step_relation M c1 e2 c2")
   prefer 2
   apply(rule_tac
      m="Suc i"
      in step_detail_before_some_position)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma derivation_append_preserves_derivation: "
  derivation M f
  \<Longrightarrow> derivation M g
  \<Longrightarrow> (case (f fn) of None \<Rightarrow> False | Some (pair e1 c1) \<Rightarrow> (case (g 0) of Some (pair None c2) \<Rightarrow> (c1=c2)))
  \<Longrightarrow> derivation M (derivation_append f g fn)"
  apply(simp (no_asm) add: derivation_def derivation_append_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> (case f 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False) | Suc i' \<Rightarrow> (case f x of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> (case f i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> (case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation M i'2 i1v i2)))"
      in allE)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(case_tac "f (Suc nat)")
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. f nat = Some (pair e1 c1) \<and> f (Suc nat) = Some (pair (Some e2) c2) \<and> step_relation M c1 e2 c2")
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat=fn")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(case_tac "g (Suc 0)")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. g 0 = Some (pair e1 c1) \<and> g (Suc 0) = Some (pair (Some e2) c2) \<and> step_relation M c1 e2 c2")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in step_detail_before_some_position)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(case_tac "f fn")
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac e1 e2 c1 c2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 option b)(*strict*)
   apply(subgoal_tac "\<exists>c. g 0 = Some (pair None c)")
    apply(rename_tac e1 e2 c1 c2 option b)(*strict*)
    prefer 2
    apply(rule some_position_has_details_at_0)
    apply(force)
   apply(rename_tac e1 e2 c1 c2 option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "g (Suc nat - fn)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. g (nat - fn) = Some (pair e1 c1) \<and> g (Suc (nat - fn)) = Some (pair (Some e2) c2) \<and> step_relation M c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat - fn"
      in step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat a e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "Suc nat -fn = Suc(nat- fn)")
   apply(rename_tac nat a e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat a e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  done

lemma derivation_take_derivation_append_distrib: "
  maximum_of_domain dRa nR
  \<Longrightarrow> derivation G dRa
  \<Longrightarrow> dR nL = Some (pair eR cR)
  \<Longrightarrow> derivation_take (derivation_append dR dRa nL) (nL + nR) =
          derivation_append (derivation_take dR nL) dRa nL"
  apply(simp add: derivation_take_def derivation_append_def)
  apply(rule ext)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>m>nR. dRa m = None")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule noSomeAfterMaxDom)
    apply(rename_tac n)(*strict*)
    apply(force)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(force)
  done

lemma der3_is_derivation: "
  TSstructure G
  \<Longrightarrow> step_relation G c1 e1 c2
  \<Longrightarrow> step_relation G c2 e2 c3
  \<Longrightarrow> derivation G (der3 c1 e1 c2 e2 c3)"
  apply(simp add: derivation_def der3_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat nata)(*strict*)
  apply(case_tac nata)
   apply(rename_tac i nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat nata natb)(*strict*)
  apply(clarsimp)
  done

lemma derivation_append_id_on_der1: "
  derivation G d
  \<Longrightarrow> d (Suc n) = None
  \<Longrightarrow> derivation_append d (der1 c) n = d"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: der1_def)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(case_tac "d x")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair e c)")
   apply(rename_tac x a)(*strict*)
   prefer 2
   apply(rule_tac
      m="x"
      in pre_some_position_is_some_position)
     apply(rename_tac x a)(*strict*)
     apply(force)
    apply(rename_tac x a)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  done

lemma der2_is_derivation: "
  step_relation G c1 e c2
  \<Longrightarrow> derivation G (der2 c1 e c2)"
  apply(simp add: derivation_def der2_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  done

lemma der1_is_derivation: "
  derivation G (der1 c)"
  apply(simp add: derivation_def der1_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  done

lemma der1_belongs: "
  c \<in> configurations G
  \<Longrightarrow> belongs G (der1 c)"
  apply(simp add: belongs_def der1_def)
  done

lemma der2_belongs: "
  c1 \<in> configurations G
  \<Longrightarrow> e \<in> step_labels G
  \<Longrightarrow> c2 \<in> configurations G
  \<Longrightarrow> belongs G (der2 c1 e c2)"
  apply(simp add: belongs_def der2_def)
  done

lemma derivation_append_extend_crop_with_last_step: "
  derivation M dL
  \<Longrightarrow> dL (Suc nL) = Some (pair (Some e2) cL)
  \<Longrightarrow> maximum_of_domain dL (Suc nL)
  \<Longrightarrow> step_relation GL c1 e2 cL
  \<Longrightarrow> dR =
          derivation_append (derivation_take dL nL)
           (der2 c1 e2 cL)
           nL
  \<Longrightarrow> dL = dR"
  apply(simp add: derivation_append_def)
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x \<le> nL")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x - nL = 0")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x - nL")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac x nat)(*strict*)
   apply(simp add: derivation_take_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="x"
      and s="Suc nL"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac x nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac x nata)(*strict*)
  apply(case_tac "dL x")
   apply(rename_tac x nata)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac x nata a)(*strict*)
  apply(rule_tac
      m="x"
      and d="dL"
      in no_some_beyond_maximum_of_domain)
     apply(rename_tac x nata a)(*strict*)
     apply(force)
    apply(rename_tac x nata a)(*strict*)
    apply(force)
   apply(rename_tac x nata a)(*strict*)
   apply(force)
  apply(rename_tac x nata a)(*strict*)
  apply(force)
  done

lemma is_forward_deterministic_derivations_coincide: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> is_forward_deterministic G
  \<Longrightarrow> d1 x = d2 y
  \<Longrightarrow> d1 (x+n) \<noteq> None
  \<Longrightarrow> d2 (y+m) \<noteq> None
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> d1 (x+n) = l
  \<Longrightarrow> d2 (y+n) = r
  \<Longrightarrow> l=r"
  apply(rule_tac
      t="l"
      and s="d1 (x+n)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="r"
      and s="d2 (y+n)"
      in ssubst)
   apply(force)
  apply(thin_tac "d1 (x+n) = l")
  apply(thin_tac "d2 (y+n) = r")
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya yaa)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (x+n) = Some (pair e1 c1) \<and> d1 (Suc (x+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n ya yaa)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (x+n)"
      in step_detail_before_some_position)
     apply(rename_tac n ya yaa)(*strict*)
     apply(force)
    apply(rename_tac n ya yaa)(*strict*)
    apply(force)
   apply(rename_tac n ya yaa)(*strict*)
   apply(force)
  apply(rename_tac n ya yaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (y+n) = Some (pair e1 c1) \<and> d2 (Suc (y+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="(y+m)"
      in step_detail_before_some_position)
     apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(simp add: use_is_forward_deterministic_E)
  apply(simp add: use_is_forward_deterministic_T)
  done

lemma is_forward_deterministic_accessible_derivations_coincide: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation_initial G d2
  \<Longrightarrow> is_forward_deterministic_accessible G
  \<Longrightarrow> d1 x = d2 y
  \<Longrightarrow> d1 (x+n) \<noteq> None
  \<Longrightarrow> d2 (y+m) \<noteq> None
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> d1 (x+n) = l
  \<Longrightarrow> d2 (y+n) = r
  \<Longrightarrow> l=r"
  apply(rule_tac
      t="l"
      and s="d1 (x+n)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="r"
      and s="d2 (y+n)"
      in ssubst)
   apply(force)
  apply(thin_tac "d1 (x+n) = l")
  apply(thin_tac "d2 (y+n) = r")
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya yaa)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (x+n) = Some (pair e1 c1) \<and> d1 (Suc (x+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n ya yaa)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (x+n)"
      in step_detail_before_some_position)
     apply(rename_tac n ya yaa)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n ya yaa)(*strict*)
    apply(force)
   apply(rename_tac n ya yaa)(*strict*)
   apply(force)
  apply(rename_tac n ya yaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (y+n) = Some (pair e1 c1) \<and> d2 (Suc (y+n)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="(y+m)"
      in step_detail_before_some_position)
     apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
     apply(rule derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
   apply(simp add: is_forward_deterministic_accessible_def)
   apply(simp add: is_forward_edge_deterministic_accessible_def)
   apply(clarsimp)
   apply(erule_tac
      x="c1a"
      in ballE)
    apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
    apply(erule_tac
      x="c2"
      in allE)
    apply(erule_tac
      x="c2a"
      in allE)
    apply(erule_tac
      x="e2"
      in allE)
    apply(erule_tac
      x="e2a"
      in allE)
    apply(clarsimp)
   apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
   apply(simp add: get_accessible_configurations_def)
   apply(erule_tac
      x="d1"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x="(x+n)"
      in allE)
   apply(simp add: get_configuration_def)
  apply(rename_tac n ya e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(simp add: is_forward_deterministic_accessible_def)
  apply(simp add: is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac n ya c2 e1a e2a c1a c2a)(*strict*)
  apply(erule_tac
      x="c1a"
      in ballE)
   apply(rename_tac n ya c2 e1a e2a c1a c2a)(*strict*)
   apply(erule_tac
      x="c2"
      in allE)
   apply(erule_tac
      x="c2a"
      in allE)
   apply(erule impE)
    apply(rename_tac n ya c2 e1a e2a c1a c2a)(*strict*)
    apply(rule_tac
      x="e2a"
      in exI)
    apply(force)
   apply(rename_tac n ya c2 e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac n ya c2 e1a e2a c1a c2a)(*strict*)
  apply(simp add: get_accessible_configurations_def)
  apply(erule_tac
      x="d1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="(x+n)"
      in allE)
  apply(simp add: get_configuration_def)
  done

lemma derivation_append_derivation_take: "
  maximum_of_domain d n
  \<Longrightarrow> derivation G d
  \<Longrightarrow> derivation_take (derivation_append d d' n) n = d"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def derivation_append_def)
  apply(clarsimp)
  apply(case_tac "d x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(rule no_some_beyond_maximum_of_domain)
     apply(rename_tac x a)(*strict*)
     apply(force)
    apply(rename_tac x a)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  done

lemma derivation_drop_derivation_append: "
  derivation G d2
  \<Longrightarrow> derivation_append_fit d1 d2 n
  \<Longrightarrow> derivation_drop (derivation_append d1 d2 n) n = d2"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_drop_def derivation_append_def derivation_append_fit_def)
  apply(clarsimp)
  apply(case_tac "d1 n")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac option b optiona ba)(*strict*)
   prefer 2
   apply(rule some_position_has_details_at_0)
   apply(force)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(clarsimp)
  done

lemma not_none_before_maximum_of_domain: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> d x \<noteq> None"
  apply(subgoal_tac "\<exists>e c. d x = Some (pair e c)")
   apply(force)
  apply (metis some_position_has_details_before_max_dom)
  done

lemma derivation_append_minimal_maximum_of_domain: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> maximum_of_domain d x
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> d = derivation_append d1 d2 n
  \<Longrightarrow> n\<le>x"
  apply(case_tac "n\<le>x")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "n>x")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "derivation_append d1 d2 n n = None")
   prefer 2
   apply (metis allPreMaxDomSome_prime less_le_not_le)
  apply(simp add: derivation_append_def maximum_of_domain_def)
  done

lemma der3_belongs: "
  TSstructure G
  \<Longrightarrow> derivation G (der3 c1 e1 c2 e2 c3)
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> belongs G (der3 c1 e1 c2 e2 c3)"
  apply(rule derivation_belongs)
     apply(force)
    apply(simp add: der3_def)
   apply(force)
  apply(force)
  done

lemma der3_preserves_get_accessible_configurations: "
  TSstructure G
  \<Longrightarrow> derivation G (der3 c1 e1 c2 e2 c3)
  \<Longrightarrow> c1 \<in> get_accessible_configurations G
  \<Longrightarrow> c3 \<in> get_accessible_configurations G"
  apply(simp add: get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="derivation_append d (der3 c1 e1 c2 e2 c3) i"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac d i)(*strict*)
     apply(force)
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac d i)(*strict*)
     apply(simp add: derivation_initial_def)
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(case_tac "d i")
    apply(rename_tac d i)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option)(*strict*)
   apply(simp add: der3_def)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="Suc(Suc i)"
      in exI)
  apply(simp add: derivation_append_def der3_def)
  apply(simp add: get_configuration_def)
  done

lemma der2_preserves_get_accessible_configurations: "
  TSstructure G
  \<Longrightarrow> derivation G (der2 c1 e1 c2)
  \<Longrightarrow> c1 \<in> get_accessible_configurations G
  \<Longrightarrow> c2 \<in> get_accessible_configurations G"
  apply(simp add: get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 c1 e1 c2) i"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac d i)(*strict*)
     apply(force)
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac d i)(*strict*)
     apply(simp add: derivation_initial_def)
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(case_tac "d i")
    apply(rename_tac d i)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac d i a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="Suc i"
      in exI)
  apply(simp add: derivation_append_def der2_def)
  apply(simp add: get_configuration_def)
  done

lemma der2_belongs_prime: "
  TSstructure G
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> derivation G (der2 c1 e c2)
  \<Longrightarrow> belongs G (der2 c1 e c2)"
  apply(simp (no_asm) add: der2_def belongs_def)
  apply(clarsimp)
  apply(rule AX_step_relation_preserves_belongs)
    apply(force)
   apply(rule position_change_due_to_step_relation)
     apply(force)
    apply(simp add: der2_def)
    apply(force)
   apply(simp add: der2_def)
  apply(force)
  done

lemma initial_configurations_are_get_accessible_configurations: "
  TSstructure G
  \<Longrightarrow> c \<in> initial_configurations G
  \<Longrightarrow> c \<in> get_accessible_configurations G"
  apply(simp add: get_accessible_configurations_def)
  apply(rule_tac
      x="der1 c"
      in exI)
  apply(rule conjI)
   apply(simp add: derivation_initial_def)
   apply(rule conjI)
    apply(rule der1_is_derivation)
   apply(simp add: der1_def)
  apply(simp add: der1_def get_configuration_def)
  done

lemma der2_derivation_implies_step_relation: "
  derivation G (der2 c1 e c2)
  \<Longrightarrow> step_relation G c1 e c2"
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(clarsimp)
  apply(simp add: der2_def)
  done

lemma derivation_initial_configurations: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> c \<in> configurations G"
  apply(rule belongs_configurations)
   apply(rule derivation_initial_belongs)
    apply(force)
   apply(force)
  apply(force)
  done

lemma pre_notnone_position_is_some_position: "
  derivation M g
  \<Longrightarrow> g m \<noteq> None
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> \<exists>e c. g n = Some (pair e c)"
  apply(case_tac "g m")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "n=m")
   apply(rename_tac option b)(*strict*)
   apply(auto)
  apply(rename_tac option b)(*strict*)
  apply(case_tac m)
   apply(clarsimp)
  apply(rename_tac option b nat)(*strict*)
  apply(subgoal_tac "g n\<noteq>None")
   apply(rename_tac option b nat)(*strict*)
   defer
   apply(rule derivationNoFromNone2_prime)
     apply(rename_tac option b nat)(*strict*)
     apply(blast)+
   apply(rename_tac option b nat)(*strict*)
   apply(arith)
  apply(rename_tac option b nat)(*strict*)
  apply(auto)
  apply(rename_tac option b nat y)(*strict*)
  apply(case_tac y)
  apply(clarsimp)
  done

lemma pre_notnone_position_is_some_position_prime: "
  derivation M g
  \<Longrightarrow> g m \<noteq> None
  \<Longrightarrow> Suc n\<le>m
  \<Longrightarrow> \<exists>e c. g (Suc n) = Some (pair (Some e) c)"
  apply(case_tac "g m")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(rule pre_some_position_is_some_position_prime)
     apply(rename_tac option b)(*strict*)
     apply(force)+
  done

lemma get_labels_derivation_append: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d1 n1 \<noteq> None
  \<Longrightarrow> d2 n2 \<noteq> None
  \<Longrightarrow> get_labels (derivation_append d1 d2 n1) (n1+n2)
  = get_labels d1 n1 @ (get_labels d2 n2)"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac y ya)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n1) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac y ya)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n2) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac y ya)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n1+n2)) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac y ya)(*strict*)
  apply(clarsimp)
  apply(rule listEqI)
   apply(rename_tac y ya)(*strict*)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (Suc 0) (n1+n2) ! i"
      and s = "SSn + SSi" for SSn SSi
      in ssubst)
   apply(rename_tac y ya i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(case_tac "i<n1")
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1) @ map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! i"
      and s = "(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1)) ! i"
      in ssubst)
    apply(rename_tac y ya i)(*strict*)
    apply (metis nth_append get_labels_def get_labels_length)
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "nat_seq (Suc 0) n1 ! i"
      and s = "SSn + SSi" for SSn SSi
      in ssubst)
    apply(rename_tac y ya i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac y ya i)(*strict*)
     apply(force)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac y ya i)(*strict*)
  apply(rule_tac
      t = "(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1) @ map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! i"
      and s = "(map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! (i-length(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1)))"
      in ssubst)
   apply(rename_tac y ya i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t = "nat_seq (Suc 0) n2 ! (i-n1)"
      and s = "SSn + SSi" for SSn SSi
      in ssubst)
   apply(rename_tac y ya i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(rule_tac
      t = "Suc i - n1 "
      and s = "Suc (i-n1)"
      in ssubst)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(force)
  done

lemma get_labels_derivation_take: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> get_labels d n = get_labels (derivation_take d n) n"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(simp add: derivation_take_def get_label_def)
  apply(clarsimp)
  apply(subgoal_tac "x\<le>n")
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply (metis nat_seq_in_interval)
  done

lemma get_labels_the_Some_on_defined_positions: "
  derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> get_labels d n = map (Some \<circ> the) (get_labels d n)"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(subgoal_tac "Suc 0\<le>x \<and> x \<le> n")
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(rename_tac x y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac y nat)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
    apply(rename_tac y nat)(*strict*)
    prefer 2
    apply(rule_tac
      m = "n"
      in pre_some_position_is_some_position_prime)
       apply(rename_tac y nat)(*strict*)
       apply(force)
      apply(rename_tac y nat)(*strict*)
      apply(force)
     apply(rename_tac y nat)(*strict*)
     apply(force)
    apply(rename_tac y nat)(*strict*)
    apply(force)
   apply(rename_tac y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac y nat e c)(*strict*)
   apply(simp add: get_label_def)
  apply(rename_tac x y)(*strict*)
  apply (metis nat_seq_in_interval)
  done

lemma derivation_append_preserves_label_set: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d2 m \<noteq> None
  \<Longrightarrow> set (get_labels
                (derivation_append d1 d2 n) (n+m)) =
          set (get_labels d1 n) \<union> set (get_labels d2 m)"
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac y ya)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac y ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya x)(*strict*)
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac y ya i)(*strict*)
   apply(case_tac "i\<le>n")
    apply(rename_tac y ya i)(*strict*)
    apply(clarsimp)
    apply(rule inMap)
    apply(rule_tac
      x="i"
      in bexI)
     apply(rename_tac y ya i)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya i)(*strict*)
    apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> (n+m)")
     apply(rename_tac y ya i)(*strict*)
     prefer 2
     apply(rule nat_seq_in_interval)
     apply(force)
    apply(rename_tac y ya i)(*strict*)
    apply(clarsimp)
    apply(rule nat_seq_interval)
     apply(rename_tac y ya i)(*strict*)
     apply(force)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "get_label (d2 (i - n)) \<in> (\<lambda>i. get_label (d2 i)) ` set (nat_seq (Suc 0) m)")
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="i-n"
      in bexI)
    apply(rename_tac y ya i)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya i)(*strict*)
   apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> (n+m)")
    apply(rename_tac y ya i)(*strict*)
    prefer 2
    apply(rule nat_seq_in_interval)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
   apply(rule nat_seq_interval)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac y ya)(*strict*)
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac y ya i)(*strict*)
   apply(rule inMap)
   apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> n")
    apply(rename_tac y ya i)(*strict*)
    prefer 2
    apply(rule nat_seq_in_interval)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(rule_tac
      x="i"
      in bexI)
    apply(rename_tac y ya i)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya i)(*strict*)
   apply(rule nat_seq_interval)
    apply(rename_tac y ya i)(*strict*)
    apply(force)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya x)(*strict*)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac y ya i)(*strict*)
  apply(rule inMap)
  apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> m")
   apply(rename_tac y ya i)(*strict*)
   prefer 2
   apply(rule nat_seq_in_interval)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(rule_tac
      x="i+n"
      in bexI)
   apply(rename_tac y ya i)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya i)(*strict*)
  apply(rule nat_seq_interval)
   apply(rename_tac y ya i)(*strict*)
   apply(force)
  apply(rename_tac y ya i)(*strict*)
  apply(force)
  done

lemma derivation_map_preserves_label_set: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> set (get_labels
                (derivation_map d1 C) n) =
          set (get_labels d1 n)"
  apply(simp add: derivation_map_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
   apply(rename_tac y x)(*strict*)
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac y i)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="i"
      in bexI)
    apply(rename_tac y i)(*strict*)
    apply(simp add: get_label_def)
    apply(case_tac "d1 i")
     apply(rename_tac y i)(*strict*)
     apply(clarsimp)
    apply(rename_tac y i a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac y i a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac y i)(*strict*)
   apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> n")
    apply(rename_tac y i)(*strict*)
    prefer 2
    apply(rule nat_seq_in_interval)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(rule nat_seq_interval)
    apply(rename_tac y i)(*strict*)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(clarsimp)
  apply(rename_tac y x)(*strict*)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="i"
      in bexI)
   apply(rename_tac y i)(*strict*)
   apply(simp add: get_label_def)
   apply(case_tac "d1 i")
    apply(rename_tac y i)(*strict*)
    apply(clarsimp)
   apply(rename_tac y i a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y i a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(force)
  done

lemma decompose_derivation_append_2: "
  TSstructure G
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> derivation_append_fit d1 d2 n
  \<Longrightarrow> derivation G (derivation_append d1 d2 n)
  \<Longrightarrow> derivation G d2"
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply(case_tac i)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac y)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac y)
    apply(rename_tac y option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac y a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac y option b)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac y)
   apply(rename_tac y option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(case_tac option)
    apply(rename_tac option b optiona ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac option b optiona ba a)(*strict*)
   apply(clarsimp)
  apply(rename_tac y i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat)(*strict*)
  apply(erule_tac
      x="Suc nat+n"
      in allE)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(case_tac "d2 (Suc nat)")
   apply(rename_tac y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac y nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat option b)(*strict*)
  apply(simp add: derivation_append_def derivation_append_fit_def)
  apply(case_tac "d2 nat")
   apply(rename_tac y nat option b)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac y nat option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac y option b)(*strict*)
    apply(case_tac y)
    apply(rename_tac y option b optiona ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac y nat option b nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac y nat option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac y nat option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac y nat b optiona ba)(*strict*)
   apply(case_tac nat)
    apply(rename_tac y nat b optiona ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac y b optiona ba)(*strict*)
    apply(case_tac y)
    apply(rename_tac y b optiona ba option bb)(*strict*)
    apply(clarsimp)
   apply(rename_tac y nat b optiona ba nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat option b optiona ba a)(*strict*)
  apply(case_tac option)
   apply(rename_tac y nat option b optiona ba a)(*strict*)
   apply(clarsimp)
  apply(rename_tac y nat option b optiona ba a aa)(*strict*)
  apply(case_tac y)
  apply(rename_tac y nat option b optiona ba a aa optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b optiona ba a optionb bb)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac nat b optiona ba a optionb bb)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat b optiona ba a optionb bb aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac nat b optiona ba a optionb bb aa option bc)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b optiona ba a optionb bb option bc)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat b optiona ba a optionb bb option bc)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat b optiona ba a optionb bc)(*strict*)
   apply(case_tac nat)
    apply(rename_tac nat b optiona ba a optionb bc)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat b optiona ba a optionb bc nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat b optiona ba a optionb bb option bc aa)(*strict*)
  apply(clarsimp)
  done

lemma in_get_labels_implies_realizable: "
  x \<in> set (get_labels d n)
  \<Longrightarrow> TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> \<exists>i c. Suc 0\<le>i \<and> i\<le>n \<and> d i = Some (pair x c)"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac i y)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(subgoal_tac "Suc 0 \<le> i \<and> i \<le> n")
   apply(rename_tac i y)(*strict*)
   prefer 2
   apply(rule nat_seq_in_interval)
   apply(force)
  apply(rename_tac i y)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(case_tac "d i")
   apply(rename_tac i y)(*strict*)
   apply(clarsimp)
   apply (metis allPreMaxDomSome derivation_take_id_prime derivation_take_twice_prime derivationNoFromNone derivationNoFromNone2 lessI maximum_of_domain_derivation_take)
  apply(rename_tac i y a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i y a option b)(*strict*)
  apply(clarsimp)
  done

lemma get_accessible_configurations_are_configurations2: "
  TSstructure G
  \<Longrightarrow> c \<in> get_accessible_configurations G
  \<Longrightarrow> c \<in> configurations G"
  apply(simp add: get_accessible_configurations_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac d i)(*strict*)
   apply(force)
  apply(rename_tac d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d i a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i option)(*strict*)
  apply (metis derivation_initial_configurations)
  done

lemma no_some_beyond_none: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> d n = None
  \<Longrightarrow> d m \<noteq> None
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> Q"
  apply (metis Suc_leI Suc_n_not_le_n derivationNoFromNone2_prime derivation_initial_is_derivation le_trans nat_neq_iff)
  done

lemma get_labels_concat2: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d1 n1 \<noteq> None
  \<Longrightarrow> d2 n2 \<noteq> None
  \<Longrightarrow> get_labels (derivation_append d1 d2 n1) (n1 + n2) = (get_labels d1 n1) @ (get_labels d2 n2)"
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n1) = SSn + 1 - SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) n2) = SSn + 1 - SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n1+n2)) = SSn + 1 - SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule listEqI)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (n1+n2) ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(case_tac "Suc i\<le>n1")
   apply(rename_tac i y ya)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1) @ map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! i"
      and s="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1) ) ! i"
      in ssubst)
    apply(rename_tac i y ya)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(simp add: get_label_def derivation_append_def)
   apply(subgoal_tac "nat_seq (Suc 0) n1 ! i = SSn+SSi" for SSn SSi)
    apply(rename_tac i y ya)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1) @ map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! i"
      and s="(map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n2)) ! (i-length(map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n1)))"
      in ssubst)
   apply(rename_tac i y ya)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(simp add: get_label_def derivation_append_def)
  apply(subgoal_tac "nat_seq (Suc 0) n2 ! (i-n1) = SSn+SSi" for SSn SSi)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Suc (i-n1)"
      and s="Suc i - n1"
      in ssubst)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(force)
  done

lemma get_labels_eq_from_equal_derivation: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> d2 n \<noteq> None
  \<Longrightarrow> \<forall>i\<le>n. d1 i = d2 i
  \<Longrightarrow> get_labels d1 n = get_labels d2 n"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(simp add: get_label_def)
  apply(case_tac "d1 x")
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
   apply (metis derivationNoFromNone_prime derivationNoFromNone2 derivationNoFromNone2_prime diff_is_0_eq less_Suc_eq linorder_neqE_nat nat_seq_in_interval neq0_conv zero_less_diff)
  apply(rename_tac x y a)(*strict*)
  apply(case_tac "d2 x")
   apply(rename_tac x y a)(*strict*)
   apply(clarsimp)
   apply (metis derivationNoFromNone_prime derivationNoFromNone2 derivationNoFromNone2_prime diff_is_0_eq less_Suc_eq nat_seq_in_interval neq0_conv zero_less_diff)
  apply(rename_tac x y a aa)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac x y a aa)(*strict*)
   apply (metis nat_seq_in_interval)
  apply(rename_tac x y a aa)(*strict*)
  apply(clarsimp)
  done

lemma derivation_from_derivation_append_first: "
  TSstructure G
  \<Longrightarrow> derivation G' (derivation_append d1 d2 n)
  \<Longrightarrow> derivation G' (derivation_take d1 n)"
  apply(simp (no_asm) add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(case_tac "d1 0")
    apply(clarsimp)
    apply(simp add: derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
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
   apply(rename_tac b a)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d1 (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nat a)(*strict*)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d1 nat")
   apply(rename_tac nat option b)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac nat option b a)(*strict*)
  apply(simp add: derivation_take_def)
  apply(case_tac a)
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat b optiona ba)(*strict*)
   apply(simp add: derivation_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac nat option b optiona ba a)(*strict*)
  apply(simp add: derivation_take_def)
  apply(simp add: derivation_def)
  apply(erule_tac
      x="Suc nat"
      in allE)
  apply(clarsimp)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(simp add: derivation_append_def)
  done

lemma get_labels_drop_last: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> d (Suc n) = Some (pair (Some e) c)
  \<Longrightarrow> m=(Suc n)
  \<Longrightarrow> get_labels d m = get_labels d n @ [Some e]"
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = nat_seq (Suc 0) n @ [Suc n]")
   apply(clarsimp)
   apply(simp add: get_label_def)
  apply (metis nat_seq_drop_last_simp append_Nil lessI less_Suc0 nat_seqEmpty natUptTo_n_n trivNat)
  done

definition trans_der :: "'TSstructure \<Rightarrow> (nat \<Rightarrow> ('label, 'conf) derivation_configuration option) \<Rightarrow> 'conf \<Rightarrow> 'label list \<Rightarrow> 'conf \<Rightarrow> bool" where
  "trans_der G d l f\<pi> fw = (\<exists>e.
  derivation G d
  \<and> belongs G d
  \<and> get_labels d (length f\<pi>) = map Some f\<pi>
  \<and> d 0 = Some (pair None l)
  \<and> d (length f\<pi>) = Some (pair e fw)
  )"

definition trans_der_list :: "'TSstructure \<Rightarrow> (nat \<Rightarrow> ('label, 'conf) derivation_configuration option) list \<Rightarrow> 'conf list \<Rightarrow> 'label list list \<Rightarrow> 'conf list \<Rightarrow> bool" where
  "trans_der_list G d l f\<pi> fw = (length d=length l \<and> length l=length f\<pi>\<and>length f\<pi>=length fw\<and> (\<forall>i<length d. trans_der G (d!i) (l!i) (f\<pi>!i) (fw!i)))"

lemma trans_der_belongs_configurations1: "
  trans_der G d c1 \<pi> c2
  \<Longrightarrow> c1 \<in> configurations G"
  apply(simp add: trans_der_def)
  apply(rule belongs_configurations)
   apply(force)
  apply(force)
  done

lemma trans_der_belongs_configurations2: "
  trans_der G d c1 \<pi> c2
  \<Longrightarrow> c2 \<in> configurations G"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule belongs_configurations)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

lemma trans_der_skip: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> cF
  \<Longrightarrow> d n = Some (pair e1 cI)
  \<Longrightarrow> n \<le> length \<pi>
  \<Longrightarrow> trans_der G (derivation_drop d n) cI (drop n \<pi>) cF"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   apply(rule_tac
      m="length \<pi>-n"
      in derivation_drop_preserves_derivation_prime)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   apply(rule derivation_drop_preserves_belongs)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length \<pi>-n)) = SSn + 1 - Suc 0" for SSn)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length \<pi>)) = SSn + 1 - Suc 0" for SSn)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule listEqI)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
   apply(rename_tac e i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="Some (\<pi> ! (n + i))"
      and s="(map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length \<pi>)))!(n+i)"
      in ssubst)
    apply(rename_tac e i)(*strict*)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(thin_tac "map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length \<pi>)) = map Some \<pi>")
   apply(subgoal_tac "nat_seq (Suc 0) (length \<pi>-n) ! i = SSn+SSi" for SSn SSi)
    apply(rename_tac e i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac e i)(*strict*)
     apply(force)
    apply(rename_tac e i)(*strict*)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (length \<pi>) ! (n+i) = SSn+SSi" for SSn SSi)
    apply(rename_tac e i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac e i)(*strict*)
     apply(force)
    apply(rename_tac e i)(*strict*)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length \<pi>)) ! (n + i)"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (length \<pi>)) ! (n + i))"
      in ssubst)
    apply(rename_tac e i)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(simp add: derivation_drop_def get_label_def)
   apply(rule_tac
      t="n+i"
      and s="i+n"
      in ssubst)
    apply(rename_tac e i)(*strict*)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(clarsimp)
  done

lemma trans_der_skip_prime: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> cF
  \<Longrightarrow> d n = Some (pair e1 cI)
  \<Longrightarrow> n \<le> length \<pi>
  \<Longrightarrow> \<pi>X=drop n \<pi>
  \<Longrightarrow> \<exists>d. trans_der G d cI \<pi>X cF"
  apply(rule_tac
      x="derivation_drop d n"
      in exI)
  apply(rule_tac
      t="\<pi>X"
      and s="drop n \<pi>"
      in ssubst)
   apply(force)
  apply(rule trans_der_skip)
     apply(force)+
  done

lemma trans_der_der2: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> step_relation G c e c'
  \<Longrightarrow> trans_der G (der2 c e c') c [e] c'"
  apply(simp add: trans_der_def)
  apply(rule conjI)
   apply(rule der2_is_derivation)
   apply(force)
  apply(rule conjI)
   apply(rule der2_belongs)
     apply(force)
    apply (metis AX_step_relation_preserves_belongs)
   apply (metis AX_step_relation_preserves_belongs)
  apply(rule conjI)
   apply (metis der2_get_labels insert_Nil)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(simp add: der2_def)
  done

lemma get_labels_subset_step_labels: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> set (map the (get_labels d n)) \<subseteq> step_labels G"
  apply(case_tac "0<n")
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac xa y)(*strict*)
   apply(subgoal_tac "\<exists>i<length (nat_seq (Suc 0) n). (nat_seq (Suc 0) n) ! i = xa")
    apply(rename_tac xa y)(*strict*)
    prefer 2
    apply(rule set_elem_nth)
    apply(force)
   apply(rename_tac xa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac y i)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
    apply(rename_tac y i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac y i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) n ! i = SSn+SSi" for SSn SSi)
    apply(rename_tac y i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac y i)(*strict*)
     apply(force)
    apply(rename_tac y i)(*strict*)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(simp add: belongs_def)
   apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac y i)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in pre_some_position_is_some_position_prime)
       apply(rename_tac y i)(*strict*)
       apply(force)
      apply(rename_tac y i)(*strict*)
      apply(force)
     apply(rename_tac y i)(*strict*)
     apply(force)
    apply(rename_tac y i)(*strict*)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y i e c)(*strict*)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
   apply(simp add: get_label_def)
  apply(clarsimp)
  apply(rename_tac xa y)(*strict*)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac y i)(*strict*)
  apply (metis Suc_n_not_le_n le_0_eq nat_seq_in_interval)
  done

lemma derivation_initial_has_configuration_at_position_0: "
  TSstructure G
  \<Longrightarrow> derivation_initial G d
  \<Longrightarrow> \<exists>c. d 0 = Some (pair None c) \<and> c \<in> configurations G"
  apply(subgoal_tac "belongs G d")
   prefer 2
   apply(rule derivation_initial_belongs)
    apply(force)
   apply(force)
  apply(simp add: derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac conf)(*strict*)
  apply(simp add: belongs_def derivation_initial_def)
  apply(erule_tac
      x="0"
      in allE)+
  apply(clarsimp)
  done

lemma trans_der_getLabel_at_pos: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> c'
  \<Longrightarrow> d (Suc n) = Some (pair (Some e) c'')
  \<Longrightarrow> n<length \<pi>
  \<Longrightarrow> \<pi>!n = \<pi>1
  \<Longrightarrow> e = \<pi>1"
  apply(simp add: trans_der_def)
  apply(rule_tac
      t="\<pi>1"
      and s="\<pi>!n"
      in ssubst)
   apply(force)
  apply(rule Some_inj)
  apply(rule_tac
      t="Some (\<pi>!n)"
      and s="(map Some \<pi>)!n"
      in subst)
   apply(rule nth_map)
   apply(force)
  apply(rule sym)
  apply(rule getLabel_at_pos)
    apply(force)
   apply(force)
  apply(force)
  done

lemma trans_der_crop_via_take: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> c'
  \<Longrightarrow> n\<le>length \<pi>
  \<Longrightarrow> get_configuration (d n) = Some cn
  \<Longrightarrow> \<pi>' = take n \<pi>
  \<Longrightarrow> trans_der G (derivation_take d n) c \<pi>' cn"
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option)(*strict*)
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac option e)(*strict*)
  apply(rule conjI)
   apply(rename_tac option e)(*strict*)
   apply(rule derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac option e)(*strict*)
  apply(rule conjI)
   apply(rename_tac option e)(*strict*)
   apply(rule derivation_take_preserves_belongs)
   apply(force)
  apply(rename_tac option e)(*strict*)
  apply(rule_tac
      t="min (length \<pi>) n"
      and s="n"
      in ssubst)
   apply(rename_tac option e)(*strict*)
   apply(force)
  apply(rename_tac option e)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_take d n) n"
      and s="get_labels d n"
      in ssubst)
   apply(rename_tac option e)(*strict*)
   apply (metis derivation_take_id_prime get_labels_derivation_take)
  apply(rename_tac option e)(*strict*)
  apply(rule conjI)
   apply(rename_tac option e)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def)
  apply(rename_tac option e)(*strict*)
  apply(rule listEqI)
   apply(rename_tac option e)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="min (length \<pi>) n"
      and s="n"
      in ssubst)
    apply(rename_tac option e)(*strict*)
    apply(force)
   apply(rename_tac option e)(*strict*)
   apply (metis list.size(3) nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
  apply(rename_tac option e i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (get_labels d n)=n")
   apply(rename_tac option e i)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac option e i)(*strict*)
  apply(rule_tac
      t="get_labels d n ! i"
      and s="get_labels d (length \<pi>) ! i"
      in ssubst)
   apply(rename_tac option e i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac option e i)(*strict*)
  apply(thin_tac "get_labels d (length \<pi>) = map Some \<pi>")
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac option e i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac option e i)(*strict*)
    apply(force)
   apply(rename_tac option e i)(*strict*)
   apply(force)
  apply(rename_tac option e i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (get_labels d (length \<pi>))=(length \<pi>)")
   apply(rename_tac option e i)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac option e i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (length \<pi>) ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac option e i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac option e i)(*strict*)
    apply(force)
   apply(rename_tac option e i)(*strict*)
   apply(force)
  apply(rename_tac option e i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length \<pi>)) ! i"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (length \<pi>)) ! i)"
      in ssubst)
   apply(rename_tac option e i)(*strict*)
   apply(rule nth_map)
   apply(simp add: get_labels_def)
  apply(rename_tac option e i)(*strict*)
  apply(force)
  done

lemma trans_der_crop_prime: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> c'
  \<Longrightarrow> n\<le>length \<pi>
  \<Longrightarrow> get_configuration (d n) = Some cn
  \<Longrightarrow> \<pi>' = take n \<pi>
  \<Longrightarrow> \<exists>d. trans_der G d c \<pi>' cn"
  apply(rule_tac
      x="(derivation_take d n)"
      in exI)
  apply(rule trans_der_crop_via_take)
      apply(blast)+
  done

lemma trans_der_slice: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> c'
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> j\<le>length \<pi>
  \<Longrightarrow> \<pi>'=(take (j-i) (drop i \<pi>))
  \<Longrightarrow> \<exists>d. trans_der G d ci \<pi>' cj"
  apply(subgoal_tac "trans_der G (derivation_drop d i) ci (drop i \<pi>) c'")
   prefer 2
   apply(rule trans_der_skip)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>d. trans_der G d ci (take (j-i) (drop i \<pi>)) cj")
   prefer 2
   apply(rule trans_der_crop_prime)
       apply(force)
      prefer 4
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: derivation_drop_def get_configuration_def)
   apply(clarsimp)
  apply(force)
  done

lemma equal_labels_is_forward_target_deterministic_coinciding_positions: "
  TSstructure G
  \<Longrightarrow> is_forward_target_deterministic G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> get_labels d1 n = get_labels d2 n
  \<Longrightarrow> d1 (n+x) \<noteq> None
  \<Longrightarrow> d2 (n+y) \<noteq> None
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> (\<forall>i\<le>k. d1 i = d2 i)"
  apply(induct k)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ya yaa i)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k ya yaa i)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+x"
      in step_detail_before_some_position)
     apply(rename_tac k ya yaa i)(*strict*)
     apply(force)
    apply(rename_tac k ya yaa i)(*strict*)
    apply(force)
   apply(rename_tac k ya yaa i)(*strict*)
   apply(force)
  apply(rename_tac k ya yaa i)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+y"
      in step_detail_before_some_position)
     apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac k ya yaa i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ya yaa i e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(case_tac "i\<le>k")
   apply(rename_tac k ya yaa i e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(clarsimp)
  apply(rename_tac k ya yaa i e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(subgoal_tac "i=Suc k")
   apply(rename_tac k ya yaa i e1 e2 c1 c2 e2a c2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k ya yaa i e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(erule_tac
      x="k"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "e2=e2a")
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac k ya yaa e1 c1 c2 e2a c2a)(*strict*)
   apply(simp add: is_forward_target_deterministic_def)
   apply(force)
  apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(subgoal_tac "Some e2=Some e2a")
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(force)
  apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(rule_tac
      t="Some e2"
      and s="(get_labels d1 n)!k"
      in ssubst)
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(rule sym)
   apply(rule_tac
      d="d1"
      and n="n"
      in getLabel_at_pos)
     apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
     apply(force)
    apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
    apply(force)
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(force)
  apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(rule_tac
      t="Some e2a"
      and s="(get_labels d2 n)!k"
      in ssubst)
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(rule sym)
   apply(rule_tac
      d="d2"
      and n="n"
      in getLabel_at_pos)
     apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
     apply(force)
    apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
    apply(force)
   apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
   apply(force)
  apply(rename_tac k ya yaa e1 e2 c1 c2 e2a c2a)(*strict*)
  apply(force)
  done

lemma trans_der_concat: "
  TSstructure G
  \<Longrightarrow> trans_der G d1 c1 \<pi>1 c1'
  \<Longrightarrow> trans_der G d2 c2 \<pi>2 c2'
  \<Longrightarrow> c1'=c2
  \<Longrightarrow> trans_der G (derivation_append d1 d2 (length \<pi>1)) c1 (\<pi>1@\<pi>2) c2'"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule derivation_append_preserves_belongs)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   apply (metis derivation_append_preserves_get_labels map_append)
  apply(rename_tac e ea)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  done

lemma trans_der_concat_prime: "
  TSstructure G
  \<Longrightarrow> trans_der G d1 c1 \<pi>1 c1'
  \<Longrightarrow> trans_der G d2 c2 \<pi>2 c2'
  \<Longrightarrow> c1'=c2
  \<Longrightarrow> \<exists>d. trans_der G d c1 (\<pi>1@\<pi>2) c2'"
  apply(rule_tac
      x="(derivation_append d1 d2 (length \<pi>1))"
      in exI)
  apply(rule trans_der_concat)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma trans_der_context: "
  TSstructure G
  \<Longrightarrow> trans_der G d c \<pi> c'
  \<Longrightarrow> (\<forall>a e b. step_relation G a e b \<longrightarrow> step_relation G (C a) e (C b))
  \<Longrightarrow> (\<forall>ca. ca \<in> configurations G \<longrightarrow> C ca \<in> configurations G)
  \<Longrightarrow> C c = c0
  \<Longrightarrow> C c' = c0'
  \<Longrightarrow> trans_der G (derivation_map d C) c0 \<pi> c0'"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac e)(*strict*)
   apply(rule derivation_map_preserves_derivation2)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   apply(rule derivation_map_preserves_belongs)
       apply(rename_tac e)(*strict*)
       apply(force)
      apply(rename_tac e)(*strict*)
      apply(force)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e ca)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   apply(simp add: get_labels_derivation_map)
  apply(rename_tac e)(*strict*)
  apply(simp add: derivation_map_def)
  done

lemma derivation_map_preserves_derivation23_VAR2: "
  derivation G d
  \<Longrightarrow> \<forall>i<n. \<forall>e c. d i=Some (pair e c) \<longrightarrow> P c
  \<Longrightarrow> \<forall>a e b. P a \<and> step_relation G a e b \<longrightarrow> step_relation G (C a) e (C b)
  \<Longrightarrow> derivation G (derivation_map (derivation_take d n) C)"
  apply(unfold derivation_map_def)
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case d 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case d i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case d i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> step_relation G i'2 i1v i2"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
   apply(case_tac "d 0")
    apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
   apply(rename_tac option b)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
   apply(simp add: derivation_take_def)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat a aa)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat a aa option b)(*strict*)
  apply(auto)
  apply(rename_tac nat aa option b)(*strict*)
  apply(case_tac "aa")
  apply(rename_tac nat aa option b optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(erule_tac
      x="ba"
      in allE)
  apply(erule_tac
      x="a"
      in allE)
  apply(erule_tac
      x="b"
      in allE)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  done

lemma existence_of_earliest_satisfaction_point_prime_prime: "
  derivation M d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> x\<le>n
  \<Longrightarrow> P c
  \<Longrightarrow> \<exists>k. x\<le>k \<and> k\<le>n \<and> (\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P c)) k \<and> (\<forall>i. x\<le>i \<and> i<k \<longrightarrow> (\<not>((\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P c)) i)))"
  apply(rule ex_least_nat_le_prime_prime)
   apply(force)
  apply(force)
  done

lemma trans_der_step_labels: "
  TSstructure G
  \<Longrightarrow> trans_der G d c1 \<pi> c2
  \<Longrightarrow> x\<in> set \<pi>
  \<Longrightarrow> x \<in> step_labels G"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = SSx" for SSw SSx)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule_tac
      w="\<pi>"
      and x="x"
      in set_elem_nth)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac e i)(*strict*)
   prefer 2
   apply(rule_tac
      m="(length \<pi>)"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac e i)(*strict*)
      apply(force)
     apply(rename_tac e i)(*strict*)
     apply(force)
    apply(rename_tac e i)(*strict*)
    apply(force)
   apply(rename_tac e i)(*strict*)
   apply(force)
  apply(rename_tac e i)(*strict*)
  apply(clarsimp)
  apply(rename_tac e i ea c)(*strict*)
  apply(subgoal_tac "ea=\<pi>!i")
   apply(rename_tac e i ea c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and \<pi>="\<pi>"
      in trans_der_getLabel_at_pos)
       apply(rename_tac e i ea c)(*strict*)
       apply(force)
      apply(rename_tac e i ea c)(*strict*)
      apply(simp add: trans_der_def)
     apply(rename_tac e i ea c)(*strict*)
     apply(force)
    apply(rename_tac e i ea c)(*strict*)
    apply(force)
   apply(rename_tac e i ea c)(*strict*)
   apply(force)
  apply(rename_tac e i ea c)(*strict*)
  apply(simp add: belongs_def)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  done

lemma trans_der_empty_list: "
  trans_der G d c1 \<pi> c2
  \<Longrightarrow> (\<And>p c2. p\<in> step_labels G \<Longrightarrow> \<not> step_relation G c1 p c2)
  \<Longrightarrow> \<pi>=[] \<and> c2=c1"
  apply(simp add: trans_der_def)
  apply(case_tac \<pi>)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a list e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length list)"
      in step_detail_before_some_position)
     apply(rename_tac a list e)(*strict*)
     apply(force)
    apply(rename_tac a list e)(*strict*)
    apply(force)
   apply(rename_tac a list e)(*strict*)
   apply(force)
  apply(rename_tac a list e)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e e2 c2a)(*strict*)
  apply(erule_tac
      x="e2"
      in meta_allE)
  apply(erule_tac
      x="c2a"
      in meta_allE)
  apply(clarsimp)
  apply(metis belongs_step_labels)
  done

lemma trans_der_step_detail: "
  TSstructure G
  \<Longrightarrow> trans_der G d c1 \<pi> c2
  \<Longrightarrow> i<length \<pi>
  \<Longrightarrow> \<exists>e ci ci'. d i = Some (pair e ci) \<and> d (Suc i) = Some (pair (Some (\<pi>!i)) ci') \<and> step_relation G ci (\<pi>!i) ci' \<and> (kleene_starT \<and> i=0 \<longrightarrow> c1=ci) \<and> (END \<and> Suc i=length \<pi> \<longrightarrow> c2=ci')"
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2" for SSd SSn)
   prefer 2
   apply(unfold trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold trans_der_def)
   apply(rule_tac
      m="length \<pi>"
      in step_detail_before_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1a c2a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac e1 e2 c1a c2a)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac e1 c1a c2a)(*strict*)
   apply(simp add: trans_der_def)
   apply(clarsimp)
   apply(rename_tac e1 c1a c2a e)(*strict*)
   apply(rule conjI)
    apply(rename_tac e1 c1a c2a e)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 c1a c2a e)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c1a c2a)(*strict*)
  apply(rule_tac
      d="d"
      in trans_der_getLabel_at_pos)
      apply(rename_tac e1 e2 c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 c1a c2a)(*strict*)
  apply(force)
  done

lemma trans_der_position_detail: "
  TSstructure G
  \<Longrightarrow> trans_der G d c1 \<pi> c2
  \<Longrightarrow> i\<le>length \<pi>
  \<Longrightarrow> \<exists>e ci. d i = Some (pair e ci)
  \<and> (i=0 \<longleftrightarrow> e=None)
  \<and> (i>0 \<longleftrightarrow> e=Some (\<pi>!(i - Suc 0)))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(unfold trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold trans_der_def)
   apply(rule_tac
      g="d"
      and n="i"
      and m="length(\<pi>)"
      in pre_some_position_is_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e c)(*strict*)
  apply(case_tac i)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(case_tac e)
    apply(rename_tac e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac e c a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c a)(*strict*)
   apply(simp add: trans_der_def)
  apply(rename_tac e c nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e c nat)(*strict*)
   prefer 2
   apply(unfold trans_der_def)
   apply(erule exE)+
   apply(rename_tac e c nat ea)(*strict*)
   apply(fold trans_der_def)
   apply(rule_tac
      g="d"
      and n="Suc nat"
      and m="length(\<pi>)"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac e c nat ea)(*strict*)
      apply(force)
     apply(rename_tac e c nat ea)(*strict*)
     apply(force)
    apply(rename_tac e c nat ea)(*strict*)
    apply(force)
   apply(rename_tac e c nat ea)(*strict*)
   apply(force)
  apply(rename_tac e c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat ea)(*strict*)
  apply(rule_tac
      d="d"
      in trans_der_getLabel_at_pos)
      apply(rename_tac c nat ea)(*strict*)
      apply(force)
     apply(rename_tac c nat ea)(*strict*)
     apply(force)
    apply(rename_tac c nat ea)(*strict*)
    apply(force)
   apply(rename_tac c nat ea)(*strict*)
   apply(force)
  apply(rename_tac c nat ea)(*strict*)
  apply(force)
  done

lemma trans_der_all_step_labels: "
  TSstructure G
  \<Longrightarrow> trans_der G d c1 \<pi> c2
  \<Longrightarrow> set \<pi> \<subseteq> step_labels G"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>k<length \<pi>. \<pi>!k=x")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac k)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac k)(*strict*)
    prefer 2
    apply(rule_tac
      i="Suc k"
      and d="d"
      in trans_der_position_detail)
      apply(rename_tac k)(*strict*)
      apply(force)
     apply(rename_tac k)(*strict*)
     apply(force)
    apply(rename_tac k)(*strict*)
    apply(force)
   apply(rename_tac k)(*strict*)
   apply(clarsimp)
   apply(rename_tac k ci)(*strict*)
   apply(simp add: trans_der_def)
   apply(clarsimp)
   apply(rename_tac k ci e)(*strict*)
   apply(rule belongs_step_labels)
    apply(rename_tac k ci e)(*strict*)
    apply(force)
   apply(rename_tac k ci e)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply (metis in_set_conv_nth)
  done

lemma trans_der_in_step_labels: "
  TSstructure G
  \<Longrightarrow> trans_der G d c1 \<pi> c2
  \<Longrightarrow> d n = Some (pair (Some e) c)
  \<Longrightarrow> e \<in> step_labels G"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac ea)(*strict*)
  apply(rule belongs_step_labels)
   apply(rename_tac ea)(*strict*)
   apply(force)
  apply(rename_tac ea)(*strict*)
  apply(force)
  done

lemma trans_der_equal_conf_if_empty_prods: "
  trans_der G d c1 [] c2
  \<Longrightarrow> c1=c2"
  apply(simp add: trans_der_def)
  apply(force)
  done

lemma derivation_map_preserves_derivation23: "
  derivation M f
  \<Longrightarrow> \<forall>c i e. f i=Some (pair e c) \<longrightarrow> P c
  \<Longrightarrow> \<forall>a e b i e1 e2. f i = Some (pair e1 a) \<longrightarrow> f (Suc i) = Some (pair e2 b) \<longrightarrow> P a \<longrightarrow> P b \<longrightarrow> step_relation M a e b \<longrightarrow> step_relation M (C a) e (C b)
  \<Longrightarrow> derivation M (derivation_map f C)"
  apply(unfold derivation_map_def)
  apply(simp add: derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
   apply(case_tac "f 0")
    apply(auto)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "f (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac "f nat")
   apply(rename_tac nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac nat a option b)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "f nat")
   apply(rename_tac nat a aa)(*strict*)
   apply(auto)
  apply(rename_tac nat a aa)(*strict*)
  apply(case_tac "a")
  apply(rename_tac nat a aa option b)(*strict*)
  apply(auto)
  apply(rename_tac nat aa option b)(*strict*)
  apply(case_tac "aa")
  apply(rename_tac nat aa option b optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(subgoal_tac "P b")
   apply(rename_tac nat b optiona ba a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(subgoal_tac "P ba")
   apply(rename_tac nat b optiona ba a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(thin_tac "\<forall>c. (\<exists>i e. f i = Some (pair e c)) \<longrightarrow> P c")
  apply(erule_tac
      x="ba"
      in allE)
  apply(erule_tac
      x="a"
      in allE)
  apply(erule_tac
      x="b"
      in allE)
  apply(erule_tac
      x="nat"
      in allE)
  apply(erule impE)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(erule impE)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(erule impE)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(erule impE)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(erule impE)
   apply(rename_tac nat b optiona ba a)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(force)
  done

lemma trans_der_is_forward_target_deterministic_coincide: "
  TSstructure G
  \<Longrightarrow> trans_der G d1 c \<pi> c1
  \<Longrightarrow> trans_der G d2 c \<pi> c2
  \<Longrightarrow> is_forward_target_deterministic G
  \<Longrightarrow> i \<le> length \<pi>
  \<Longrightarrow> d1 i = d2 i"
  apply(induct i)
   apply(clarsimp)
   apply(simp add: trans_der_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d1"
      and i="i"
      and kleene_starT="False"
      and END="False"
      in trans_der_step_detail)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d2"
      and i="i"
      and kleene_starT="False"
      and END="False"
      in trans_der_step_detail)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ci ci' ci'a)(*strict*)
  apply(simp add: is_forward_target_deterministic_def)
  apply(erule_tac
      x="ci"
      in allE)
  apply(erule_tac
      x="ci'"
      in allE)
  apply(erule_tac
      x="ci'a"
      in allE)
  apply(erule impE)
   apply(rename_tac i e ci ci' ci'a)(*strict*)
   apply(rule_tac
      x="\<pi>!i"
      in exI)
   apply(force)
  apply(rename_tac i e ci ci' ci'a)(*strict*)
  apply(force)
  done

lemma trans_der_coincide_with_pseudo_concat_back: "
  TSstructure G
  \<Longrightarrow> trans_der G d1 c1 \<pi>1 cI
  \<Longrightarrow> trans_der G d2 cI \<pi>2 c2
  \<Longrightarrow> trans_der G d3 c1 (\<pi>1@\<pi>2) c2
  \<Longrightarrow> n = m + length \<pi>1
  \<Longrightarrow> n\<le>length (\<pi>1@\<pi>2)
  \<Longrightarrow> is_forward_target_deterministic G
  \<Longrightarrow> m>0
  \<Longrightarrow> d3 n = d2 m"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      in trans_der_concat)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<forall>i\<le>length(\<pi>1@\<pi>2). d3 i = (derivation_append d1 d2 (length \<pi>1)) i")
   apply(clarsimp)
   apply(erule_tac
      x="m+length \<pi>1"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule trans_der_is_forward_target_deterministic_coincide)
      apply(rename_tac i)(*strict*)
      apply(force)+
  done

lemma derivationsCoincide_CropProper: "
  is_forward_deterministic P
  \<Longrightarrow> derivation P d
  \<Longrightarrow> belongs P d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> d n = Some (pair e cn)
  \<Longrightarrow> derivation P d'
  \<Longrightarrow> belongs P d'
  \<Longrightarrow> maximum_of_domain d' n'
  \<Longrightarrow> d' 0 = Some (pair None c0)
  \<Longrightarrow> d' n' = Some (pair e' cn')
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> k\<le>n'
  \<Longrightarrow> derivation_take d' k = derivation_take d k"
  apply(subgoal_tac "\<exists>e c. d' k = Some (pair e c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(blast)
    apply(blast)
   apply(force)
  apply(subgoal_tac "\<exists>e c. d k = Some (pair e c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(blast)
    apply(blast)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ea eaa c ca)(*strict*)
  apply(rule derivationsCoincide)
          apply(rename_tac ea eaa c ca)(*strict*)
          apply(force)+
         apply(rename_tac ea eaa c ca)(*strict*)
         apply(rule derivation_take_preserves_derivation)
         apply(force)+
        apply(rename_tac ea eaa c ca)(*strict*)
        apply(rule maximum_of_domain_derivation_take)
        apply(force)+
       apply(rename_tac ea eaa c ca)(*strict*)
       apply(simp add: derivation_take_def)
      apply(rename_tac ea eaa c ca)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac ea eaa c ca)(*strict*)
     apply(rule derivation_take_preserves_derivation)
     apply(force)+
    apply(rename_tac ea eaa c ca)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)+
   apply(rename_tac ea eaa c ca)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac ea eaa c ca)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma derivationsCoincide_CropProperR: "
  is_forward_deterministic_accessible P
  \<Longrightarrow> derivation_initial P d
  \<Longrightarrow> belongs P d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> d n = Some (pair e cn)
  \<Longrightarrow> derivation P d'
  \<Longrightarrow> belongs P d'
  \<Longrightarrow> maximum_of_domain d' n'
  \<Longrightarrow> d' 0 = Some (pair None c0)
  \<Longrightarrow> d' n' = Some (pair e' cn')
  \<Longrightarrow> k\<le>n
  \<Longrightarrow> k\<le>n'
  \<Longrightarrow> derivation_take d' k = derivation_take d k"
  apply(subgoal_tac "\<exists>e c. d' k = Some (pair e c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(blast)
    apply(blast)
   apply(force)
  apply(subgoal_tac "\<exists>e c. d k = Some (pair e c)")
   prefer 2
   apply(rule some_position_has_details_before_max_dom)
     apply(rule derivation_initial_is_derivation)
     apply(blast)
    apply(blast)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ea eaa c ca)(*strict*)
  apply(rule_tac
      n="k"
      in derivationsCoincideR)
          apply(rename_tac ea eaa c ca)(*strict*)
          apply(force)
         apply(rename_tac ea eaa c ca)(*strict*)
         apply(rule derivation_take_preserves_derivation)
         apply(force)
        apply(rename_tac ea eaa c ca)(*strict*)
        apply(rule maximum_of_domain_derivation_take)
        apply(force)
       apply(rename_tac ea eaa c ca)(*strict*)
       apply(simp add: derivation_take_def)
      apply(rename_tac ea eaa c ca)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac ea eaa c ca)(*strict*)
     apply(rule derivation_take_preserves_derivation_initial)
     apply(force)+
    apply(rename_tac ea eaa c ca)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)+
   apply(rename_tac ea eaa c ca)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac ea eaa c ca)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma existence_of_earliest_satisfaction_point_prime: "
  derivation M d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> P e c
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not>(\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P e c)) i) & ((\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> P e c)))k"
  apply(case_tac "d 0")
   apply(rule initialNotNone_prime)
    apply(force)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "P option b")
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(rule ex_least_nat_le)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(force)
  done

lemma get_accessible_configurations_closed_under_steps: "
  TSstructure G
  \<Longrightarrow> c \<in> get_accessible_configurations G
  \<Longrightarrow> step_relation G c e c'
  \<Longrightarrow> c' \<in> get_accessible_configurations G"
  apply(simp add: get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 c e c') i"
      in exI)
  apply(rule conjI)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation_initial)
     apply(rename_tac d i)(*strict*)
     apply(force)
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(rule derivation_append_preserves_derivation)
     apply(rename_tac d i)(*strict*)
     apply(simp add: derivation_initial_def)
    apply(rename_tac d i)(*strict*)
    apply(rule der2_is_derivation)
    apply(force)
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac d i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d i)(*strict*)
  apply(rule_tac
      x="Suc i"
      in exI)
  apply(simp add: get_configuration_def derivation_append_def der2_def)
  done

lemma derivation_append_from_derivation_append_fit: "
  TSstructure G
  \<Longrightarrow> derivation G d1
  \<Longrightarrow> derivation G d2
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> derivation_append_fit d1 d2 n
  \<Longrightarrow> derivation G (derivation_append d1 d2 n)"
  apply(rule derivation_concat2)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: derivation_append_fit_def)
  apply(case_tac "d1 n")
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac option b)(*strict*)
   apply(simp add: derivation_def)
  apply(rename_tac option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b optiona ba)(*strict*)
  apply(case_tac optiona)
   apply(rename_tac option b optiona ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac option b optiona ba a)(*strict*)
  apply(clarsimp)
  done

lemma apply_is_forward_edge_deterministic_accessible: "
  TSstructure G
  \<Longrightarrow> is_forward_edge_deterministic_accessible G
  \<Longrightarrow> c \<in> get_accessible_configurations G
  \<Longrightarrow> \<exists>c1. step_relation G c e1 c1
  \<Longrightarrow> \<exists>c2. step_relation G c e2 c2
  \<Longrightarrow> e1=e2"
  apply(simp add: is_forward_edge_deterministic_accessible_def)
  apply(erule_tac
      x="c"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  done

lemma Deterministic_pre_get_accessible_configurations: "
  TSstructure G
  \<Longrightarrow> c' \<in> get_accessible_configurations G
  \<Longrightarrow> step_relation G c e c'
  \<Longrightarrow> c' \<notin> initial_configurations G
  \<Longrightarrow> (\<forall>e' cx. step_relation G cx e' c' \<longrightarrow> c=cx)
  \<Longrightarrow> c \<in> get_accessible_configurations G"
  apply(unfold get_accessible_configurations_def)
  apply(clarify)
  apply(rename_tac d i)(*strict*)
  apply(case_tac i)
   apply(rename_tac d i)(*strict*)
   apply(thin_tac "\<forall>e' cx. step_relation G cx e' c' \<longrightarrow> c = cx")
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(simp add: derivation_initial_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac "d 0")
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i nat)(*strict*)
  apply(clarify)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="nat"
      in exI)
  apply(clarify)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac d i nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in step_detail_before_some_position)
     apply(rename_tac d i nat)(*strict*)
     apply(simp add: derivation_initial_def)
    apply(rename_tac d i nat)(*strict*)
    apply(simp add: get_configuration_def)
    apply(rename_tac d nat)(*strict*)
    apply(case_tac "d(Suc nat)")
     apply(rename_tac d nat)(*strict*)
     apply(force)
    apply(rename_tac d nat a)(*strict*)
    apply(force)
   apply(rename_tac d i nat)(*strict*)
   apply(force)
  apply(rename_tac d i nat)(*strict*)
  apply(clarify)
  apply(rename_tac d i nat e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  done

lemma trans_der_crop: "
  TSstructure G
  \<Longrightarrow> trans_der G d c0 \<pi> c1
  \<Longrightarrow> n\<le>length \<pi>
  \<Longrightarrow> d n = Some (pair e c2)
  \<Longrightarrow> \<pi>' = take n \<pi>
  \<Longrightarrow> trans_der G d c0 \<pi>' c2"
  apply(simp add: trans_der_def)
  apply(clarsimp)
  apply(rename_tac ea)(*strict*)
  apply(rule_tac
      t="min (length \<pi>) n"
      and s="n"
      in ssubst)
   apply(rename_tac ea)(*strict*)
   apply(force)
  apply(rename_tac ea)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      m="length \<pi>-n"
      and v="map Some (drop n \<pi>)"
      in get_labels_drop_tail)
   apply(rename_tac ea)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="map Some (take n \<pi>) @ map Some (drop n \<pi>)"
      and s="map Some (take n \<pi> @ drop n \<pi>)"
      in ssubst)
    apply(rename_tac ea)(*strict*)
    apply (metis List.map_append append_take_drop_id)
   apply(rename_tac ea)(*strict*)
   apply(rule_tac
      t="take n \<pi> @ drop n \<pi>"
      and s="\<pi>"
      in ssubst)
    apply(rename_tac ea)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ea)(*strict*)
   apply (metis append_take_drop_id)
  apply(rename_tac ea)(*strict*)
  apply(force)
  done

definition single_initial_configuration :: "'TSstructure \<Rightarrow> bool" where
  "single_initial_configuration G \<equiv> \<exists>c. initial_configurations G = {c}"

lemma is_forward_edge_deterministic_accessible__derivation__conincide: "
  is_forward_deterministic_accessible G
  \<Longrightarrow> derivation_initial G d1
  \<Longrightarrow> derivation_initial G d2
  \<Longrightarrow> d1 0  = d2 0
  \<Longrightarrow> d1 n1 \<noteq> None
  \<Longrightarrow> d2 n2 \<noteq> None
  \<Longrightarrow> n\<le>n1
  \<Longrightarrow> n\<le>n2
  \<Longrightarrow> d1 n = d2 n"
  apply(induct n)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n" and
      d="d1" and
      m="n1"
      in step_detail_before_some_position)
     apply(simp add: derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="n" and
      d="d2" and
      m="n2"
      in step_detail_before_some_position)
     apply(simp add: derivation_initial_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: is_forward_edge_deterministic_accessible_def is_forward_target_deterministic_accessible_def is_forward_deterministic_accessible_def)
  apply(clarsimp)
  apply(erule_tac x="c1" in ballE)
   prefer 2
   apply(simp add: get_accessible_configurations_def)
   apply(erule_tac x="d1" in allE)
   apply(clarsimp)
   apply(erule_tac x="n" in allE)
   apply(simp add: get_configuration_def)
  apply(erule_tac x="c1" in ballE)
   prefer 2
   apply(simp add: get_accessible_configurations_def)
   apply(erule_tac x="d1" in allE)
   apply(clarsimp)
   apply(erule_tac x="n" in allE)
   apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(force)
  done

end

end
