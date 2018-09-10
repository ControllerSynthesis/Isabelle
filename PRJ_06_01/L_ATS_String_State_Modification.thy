section {*L\_ATS\_String\_State\_Modification*}
theory
  L_ATS_String_State_Modification

imports
  L_ATS_List_Based_Effects

begin

locale ATS_String_State_Modification =
  ATS_List_Based_Effects
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  "effects :: 'TSstructure \<Rightarrow> 'event list set"
  "marking_condition :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> bool"
  "marked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event list set"
  "unmarked_effect :: 'TSstructure \<Rightarrow> ('label,'conf)derivation \<Rightarrow> 'event list set"
  for
    TSstructure configurations initial_configurations step_labels step_relation effects marking_condition marked_effect unmarked_effect
    +

fixes decreasing :: "bool"

fixes string_state :: "'conf \<Rightarrow> 'event list"

assumes AX_string_state_decreases: "
  TSstructure G
  \<Longrightarrow> decreasing
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> \<exists>w. string_state c1 = w @ (string_state c2)"

assumes AX_string_state_increases: "
  TSstructure G
  \<Longrightarrow> \<not> decreasing
  \<Longrightarrow> c1 \<in> configurations G
  \<Longrightarrow> step_relation G c1 e c2
  \<Longrightarrow> \<exists>w. string_state c1 @ w = (string_state c2)"

context ATS_String_State_Modification
begin

lemma derivation_monotonically_prime: "
  TSstructure P
  \<Longrightarrow> belongs P d
  \<Longrightarrow> derivation P d
  \<Longrightarrow> d i = Some(pair ei ci)
  \<Longrightarrow> d (i+j) = Some(pair eij cij)
  \<Longrightarrow> if decreasing then (\<exists>w. string_state ci = w@ string_state cij) else (\<exists>w. string_state ci @ w = string_state cij)"
  apply(subgoal_tac "\<forall>eij cij. d (i+j) = Some(pair eij cij) \<longrightarrow> (if decreasing then \<exists>w. string_state ci = w @ string_state cij else \<exists>w. string_state ci @ w = string_state cij)")
   apply(force)
  apply(rule_tac
      P="\<lambda>W. (\<forall>eij cij. W = Some (pair eij cij) \<longrightarrow> (if decreasing then \<exists>w. string_state ci = w @ string_state cij else \<exists>w. string_state ci @ w = string_state cij))"
      and G="P"
      and d="d"
      and m="i"
      and x="i+j"
      and n="j"
      in property_preseved_under_steps_is_invariant2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac ia eija cija)(*strict*)
  apply(case_tac "d(Suc ia)")
   apply(rename_tac ia eija cija)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia eija cija a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc ia) = Some (pair (Some e) c)")
   apply(rename_tac ia eija cija a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc ia"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac ia eija cija a)(*strict*)
      apply(force)
     apply(rename_tac ia eija cija a)(*strict*)
     apply(force)
    apply(rename_tac ia eija cija a)(*strict*)
    apply(force)
   apply(rename_tac ia eija cija a)(*strict*)
   apply(force)
  apply(rename_tac ia eija cija a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia eija cija e c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d ia = Some (pair e c)")
   apply(rename_tac ia eija cija e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc ia"
      in pre_some_position_is_some_position)
     apply(rename_tac ia eija cija e c)(*strict*)
     apply(force)
    apply(rename_tac ia eija cija e c)(*strict*)
    apply(force)
   apply(rename_tac ia eija cija e c)(*strict*)
   apply(force)
  apply(rename_tac ia eija cija e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia eija cija e c ea ca)(*strict*)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="ca"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "step_relation P ca e c")
   apply(rename_tac ia eija cija e c ea ca)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac ia eija cija e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac ia eija cija e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac ia eija cija e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac ia eija cija e c ea ca)(*strict*)
  apply(case_tac decreasing)
   apply(rename_tac ia eija cija e c ea ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia cija e ea ca w)(*strict*)
   apply(subgoal_tac "\<exists>w. string_state ca = w @ (string_state cija)")
    apply(rename_tac ia cija e ea ca w)(*strict*)
    prefer 2
    apply(rule_tac
      e="e"
      in AX_string_state_decreases)
       apply(rename_tac ia cija e ea ca w)(*strict*)
       apply(force)
      apply(rename_tac ia cija e ea ca w)(*strict*)
      apply(force)
     apply(rename_tac ia cija e ea ca w)(*strict*)
     apply(simp add: belongs_def)
     apply(erule_tac
      x="ia"
      in allE)
     apply(force)
    apply(rename_tac ia cija e ea ca w)(*strict*)
    apply(force)
   apply(rename_tac ia cija e ea ca w)(*strict*)
   apply(force)
  apply(rename_tac ia eija cija e c ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia cija e ea ca w)(*strict*)
  apply(subgoal_tac "\<exists>w. string_state ca @ w = (string_state cija)")
   apply(rename_tac ia cija e ea ca w)(*strict*)
   prefer 2
   apply(rule_tac
      e="e"
      in AX_string_state_increases)
      apply(rename_tac ia cija e ea ca w)(*strict*)
      apply(force)
     apply(rename_tac ia cija e ea ca w)(*strict*)
     apply(force)
    apply(rename_tac ia cija e ea ca w)(*strict*)
    apply(simp add: belongs_def)
    apply(erule_tac
      x="ia"
      in allE)
    apply(force)
   apply(rename_tac ia cija e ea ca w)(*strict*)
   apply(force)
  apply(rename_tac ia cija e ea ca w)(*strict*)
  apply(clarsimp)
  apply(rename_tac ia cija e ea ca w wa)(*strict*)
  apply(rule_tac
      x="w@wa"
      in exI)
  apply(rule_tac
      t="string_state cija"
      and s="string_state ca @ wa"
      in ssubst)
   apply(rename_tac ia cija e ea ca w wa)(*strict*)
   apply(force)
  apply(rename_tac ia cija e ea ca w wa)(*strict*)
  apply(simp (no_asm_use))
  done

lemma derivation_monotonically_dec: "
  TSstructure P
  \<Longrightarrow> decreasing
  \<Longrightarrow> belongs P d
  \<Longrightarrow> derivation P d
  \<Longrightarrow> d i = Some(pair ei ci)
  \<Longrightarrow> d (i+j) = Some(pair eij cij)
  \<Longrightarrow> \<exists>w. string_state ci = w@ string_state cij"
  apply(subgoal_tac "if decreasing then (\<exists>w. string_state ci = w@ string_state cij) else (\<exists>w. string_state ci @ w = string_state cij)")
   apply(force)
  apply(rule derivation_monotonically_prime)
      apply(force)+
  done

lemma derivation_monotonically_inc: "
  TSstructure P
  \<Longrightarrow> \<not> decreasing
  \<Longrightarrow> belongs P d
  \<Longrightarrow> derivation P d
  \<Longrightarrow> d i = Some(pair ei ci)
  \<Longrightarrow> d (i+j) = Some(pair eij cij)
  \<Longrightarrow> \<exists>w. string_state ci @ w = string_state cij"
  apply(subgoal_tac "if decreasing then (\<exists>w. string_state ci = w@ string_state cij) else (\<exists>w. string_state ci @ w = string_state cij)")
   apply(force)
  apply(rule derivation_monotonically_prime)
      apply(force)+
  done

definition trans_point :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "trans_point d i j l k R \<equiv> k \<le> j \<and>
            (\<forall>xl\<le>k.
                R l (case d (xl + i) of None \<Rightarrow> 0
                      | Some (pair e c) \<Rightarrow> length (string_state c))) \<and>
            (\<forall>xl>k.
                xl \<le> j \<longrightarrow>
                \<not> (R l (case d (xl + i) of None \<Rightarrow> 0
                 | Some (pair e c) \<Rightarrow> length (string_state c))
             ))"

lemma derivation_monotonically_decreasing_transition_point: "
  TSstructure P
  \<Longrightarrow> decreasing
  \<Longrightarrow> belongs P d
  \<Longrightarrow> derivation P d
  \<Longrightarrow> d i = Some(pair ei ci)
  \<Longrightarrow> d (i+j) = Some(pair eij cij)
  \<Longrightarrow> l \<le> length (string_state ci)
  \<Longrightarrow> length (string_state cij) \<le> l
  \<Longrightarrow> \<exists>!k. trans_point d i j l k ((\<le>))"
  apply(unfold trans_point_def)
  apply(rule monotonicSelector2)
    apply(clarsimp)
    apply(rename_tac ia ja)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (ja+i) = Some (pair (Some e) c)")
     apply(rename_tac ia ja)(*strict*)
     prefer 2
     apply(rule_tac
      m="i+j"
      in pre_some_position_is_some_position_prime)
        apply(rename_tac ia ja)(*strict*)
        apply(force)
       apply(rename_tac ia ja)(*strict*)
       apply(force)
      apply(rename_tac ia ja)(*strict*)
      apply(force)
     apply(rename_tac ia ja)(*strict*)
     apply(force)
    apply(rename_tac ia ja)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (ia+i) = Some (pair e c)")
     apply(rename_tac ia ja)(*strict*)
     prefer 2
     apply(rule_tac
      m="i+j"
      in pre_some_position_is_some_position)
       apply(rename_tac ia ja)(*strict*)
       apply(force)
      apply(rename_tac ia ja)(*strict*)
      apply(force)
     apply(rename_tac ia ja)(*strict*)
     apply(force)
    apply(rename_tac ia ja)(*strict*)
    apply(clarsimp)
    apply(rename_tac ia ja e ea c ca)(*strict*)
    apply(subgoal_tac "\<exists>w. string_state ca = w@ string_state c")
     apply(rename_tac ia ja e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      i="ia + i"
      and j="ja - ia"
      in derivation_monotonically_dec)
          apply(rename_tac ia ja e ea c ca)(*strict*)
          apply(force)
         apply(rename_tac ia ja e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac ia ja e ea c ca)(*strict*)
        apply(force)
       apply(rename_tac ia ja e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac ia ja e ea c ca)(*strict*)
      apply(rule_tac
      t="(ia + i + (ja - ia))"
      and s="ja+i"
      in ssubst)
       apply(rename_tac ia ja e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac ia ja e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac ia ja e ea c ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="i+ja"
      and s="ja+i"
      in ssubst)
      apply(rename_tac ia ja e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac ia ja e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac ia ja e ea c ca)(*strict*)
    apply(force)
   apply(force)
  apply(rule_tac
      t="j+i"
      and s="i+j"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma at_most_one_input_read_trans_point_prefix_closureise: "
  TSstructure P
  \<Longrightarrow> decreasing
  \<Longrightarrow> belongs P d
  \<Longrightarrow> derivation P d
  \<Longrightarrow> d i = Some(pair ei ci)
  \<Longrightarrow> d (i+j) = Some(pair eij cij)
  \<Longrightarrow> l \<le> length (string_state ci)
  \<Longrightarrow> length (string_state cij) \<le> l
  \<Longrightarrow> trans_point d i j l k ((\<le>))
  \<Longrightarrow> k<j
  \<Longrightarrow> d (k+i) = Some(pair ek ck)
  \<Longrightarrow> (\<forall>e\<in> step_labels P. \<forall>c1 c2. step_relation P c1 e c2 \<longrightarrow> length(string_state c1) > length(string_state c2) \<longrightarrow> (\<exists>a. string_state c1 = a#(string_state c2)))
  \<Longrightarrow> length (string_state ck) = l"
  apply(subgoal_tac "\<exists>ek' ck'. d (Suc(k+i)) = Some(pair (Some ek') ck')")
   apply(erule exE)+
   apply(rename_tac ek' ck')(*strict*)
   apply(subgoal_tac "ek' \<in> step_labels P")
    apply(rename_tac ek' ck')(*strict*)
    apply(simp add: trans_point_def)
    apply(clarsimp)
    apply(erule_tac x="k" and P="\<lambda>x. x \<le> k \<longrightarrow> l \<le> case_option 0 (case_derivation_configuration (\<lambda>e c. length (string_state c))) (d (x + i))"in allE)
    apply(rename_tac ek' ck')(*strict*)
    apply(erule_tac
      x="Suc k"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="ek'"
      in ballE)
     apply(rename_tac ek' ck')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ek' ck')(*strict*)
    apply(erule_tac
      x="ck"
      in allE)
    apply(erule_tac
      x="ck'"
      in allE)
    apply(erule impE)
     apply(rename_tac ek' ck')(*strict*)
     apply(rule position_change_due_to_step_relation)
       apply(rename_tac ek' ck')(*strict*)
       apply(force)
      apply(rename_tac ek' ck')(*strict*)
      apply(force)
     apply(rename_tac ek' ck')(*strict*)
     apply(force)
    apply(rename_tac ek' ck')(*strict*)
    apply(erule impE)
     apply(rename_tac ek' ck')(*strict*)
     apply(force)
    apply(rename_tac ek' ck')(*strict*)
    apply(force)
   apply(rename_tac ek' ck')(*strict*)
   apply(rule belongs_step_labels)
    apply(rename_tac ek' ck')(*strict*)
    apply(force)
   apply(rename_tac ek' ck')(*strict*)
   apply(force)
  apply(rule_tac
      m="i+j"
      in pre_some_position_is_some_position_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma context_extend_preserves_string_state_prefix: "
  TSstructure M
  \<Longrightarrow> decreasing
  \<Longrightarrow> belongs M d
  \<Longrightarrow> derivation M d
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> derivation M d'
  \<Longrightarrow> (\<And>c1 c2 e w.
  step_relation M c1 e c2
  \<Longrightarrow> step_relation M (C c1) e (C c2)
  \<Longrightarrow> string_state c1 = w @ string_state c2
  \<Longrightarrow> string_state (C c1) = w @ string_state (C c2))
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow>
(\<lambda>x. case x of None \<Rightarrow> True | Some (pair e c) \<Rightarrow>
  (\<lambda>x. case x of None \<Rightarrow> False | Some (pair e c') \<Rightarrow> c = C c'
  \<and> (\<exists>w. string_state c1 = w @ (string_state c'))
  \<and> (\<forall>w. string_state c1 = w @ (string_state c') \<longrightarrow> string_state (C c1) = w @ (string_state c))
  ) (d n)
) (d' n)"
  apply(rule_tac m="0" and n="n" in property_preseved_under_steps_is_invariant2_prime)
     apply(clarsimp)
     apply(simp add: derivation_map_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(case_tac "derivation_map d C (Suc i)")
   apply(rename_tac i option b)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba)(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac i option b optiona ba)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in pre_some_position_is_some_position)
     apply(rename_tac i option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac i option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac i option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac i option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba e c)(*strict*)
  apply(case_tac "derivation_map d C i")
   apply(rename_tac i option b optiona ba e c)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b optiona ba e c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i option b optiona ba e c a optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
  apply(subgoal_tac "e=optionb \<and> option=optiona")
   apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b optiona ba c optionb w)(*strict*)
  apply(subgoal_tac "ba = C b")
   apply(rename_tac i b optiona ba c optionb w)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
  apply(rename_tac i b optiona ba c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b optiona c optionb w)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i b optiona c optionb w)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac i b optiona c optionb w)(*strict*)
      apply(force)
     apply(rename_tac i b optiona c optionb w)(*strict*)
     apply(force)
    apply(rename_tac i b optiona c optionb w)(*strict*)
    apply(force)
   apply(rename_tac i b optiona c optionb w)(*strict*)
   apply(clarsimp)
  apply(rename_tac i b optiona c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "step_relation M c e b")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac i b c optionb w e)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "e \<in> step_labels M")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(simp add: belongs_def)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "\<exists>w. string_state c = w @ (string_state b)")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(rule AX_string_state_decreases)
      apply(rename_tac i b c optionb w e)(*strict*)
      apply(force)
     apply(rename_tac i b c optionb w e)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e)(*strict*)
    apply(simp add: belongs_def)
    apply(erule_tac
      x="i"
      in allE)+
    apply(force)
   apply(rename_tac i b c optionb w e)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b c optionb w e wa)(*strict*)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(erule_tac
      x="b"
      in meta_allE)
  apply(erule_tac
      x="e"
      in meta_allE)
  apply(erule_tac
      x="wa"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(rule_tac
      d="derivation_map d C"
      in position_change_due_to_step_relation)
     apply(rename_tac i b c optionb w e wa)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e wa)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa)(*strict*)
  apply(force)
  done

lemma context_extend_preserves_string_state_suffix: "
  TSstructure M
  \<Longrightarrow> \<not> decreasing
  \<Longrightarrow> belongs M d
  \<Longrightarrow> derivation M d
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> derivation M d'
  \<Longrightarrow> (\<And>c1 c2 e w i e'.
  d i = Some (pair e' c1)
  \<Longrightarrow> d (Suc i) = Some (pair (Some e) c2)
  \<Longrightarrow> step_relation M c1 e c2
  \<Longrightarrow> step_relation M (C c1) e (C c2)
  \<Longrightarrow> string_state c1 @ w = string_state c2
  \<Longrightarrow> string_state (C c1) @ w= string_state (C c2))
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow>
(\<lambda>x. case x of None \<Rightarrow> True | Some (pair e c) \<Rightarrow>
  (\<lambda>x. case x of None \<Rightarrow> False | Some (pair e c') \<Rightarrow> c = C c'
  \<and> (\<exists>w. string_state c1 @ w = (string_state c'))
  \<and> (\<forall>w. string_state c1 @ w = (string_state c') \<longrightarrow> string_state (C c1) @ w = (string_state c))
  ) (d n)
) (d' n)"
  apply(rule_tac m="0" and n="n" in property_preseved_under_steps_is_invariant2_prime)
     apply(clarsimp)
     apply(simp add: derivation_map_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(case_tac "derivation_map d C (Suc i)")
   apply(rename_tac i option b)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba)(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac i option b optiona ba)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in pre_some_position_is_some_position)
     apply(rename_tac i option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac i option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac i option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac i option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba e c)(*strict*)
  apply(case_tac "derivation_map d C i")
   apply(rename_tac i option b optiona ba e c)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b optiona ba e c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i option b optiona ba e c a optionb bb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
  apply(subgoal_tac "e=optionb \<and> option=optiona")
   apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
  apply(rename_tac i option b optiona ba e c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b optiona ba c optionb w)(*strict*)
  apply(subgoal_tac "ba = C b")
   apply(rename_tac i b optiona ba c optionb w)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
  apply(rename_tac i b optiona ba c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b optiona c optionb w)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i b optiona c optionb w)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in pre_some_position_is_some_position_prime)
      apply(rename_tac i b optiona c optionb w)(*strict*)
      apply(force)
     apply(rename_tac i b optiona c optionb w)(*strict*)
     apply(force)
    apply(rename_tac i b optiona c optionb w)(*strict*)
    apply(force)
   apply(rename_tac i b optiona c optionb w)(*strict*)
   apply(clarsimp)
  apply(rename_tac i b optiona c optionb w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "step_relation M c e b")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(rule position_change_due_to_step_relation)
     apply(rename_tac i b c optionb w e)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "e \<in> step_labels M")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(simp add: belongs_def)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(subgoal_tac "\<exists>w. string_state c @ w= (string_state b)")
   apply(rename_tac i b c optionb w e)(*strict*)
   prefer 2
   apply(rule AX_string_state_increases)
      apply(rename_tac i b c optionb w e)(*strict*)
      apply(force)
     apply(rename_tac i b c optionb w e)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e)(*strict*)
    apply(simp add: belongs_def)
    apply(erule_tac
      x="i"
      in allE)+
    apply(force)
   apply(rename_tac i b c optionb w e)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b c optionb w e wa)(*strict*)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(erule_tac
      x="b"
      in meta_allE)
  apply(erule_tac
      x="e"
      in meta_allE)
  apply(erule_tac
      x="wa"
      in meta_allE)
  apply(erule_tac
      x="i"
      in meta_allE)
  apply(erule_tac
      x="optionb"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(rule_tac
      d="derivation_map d C"
      in position_change_due_to_step_relation)
     apply(rename_tac i b c optionb w e wa)(*strict*)
     apply(force)
    apply(rename_tac i b c optionb w e wa)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(rule_tac
      x="w@wa"
      in exI)
   apply(rule_tac
      t="string_state b"
      and s="string_state c @ wa"
      in ssubst)
    apply(rename_tac i b c optionb w e wa)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(rule_tac
      t="string_state c"
      and s="string_state c1 @ w"
      in ssubst)
    apply(rename_tac i b c optionb w e wa)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac i b c optionb w e wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(erule_tac
      x="w"
      in allE)
  apply(erule impE)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(rule_tac
      t="string_state b"
      and s="string_state c @ wa"
      in ssubst)
    apply(rename_tac i b c optionb w e wa wb)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(rule_tac
      t="string_state c"
      and s="string_state c1 @ w"
      in ssubst)
    apply(rename_tac i b c optionb w e wa wb)(*strict*)
    apply(force)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(rule_tac
      t="string_state (C b)"
      and s="string_state (C c) @ wa"
      in ssubst)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(rule_tac
      t="string_state (C c)"
      and s="string_state (C c1) @ w"
      in ssubst)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(rule_tac
      t="wb"
      and s="w@wa"
      in ssubst)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   prefer 2
   apply(simp (no_asm_use))
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(case_tac "wb=w@wa")
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(subgoal_tac "string_state c1 @ wb\<noteq>string_state b")
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(rule_tac
      t="string_state b"
      and s="string_state c @ wa"
      in ssubst)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(rule_tac
      t="string_state c"
      and s="string_state c1 @ w"
      in ssubst)
   apply(rename_tac i b c optionb w e wa wb)(*strict*)
   apply(force)
  apply(rename_tac i b c optionb w e wa wb)(*strict*)
  apply(simp (no_asm_use))
  done

end

end
