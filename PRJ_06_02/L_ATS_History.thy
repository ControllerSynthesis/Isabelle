section {*L\_ATS\_History*}
theory
  L_ATS_History

imports
  PRJ_06_02__ENTRY

begin

locale ATS_History =
  ATS
  "TSstructure :: 'TSstructure \<Rightarrow> bool"
  "configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "initial_configurations :: 'TSstructure \<Rightarrow> 'conf set"
  "step_labels :: 'TSstructure \<Rightarrow> 'label set"
  "step_relation :: 'TSstructure \<Rightarrow> 'conf \<Rightarrow> 'label \<Rightarrow> 'conf \<Rightarrow> bool"
  for
    TSstructure configurations initial_configurations step_labels step_relation
    +

fixes histories :: "'TSstructure \<Rightarrow> 'history set"
fixes history_fragments :: "'TSstructure \<Rightarrow> 'history_fragment set"
fixes empty_history :: "'TSstructure \<Rightarrow> 'history"
fixes empty_history_fragment :: "'TSstructure \<Rightarrow> 'history_fragment"
fixes set_history :: "'conf \<Rightarrow> 'history \<Rightarrow> 'conf"
fixes extend_history :: "'history \<Rightarrow> 'history_fragment \<Rightarrow> 'history"
fixes join_history_fragments :: "'history_fragment \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment"
fixes get_history :: "'conf \<Rightarrow> 'history"

assumes AX_initial_history_empty: "
  TSstructure G
  \<Longrightarrow> c \<in> initial_configurations G
  \<Longrightarrow> get_history c = empty_history G"

assumes AX_steps_extend_history: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> step_relation G c e c'
  \<Longrightarrow> \<exists>hf \<in> history_fragments G. get_history c' = extend_history (get_history c) hf"

assumes AX_empty_history_is_history: "
  TSstructure G
  \<Longrightarrow> empty_history G \<in> histories G"

assumes AX_empty_history_fragment_is_history_fragment: "
  TSstructure G
  \<Longrightarrow> empty_history_fragment G \<in> history_fragments G"

assumes AX_set_get_history: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> set_history c (get_history c) = c"

assumes AX_get_set_history: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> h \<in> histories G
  \<Longrightarrow> get_history (set_history c h) = h"

assumes AX_extend_history_empty1: "
  TSstructure G
  \<Longrightarrow> h \<in> histories G
  \<Longrightarrow> extend_history h (empty_history_fragment G) = h"

assumes AX_extend_history_empty2: "
  TSstructure G
  \<Longrightarrow> h \<in> histories G
  \<Longrightarrow> extend_history h hf = h
  \<Longrightarrow> hf = empty_history_fragment G"

assumes AX_extend_history_add: "
  TSstructure G
  \<Longrightarrow> h \<in> histories G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> extend_history h (join_history_fragments hf1 hf2) = h1
  \<Longrightarrow> extend_history (extend_history h hf1) hf2 = h2
  \<Longrightarrow> h1 = h2"

assumes AX_join_history_fragments_closed: "
  TSstructure G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> join_history_fragments hf1 hf2 \<in> history_fragments G"

assumes AX_join_history_fragments_empty1: "
  TSstructure G
  \<Longrightarrow> hf \<in> history_fragments G
  \<Longrightarrow> join_history_fragments hf (empty_history_fragment G) = hf"

assumes AX_join_history_fragments_empty2: "
  TSstructure G
  \<Longrightarrow> hf \<in> history_fragments G
  \<Longrightarrow> join_history_fragments (empty_history_fragment G) hf = hf"

assumes AX_join_history_fragments_asso: "
  TSstructure G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> hf3 \<in> history_fragments G
  \<Longrightarrow> join_history_fragments (join_history_fragments hf1 hf2) hf3 = join_history_fragments hf1 (join_history_fragments hf2 hf3)"

assumes AX_get_history_closed: "
  TSstructure G
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> get_history c \<in> histories G"

assumes AX_join_history_fragments_injective: "
  TSstructure G
  \<Longrightarrow> h \<in> histories G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> extend_history h hf1 = h'
  \<Longrightarrow> extend_history h hf2 = h'
  \<Longrightarrow> hf1 = hf2"

assumes AX_mutual_prefix: "
  TSstructure G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> hf3 \<in> history_fragments G
  \<Longrightarrow> hf4 \<in> history_fragments G
  \<Longrightarrow> join_history_fragments hf1 hf2 = join_history_fragments hf3 hf4
  \<Longrightarrow> (\<exists>hf \<in> history_fragments G. join_history_fragments hf1 hf = hf3)
  \<or> (\<exists>hf \<in> history_fragments G. join_history_fragments hf3 hf = hf1)"

context ATS_History begin

definition history_fragment_prefixes :: "'TSstructure \<Rightarrow> 'history_fragment \<Rightarrow> 'history_fragment set" where
  "history_fragment_prefixes G hf = {hf'\<in> history_fragments G.
  \<exists>hf''\<in> history_fragments G.
  join_history_fragments hf' hf'' = hf
  }"

lemma steps_extend_history_derivation: "
  TSstructure G
  \<Longrightarrow> derivation G d
  \<Longrightarrow> c \<in> configurations G
  \<Longrightarrow> get_configuration (d n) = Some c
  \<Longrightarrow> get_configuration (d (n+m)) = Some c'
  \<Longrightarrow> \<exists>h\<in> history_fragments G. get_history c' = extend_history (get_history c) h"
  apply(induct m arbitrary: c')
   apply(rename_tac c')(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="empty_history_fragment G"
      in bexI)
    apply(rule sym)
    apply(rule AX_extend_history_empty1)
     apply(force)
    apply(rule AX_get_history_closed)
     apply(force)
    apply(force)
   apply(rule AX_empty_history_fragment_is_history_fragment)
   apply(force)
  apply(rename_tac m c')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+m) = Some (pair e1 c1) \<and> d (Suc (n+m)) = Some (pair (Some e2) c2) \<and> step_relation G c1 e2 c2")
   apply(rename_tac m c')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(n+m)"
      in step_detail_before_some_position)
     apply(rename_tac m c')(*strict*)
     apply(force)
    apply(rename_tac m c')(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d (Suc (n + m))")
     apply(rename_tac m c')(*strict*)
     apply(clarsimp)
    apply(rename_tac m c' a)(*strict*)
    apply(clarsimp)
   apply(rename_tac m c')(*strict*)
   apply(force)
  apply(rename_tac m c')(*strict*)
  apply(clarsimp)
  apply(rename_tac m c' e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac m c' e1 e2 c1 h)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac m c' e1 e2 c1 h)(*strict*)
   apply(clarsimp)
  apply(rename_tac m c' e1 e2 c1 h a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac m c' e1 e2 c1 h a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
  apply(subgoal_tac "\<exists>hf\<in> history_fragments G. get_history c' = extend_history (get_history c1) hf")
   apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
   prefer 2
   apply(rule AX_steps_extend_history)
     apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
     apply(force)
    apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
    apply(rule stays_in_configuration)
         apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
         apply(force)
        apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
        apply(force)
       apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
      apply(force)
     apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
    apply(force)
   apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
   apply(force)
  apply(rename_tac m c' e1 e2 c1 h option)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
  apply(rule_tac
      x="join_history_fragments h hf"
      in bexI)
   apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
   apply(rule_tac
      t="get_history c1"
      and s="extend_history (get_history c) h"
      in ssubst)
    apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
    apply(force)
   apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
   apply(rule sym)
   apply(rule AX_extend_history_add)
        apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
        apply(force)
       apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
     apply(rule AX_get_history_closed)
      apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
      apply(force)
     apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
     apply(force)
    apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
    apply(force)
   apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
   apply(force)
  apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
  apply(rule AX_join_history_fragments_closed)
    apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
    apply(force)
   apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
   apply(force)
  apply(rename_tac m c' e1 e2 c1 h option hf)(*strict*)
  apply(force)
  done

lemma history_fragment_prefixes: "
  TSstructure G
  \<Longrightarrow> hf1 \<in> history_fragments G
  \<Longrightarrow> hf2 \<in> history_fragments G
  \<Longrightarrow> hf3 \<in> history_fragments G
  \<Longrightarrow> hf4 \<in> history_fragments G
  \<Longrightarrow> join_history_fragments hf1 hf2 = join_history_fragments hf3 hf4
  \<Longrightarrow> hf1 \<in> history_fragment_prefixes G hf3
  \<or> hf3 \<in> history_fragment_prefixes G hf1"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?hf1.0="hf1"
      and ?hf2.0="hf2"
      and ?hf3.0="hf3"
      and ?hf4.0="hf4"
      in AX_mutual_prefix)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: history_fragment_prefixes_def)
  done

end

end
