section {*FUNCTION\_\_EPDA\_GOTO*}
theory
  FUNCTION__EPDA_GOTO

imports
  PRJ_12_06_01__ENTRY

begin

lemma EX1_F_EPDA_GOTO_for_complete_DFA: "
  valid_dfa G
  \<Longrightarrow> e \<in> epda_delta G
  \<Longrightarrow> edge_src e = q
  \<Longrightarrow> edge_event e = Some A
  \<Longrightarrow> every_state_in_some_accessible_configuration G
  \<Longrightarrow> \<exists>!x. x \<in> F_EPDA_GOTO G q A"
  apply(rule ex_ex1I)
   apply(clarsimp)
   apply(simp add: F_EPDA_GOTO_def)
   apply(rule_tac
      x="edge_trg e"
      in exI)
   apply(subgoal_tac "\<lparr>edge_src = edge_src e, edge_event = Some A, edge_pop = [epda_box G], edge_push = [epda_box G], edge_trg = edge_trg e\<rparr>=e")
    apply(clarsimp)
   apply(case_tac e)
   apply(rename_tac edge_srca edge_eventa edge_pop edge_push edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac edge_src edge_pop edge_push edge_trg)(*strict*)
   apply(simp add: valid_dfa_def)
   apply(rename_tac edge_src edge_popa edge_pusha edge_trg)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>edge_src = edge_src, edge_event = Some A, edge_pop = edge_popa, edge_push = edge_pusha, edge_trg = edge_trg\<rparr>"
      in ballE)
    apply(rename_tac edge_src edge_popa edge_pusha edge_trg)(*strict*)
    apply(clarsimp)
   apply(rename_tac edge_src edge_pop edge_push edge_trg)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(clarsimp)
  apply(simp add: F_EPDA_GOTO_def)
  apply(simp add: valid_dfa_def)
  apply(clarsimp)
  apply(simp add: valid_dpda_def)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac x y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(clarsimp)
  apply(simp add: every_state_in_some_accessible_configuration_def)
  apply(erule_tac
      x="edge_src e"
      in ballE)
   apply(rename_tac x y)(*strict*)
   prefer 2
   apply(simp add: valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      and P="\<lambda>x. valid_epda_step_label G x"
      in ballE)
    apply(rename_tac x y)(*strict*)
    apply(simp add: valid_epda_step_label_def)
   apply(rename_tac x y)(*strict*)
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="[A]"
      in allE)
  apply(erule impE)
   apply(rename_tac x y)(*strict*)
   apply(simp add: valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      and P="\<lambda>x. valid_epda_step_label G x"
      in ballE)
    apply(rename_tac x y)(*strict*)
    apply(simp add: valid_epda_step_label_def)
    apply(simp add: option_to_set_def)
   apply(rename_tac x y)(*strict*)
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = edge_src e, epdaS_conf_scheduler = [A], epdaS_conf_stack = [epda_box G]\<rparr>"
      in ballE)
   apply(rename_tac x y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = x, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in allE)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state = y, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box G]\<rparr>"
      in allE)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = edge_src e, edge_event = Some A, edge_pop = [epda_box G], edge_push = [epda_box G], edge_trg = x\<rparr>"
      in allE)
  apply(rename_tac x y)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = edge_src e, edge_event = Some A, edge_pop = [epda_box G], edge_push = [epda_box G], edge_trg = y\<rparr>"
      in allE)
  apply(rename_tac x y)(*strict*)
  apply(erule impE)
   apply(rename_tac x y)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x y)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(simp add: option_to_list_def)
  done

lemma F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA: "
  valid_dfa G
  \<Longrightarrow> some_step_from_every_configuration G
  \<Longrightarrow> every_state_in_some_accessible_configuration G
  \<Longrightarrow> q \<in> epda_states G
  \<Longrightarrow> A \<in> epda_events G
  \<Longrightarrow> F_DFA_GOTO G q A \<in> F_EPDA_GOTO G q A"
  apply(simp add: F_DFA_GOTO_def)
  apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO G q A")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="THE_default q (\<lambda>x. x \<in> F_EPDA_GOTO G q A)"
      and s="x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule Fun_Def.THE_default1_equality)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(blast)
  apply(simp add: some_step_from_every_configuration_def)
  apply(erule_tac
      x="q"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="A"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
      apply(rename_tac e)(*strict*)
      apply(blast)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

lemma F_EPDA_GOTO_closed_for_states: "
  valid_dfa M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> p \<in> F_EPDA_GOTO M q a
  \<Longrightarrow> p \<in> epda_states M"
  apply(simp add: F_EPDA_GOTO_def)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(auto)
  apply(erule_tac
      x="\<lparr>edge_src = q, edge_event = Some a, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = p\<rparr>"
      and P="\<lambda>x. valid_epda_step_label M x"
      in ballE)
   apply(simp add: valid_epda_step_label_def)
  apply(auto)
  done

lemma F_EPDA_GOTO_SEQUENCESound_main: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> qseq \<in> F_EPDA_GOTO_SEQUENCE M q w
  \<Longrightarrow> length w = length qseq \<and> (\<forall>i < length w. qseq ! i \<in> F_EPDA_GOTO M ((q # qseq) ! i) (w ! i)) \<and> set qseq \<subseteq> epda_states M"
  apply(induct w arbitrary: qseq q)
   apply(rename_tac qseq q)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w qseq q)(*strict*)
  apply(subgoal_tac "\<exists>a qseq'. qseq=a#qseq'")
   apply(rename_tac a w qseq q)(*strict*)
   prefer 2
   apply(simp add: F_EPDA_GOTO_SEQUENCE_def)
   apply(clarsimp)
  apply(rename_tac a w qseq q)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q p p_seq)(*strict*)
  apply(subgoal_tac "p \<in> epda_states M")
   apply(rename_tac a w q p p_seq)(*strict*)
   prefer 2
   apply(rule F_EPDA_GOTO_closed_for_states)
      apply(rename_tac a w q p p_seq)(*strict*)
      apply(force)
     apply(rename_tac a w q p p_seq)(*strict*)
     apply(force)
    apply(rename_tac a w q p p_seq)(*strict*)
    apply(force)
   apply(rename_tac a w q p p_seq)(*strict*)
   apply(force)
  apply(rename_tac a w q p p_seq)(*strict*)
  apply(erule_tac
      x="p_seq"
      in meta_allE)
  apply(erule_tac
      x="p"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac a w q p p_seq)(*strict*)
   apply(force)
  apply(rename_tac a w q p p_seq)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q p p_seq i)(*strict*)
  apply(case_tac i)
   apply(rename_tac a w q p p_seq i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q p p_seq i nat)(*strict*)
  apply(clarsimp)
  done

lemma F_EPDA_GOTO_SEQUENCESound_main1: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> qseq \<in> F_EPDA_GOTO_SEQUENCE M q w
  \<Longrightarrow> length w = length qseq"
  apply(simp add: F_EPDA_GOTO_SEQUENCESound_main)
  done

lemma F_EPDA_GOTO_SEQUENCESound_main2: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> qseq \<in> F_EPDA_GOTO_SEQUENCE M q w
  \<Longrightarrow> \<forall>i < length w. qseq ! i \<in> F_EPDA_GOTO M ((q # qseq) ! i) (w ! i)"
  apply(simp add: F_EPDA_GOTO_SEQUENCESound_main)
  done

lemma F_EPDA_GOTO_SEQUENCESound_main3: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> qseq \<in> F_EPDA_GOTO_SEQUENCE M q w
  \<Longrightarrow> set qseq \<subseteq> epda_states M"
  apply(simp add: F_EPDA_GOTO_SEQUENCESound_main)
  done

lemma F_EPDA_GOTO_to_derivation: "
  valid_pda M
  \<Longrightarrow> F_EPDA_GOTO M q A = {q'. \<exists>d e. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [A], epdaS_conf_stack = [epda_box M]\<rparr>) \<and> d (Suc 0) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>) \<and> maximum_of_domain d (Suc 0)}"
  apply(simp add: F_EPDA_GOTO_def)
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x = "\<lambda>n. if n = 0 then Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [A], epdaS_conf_stack = [epda_box M]\<rparr>) else (if n = Suc 0 then Some (pair (Some \<lparr>edge_src = q, edge_event = Some A, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = x\<rparr>) \<lparr>epdaS_conf_state = x, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>) else None)"
      in exI)
   apply(rename_tac x)(*strict*)
   apply(rule conjI)
    apply(rename_tac x)(*strict*)
    apply(fold der2_def)
    apply(rule epdaS.der2_is_derivation)
    apply(simp add: epdaS_step_relation_def)
    apply(simp add: option_to_list_def)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac x d e)(*strict*)
  apply(subgoal_tac "\<exists>e'. Some e'=e")
   apply(rename_tac x d e)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d e')(*strict*)
   apply(subgoal_tac "epdaS_step_relation M \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [A], epdaS_conf_stack = [epda_box M]\<rparr> e' \<lparr>epdaS_conf_state = x,epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>")
    apply(rename_tac x d e')(*strict*)
    apply(subgoal_tac "e'=\<lparr>edge_src = q, edge_event = Some A, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = x\<rparr>")
     apply(rename_tac x d e')(*strict*)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac x d e')(*strict*)
    prefer 2
    apply(rule epdaS.position_change_due_to_step_relation)
      apply(rename_tac x d e')(*strict*)
      apply(blast)
     apply(rename_tac x d e')(*strict*)
     apply(blast)
    apply(rename_tac x d e')(*strict*)
    apply(blast)
   apply(rename_tac x d e')(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d e' w)(*strict*)
   apply(case_tac e')
   apply(rename_tac d e' w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w edge_src edge_event edge_pop edge_trg)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac edge_event)
    apply(rename_tac d w edge_src edge_event edge_pop edge_trg)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w edge_src edge_event edge_pop edge_trg a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w edge_src edge_pop edge_trg)(*strict*)
   apply(simp add: valid_pda_def)
   apply(rename_tac d w edge_src edge_popa edge_trg)(*strict*)
   apply(auto)
   apply(erule_tac
      x="\<lparr>edge_src = edge_src, edge_event = Some A, edge_pop = edge_popa, edge_push = edge_popa, edge_trg = edge_trg\<rparr>"
      in ballE)
    apply(rename_tac d w edge_src edge_popa edge_trg)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w edge_src edge_pop edge_trg)(*strict*)
    apply(case_tac "edge_pop")
     apply(rename_tac d w edge_src edge_pop edge_trg)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w edge_src edge_pop edge_trg a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w edge_src edge_pop edge_trg)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d e)(*strict*)
  apply(case_tac e)
   apply(rename_tac x d e)(*strict*)
   apply(rule epdaS.derivation_Always_PreEdge_prime)
    apply(rename_tac x d e)(*strict*)
    apply(blast)+
  done

theorem F_EPDA_GOTO_SEQUENCE_to_derivation: "
  valid_dfa M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_EPDA_GOTO_SEQUENCE M q w = {qseq. \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>) \<and> q # qseq = map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w) }"
  apply(induct w arbitrary: q)
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq 0 0 = [0]")
    apply(rename_tac q)(*strict*)
    apply(rule order_antisym)
     apply(rename_tac q)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      x = "\<lambda>n. if n = 0 then Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>) else None"
      in exI)
     apply(rename_tac q)(*strict*)
     apply(clarsimp)
     apply(fold der1_def)
     apply(rule conjI)
      apply(rename_tac q)(*strict*)
      apply(rule epdaS.der1_is_derivation)
     apply(rename_tac q)(*strict*)
     apply(rule conjI)
      apply(rename_tac q)(*strict*)
      apply(simp add: get_configurations_def get_configuration_def der1_def)
     apply(rename_tac q)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac q)(*strict*)
    apply(simp add: get_configurations_def get_configuration_def der1_def)
    prefer 2
    apply(rule natUptTo_n_n)
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q)(*strict*)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(rename_tac a w q)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p p_seq)(*strict*)
   apply(erule_tac
      x="p"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac a w q p p_seq)(*strict*)
    apply(simp add: F_EPDA_GOTO_def)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>edge_src = q, edge_event = Some a, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = p\<rparr>"
      and P="\<lambda>x. valid_epda_step_label M x"
      in ballE)
     apply(rename_tac a w q p p_seq)(*strict*)
     apply(simp add: valid_epda_step_label_def)
    apply(rename_tac a w q p p_seq)(*strict*)
    apply(force)
   apply(rename_tac a w q p p_seq)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs)(*strict*)
   apply(thin_tac "F_EPDA_GOTO_SEQUENCE M p w = {qseq. \<exists>d. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = p, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> (\<exists>e q'. d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<and> p # qseq = map (case_option p epdaS_conf_state) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)}")
   apply(rename_tac a w q p d e q' z zs)(*strict*)
   apply(subgoal_tac "\<exists>d e. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=[a],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (Suc 0) = Some (pair e \<lparr>epdaS_conf_state=p,epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> maximum_of_domain d (Suc 0)")
    apply(rename_tac a w q p d e q' z zs)(*strict*)
    prefer 2
    apply(subgoal_tac "F_EPDA_GOTO M q a = {q'. \<exists>d e. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=[a],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (Suc 0) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> maximum_of_domain d (Suc 0)}")
     apply(rename_tac a w q p d e q' z zs)(*strict*)
     prefer 2
     apply(rule F_EPDA_GOTO_to_derivation)
     apply(simp add: valid_dfa_def valid_dpda_def)
    apply(rename_tac a w q p d e q' z zs)(*strict*)
    apply(blast)
   apply(rename_tac a w q p d e q' z zs)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(rule_tac
      x="derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler:=(epdaS_conf_scheduler v)@w\<rparr>)) (derivation_map d (\<lambda>v. v)) (Suc 0)"
      in exI)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(rule epdaS.derivation_concat2)
       apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
       apply(rule epdaS.derivation_map_preserves_derivation2)
        apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
        apply(blast)
       apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
       apply(clarsimp)
       apply(rename_tac a w q p d e q' z zs da ea aa eb b)(*strict*)
       apply(simp add: epdaS_step_relation_def)
      apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(blast)
     apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
     apply(rule epdaS.derivation_map_preserves_derivation2)
      apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
      apply(blast)
     apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(simp add: derivation_append_def)
    apply(simp add: derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(case_tac w)
     apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
     apply(rule_tac
      x="ea"
      in exI)
     apply(rule_tac
      x="p"
      in exI)
     apply(simp add: derivation_append_def)
     apply(simp add: derivation_map_def)
    apply(rename_tac a w q p d e q' z zs da ea aa list)(*strict*)
    apply(rule_tac
      x="e"
      in exI)
    apply(rule_tac
      x="q'"
      in exI)
    apply(simp add: derivation_append_def)
    apply(simp add: derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    prefer 2
    apply(rule_tac
      t="Suc (length w)"
      and s="Suc 0+length w"
      in ssubst)
     apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
     apply(arith)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
     apply(simp add: maximum_of_domain_def derivation_map_def)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(simp add: maximum_of_domain_def derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(subgoal_tac "length (get_configurations d (length w)) = Suc (length w)")
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    prefer 2
    apply(rule get_configurations_length)
   apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
   apply(clarsimp)
   apply(rule listEqI)
    apply(rename_tac a w q p d e q' z zs da ea)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule get_configurations_length)
   apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
   apply(rule impI)
   apply(rule_tac
      t="map (case_option q epdaS_conf_state) (get_configurations (derivation_append (\<lambda>n. case da n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (c\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler c @ w\<rparr>))) d (Suc 0)) (Suc (length w))) ! i"
      and s="(case_option q epdaS_conf_state) ((get_configurations (derivation_append (\<lambda>n. case da n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (c\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler c @ w\<rparr>))) d (Suc 0)) (Suc (length w))) ! i)"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(rule nth_map)
    apply(rule_tac
      t="length (get_configurations (derivation_append (\<lambda>n. case da n of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some (pair e (c\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler c @ w\<rparr>))) d (Suc 0)) (Suc (length w)))"
      and s="Suc (Suc (length w))"
      in ssubst)
     apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
     apply(rule get_configurations_length)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
   apply(clarsimp)
   apply(simp (no_asm) add: get_configurations_def)
   apply(rule_tac
      t=" map (case_option q epdaS_conf_state \<circ> (\<lambda>i. get_configuration (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ w\<rparr>)) (derivation_map d (\<lambda>v. v)) (Suc 0) i))) (nat_seq 0 (Suc (length w))) ! i"
      and s=" (case_option q epdaS_conf_state \<circ> (\<lambda>i. get_configuration (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ w\<rparr>)) (derivation_map d (\<lambda>v. v)) (Suc 0) i))) ((nat_seq 0 (Suc (length w))) ! i)"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(rule nth_map)
    apply(rule_tac
      t="length (nat_seq 0 (Suc (length w)))"
      and s="Suc (length w) - 0 + 1"
      in ssubst)
     apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
     apply(rule nat_seq_length)
     apply(blast)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
   apply(rule_tac
      t="nat_seq 0 (Suc (length w)) ! i"
      and s="0+i"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
     apply(blast)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(arith)
   apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac a w q p d e q' z zs da ea i)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea nat)(*strict*)
   apply(case_tac nat)
    apply(rename_tac a w q p d e q' z zs da ea nat)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def derivation_map_def)
   apply(rename_tac a w q p d e q' z zs da ea nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea nata)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def derivation_map_def)
   apply(subgoal_tac "\<exists>e c. d (Suc nata) = Some (pair (Some e) c)")
    apply(rename_tac a w q p d e q' z zs da ea nata)(*strict*)
    prefer 2
    apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac a w q p d e q' z zs da ea nata)(*strict*)
      apply(blast)+
    apply(rename_tac a w q p d e q' z zs da ea nata)(*strict*)
    apply(arith)
   apply(rename_tac a w q p d e q' z zs da ea nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(rule_tac
      t="zs ! nata"
      and s="(z#zs)!(Suc nata)"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(force)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(subgoal_tac "(z#zs)!(Suc nata)=Some c")
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(force)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(rule_tac
      s="get_configurations d (length w) ! (Suc nata)"
      and t="(z#zs)!(Suc nata)"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(rule_tac
      f="\<lambda>x. x!(Suc nata)"
      in HOL.arg_cong)
    apply(force)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(simp (no_asm) add: get_configurations_def)
   apply(rule_tac
      s="(\<lambda>i. get_configuration (d i)) ((nat_seq 0 (length w)) ! (Suc nata))"
      and t="map (\<lambda>i. get_configuration (d i)) (nat_seq 0 (length w)) ! Suc nata"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(rule nth_map)
    apply(rule_tac
      t="length (nat_seq 0 (length w))"
      and s="length w - 0 + 1"
      in ssubst)
     apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
     apply(rule nat_seq_length)
     apply(blast)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(arith)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(rule_tac
      t="nat_seq 0 ((length w)) ! (Suc nata)"
      and s="0+(Suc nata)"
      in ssubst)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
     apply(blast)
    apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
    apply(arith)
   apply(rename_tac a w q p d e q' z zs da ea nata eb c)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac a w q)(*strict*)
  apply(subgoal_tac "\<And>q. q \<in> epda_states M \<Longrightarrow> F_EPDA_GOTO_SEQUENCE M q w \<supseteq> {qseq. \<exists>d. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> (\<exists>e q'. d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<and> q # qseq = map (case_option q epdaS_conf_state) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)}")
   apply(rename_tac a w q)(*strict*)
   prefer 2
   apply(rename_tac a w q qa)(*strict*)
   apply(erule_tac
      x="qa"
      in meta_allE)
   apply(erule meta_impE)
    apply(rename_tac a w q qa)(*strict*)
    apply(force)
   apply(rename_tac a w q qa)(*strict*)
   apply(simp (no_asm_simp))
  apply(rename_tac a w q)(*strict*)
  apply(thin_tac "\<And>q. q \<in> epda_states M \<Longrightarrow> F_EPDA_GOTO_SEQUENCE M q w = {qseq. \<exists>d. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> (\<exists>e q'. d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<and> q # qseq = map (case_option q epdaS_conf_state) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)}")
  apply(rename_tac a w q)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q' z zs)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac a w q d e q' z zs)(*strict*)
   prefer 2
   apply(rule_tac epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac a w q d e q' z zs)(*strict*)
     apply(blast)
    apply(rename_tac a w q d e q' z zs)(*strict*)
    apply(blast)
   apply(rename_tac a w q d e q' z zs)(*strict*)
   apply(blast)
  apply(rename_tac a w q d e q' z zs)(*strict*)
  apply(erule exE)+
  apply(rename_tac a w q d e q' z zs ea c)(*strict*)
  apply(subgoal_tac "epdaS_step_relation M \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = a#w, epdaS_conf_stack = [epda_box M]\<rparr> ea c")
   apply(rename_tac a w q d e q' z zs ea c)(*strict*)
   prefer 2
   apply(rule epdaS.position_change_due_to_step_relation)
     apply(rename_tac a w q d e q' z zs ea c)(*strict*)
     apply(blast)
    apply(rename_tac a w q d e q' z zs ea c)(*strict*)
    apply(blast)
   apply(rename_tac a w q d e q' z zs ea c)(*strict*)
   apply(blast)
  apply(rename_tac a w q d e q' z zs ea c)(*strict*)
  apply(simp add: get_configurations_def)
  apply(clarsimp)
  apply(rename_tac a w q d e q' ea c za zsa)(*strict*)
  apply(case_tac c)
  apply(rename_tac a w q d e q' ea c za zsa epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q' ea za zsa epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply(rename_tac q' i s)
  apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
  apply(erule_tac
      x="q'"
      in meta_allE)
  apply(subgoal_tac "ea \<in> epda_step_labels M")
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in epdaS.belongs_step_labels)
    apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
      apply(force)
     apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
     apply(simp add: epdaS_configurations_def)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   apply(subgoal_tac "\<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = i, epdaS_conf_stack = s\<rparr> \<in> epdaS_configurations M")
    apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
    apply(simp add: epdaS_configurations_def)
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   apply(rule_tac
      d="d"
      in epdaS.belongs_configurations)
    apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
    apply(rule epdaS.derivation_belongs)
       apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
      apply(force)
     apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
     apply(simp add: epdaS_configurations_def)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
  apply(rule_tac
      x="q'"
      in exI)
  apply(case_tac zsa)
   apply(rename_tac a w q d e q'a ea za zsa q' i s)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w q d e q'a ea za q' i s)(*strict*)
   apply(subgoal_tac "length (nat_seq 0 (Suc (length w))) = Suc (length w) + 1 - 0")
    apply(rename_tac a w q d e q'a ea za q' i s)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac a w q d e q'a ea za q' i s)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea za zsa q' i s aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
  apply(subgoal_tac "za=0")
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   prefer 2
   apply(rule_tac
      t="za"
      and s="(za # aa # list)!0"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(rule_tac
      t="za # aa # list"
      and s="nat_seq 0 (Suc (length w))"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(rule_tac
      t="nat_seq 0 (Suc (length w)) ! 0"
      and s="0+0"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
     apply(force)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
  apply(subgoal_tac "aa=Suc 0")
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   prefer 2
   apply(rule_tac
      t="aa"
      and s="(za # aa # list)!1"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(rule_tac
      t="za # aa # list"
      and s="nat_seq 0 (Suc (length w))"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(rule_tac
      t="nat_seq 0 (Suc (length w)) ! 1"
      and s="0+1"
      in ssubst)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
     apply(force)
    apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea za q' i s aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x="ea"
      in ballE)
    apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
    prefer 2
    apply(simp add: epda_step_labels_def)
   apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac a w d e q'a ea i list y)(*strict*)
   apply(case_tac ea)
   apply(rename_tac a w d e q'a ea i list y edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w d e q'a i list y edge_srca edge_trg)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(rule_tac
      A="{qseq. \<exists>d. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> (\<exists>e q'. d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<and> q' # qseq = map (case_option q' epdaS_conf_state \<circ> (\<lambda>i. get_configuration (d i))) (nat_seq 0 (length w)) \<and> maximum_of_domain d (length w)}"
      in set_mp)
   apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(thin_tac "{qseq. \<exists>d. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> (\<exists>e q'. d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<and> q' # qseq = map (case_option q' epdaS_conf_state \<circ> (\<lambda>i. get_configuration (d i))) (nat_seq 0 (length w)) \<and> maximum_of_domain d (length w)} \<subseteq> F_EPDA_GOTO_SEQUENCE M q' w")
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i=w \<and> s=[epda_box M]")
   apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: option_to_list_def)
   apply(clarsimp)
   apply(rename_tac a w d e q'a ea i list wa)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac a w d e q'a ea i list wa)(*strict*)
    apply(subgoal_tac "edge_event ea\<noteq>None")
     apply(rename_tac a w d e q'a ea i list wa)(*strict*)
     apply(force)
    apply(rename_tac a w d e q'a ea i list wa)(*strict*)
    apply(rule DFA_not_none_read)
     apply(rename_tac a w d e q'a ea i list wa)(*strict*)
     apply(force)
    apply(rename_tac a w d e q'a ea i list wa)(*strict*)
    apply(force)
   apply(rename_tac a w d e q'a ea i list wa)(*strict*)
   apply(rule DFA_push_pop_eq)
    apply(rename_tac a w d e q'a ea i list wa)(*strict*)
    apply(force)
   apply(rename_tac a w d e q'a ea i list wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' i s list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(rule_tac
      x="derivation_drop d (Suc 0)"
      in exI)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(rule_tac
      m = "((length w))"
      in epdaS.derivation_drop_preserves_derivation)
    apply(rename_tac a w q d e q'a ea q' list)(*strict*)
    apply(blast)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(simp add: derivation_map_def derivation_drop_def)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(simp add: derivation_map_def derivation_drop_def)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(rule conjI)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   prefer 2
   apply(rule_tac
      t="length w"
      and s="(Suc(length w))-Suc 0"
      in ssubst)
    apply(rename_tac a w q d e q'a ea q' list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(rule epdaS.derivation_drop_makes_maximum_of_domain)
     apply(rename_tac a w q d e q'a ea q' list)(*strict*)
     apply(force)
    apply(rename_tac a w q d e q'a ea q' list)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 ((length w))) = ((length w)) - 0 + 1")
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   prefer 2
   apply(rule nat_seq_length)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(subgoal_tac "length (nat_seq 0 (Suc(length w))) = (Suc(length w)) - 0 + 1")
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   prefer 2
   apply(rule nat_seq_length)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list)(*strict*)
  apply(rule listEqI)
   apply(rename_tac a w q d e q'a ea q' list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq 0 (length w) ! i"
      and s="0+i"
      in ssubst)
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
  apply(simp add: derivation_map_def derivation_drop_def get_configuration_def)
  apply(case_tac "d (Suc i)")
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "i>Suc(length w)")
    apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(case_tac "Suc (length w) < i")
    apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(rule_tac
      n="Suc i"
      in epdaS.maximum_of_domainSmaller)
      apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
      apply(force)
     apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
     apply(force)
    apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list i)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list i aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac a w q d e q'a ea q' list i aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list i option b)(*strict*)
  apply(case_tac i)
   apply(rename_tac a w q d e q'a ea q' list i option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list i option b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
  apply(subgoal_tac "list!nat = Suc(Suc nat)")
   apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
  apply(rule_tac
      t="list!nat"
      and s="(0#(Suc 0)#list)!(Suc(Suc nat))"
      in ssubst)
   apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
  apply(rule_tac
      t="0 # Suc 0 # list"
      and s="nat_seq 0 (Suc (length w))"
      in ssubst)
   apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
  apply(rule_tac
      t="nat_seq 0 (Suc (length w)) ! Suc (Suc nat)"
      and s="0+Suc (Suc nat)"
      in ssubst)
   apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
    apply(force)
   apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
   apply(force)
  apply(rename_tac a w q d e q'a ea q' list option b nat)(*strict*)
  apply(force)
  done

lemma F_EPDA_GOTO_SEQUENCE_add_tailStep: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set (w @ [a, b]) \<subseteq> (epda_events M)
  \<Longrightarrow> wa_qs \<in> F_EPDA_GOTO_SEQUENCE M q (w @ [a])
  \<Longrightarrow> b_q \<in> F_EPDA_GOTO M (last wa_qs) b
  \<Longrightarrow> wa_qs @ [b_q] \<in> F_EPDA_GOTO_SEQUENCE M q (w @ [a, b])"
  apply(subgoal_tac "b_q \<in> {q'. \<exists>d e. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=(last wa_qs),epdaS_conf_scheduler=[b],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (Suc 0) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> maximum_of_domain d (Suc 0)}")
   prefer 2
   apply(rule_tac
      P="\<lambda>y. b_q \<in> y"
      and s="F_EPDA_GOTO M (last wa_qs) b"
      in subst)
    apply(rule F_EPDA_GOTO_to_derivation)
    apply(simp add: valid_dfa_def valid_dpda_def)
   apply(force)
  apply(thin_tac "b_q \<in> F_EPDA_GOTO M (last wa_qs) b")
  apply(subgoal_tac "wa_qs \<in> {qseq. \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w@[a],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length (w@[a])) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#qseq=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length (w@[a]))) \<and> maximum_of_domain d (length (w@[a])) }")
   prefer 2
   apply(rule_tac
      P="\<lambda>y. wa_qs \<in> y"
      and s="F_EPDA_GOTO_SEQUENCE M q (w@[a])"
      in subst)
    apply(rule F_EPDA_GOTO_SEQUENCE_to_derivation)
      apply(simp add: valid_dfa_def valid_dpda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "wa_qs \<in> F_EPDA_GOTO_SEQUENCE M q (w@[a])")
  apply(rule_tac
      t="F_EPDA_GOTO_SEQUENCE M q (w@[a,b])"
      and s="{qseq. \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w@[a,b],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length (w@[a,b])) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#qseq=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length (w@[a,b]))) \<and> maximum_of_domain d (length (w@[a,b])) }"
      in ssubst)
   apply(rule F_EPDA_GOTO_SEQUENCE_to_derivation)
     apply(simp add: valid_dfa_def valid_dpda_def)
    apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler:=(epdaS_conf_scheduler v)@[b]\<rparr>)) d (length (w@[a]))"
      in exI)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(subgoal_tac "length (get_configurations da (Suc(length w))) = Suc(Suc(length w))")
   apply(rename_tac d da e ea q' z zs)(*strict*)
   prefer 2
   apply(rule get_configurations_length)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(subgoal_tac "\<forall>i<length(z # zs). \<forall>c e. da i=Some (pair e c) \<longrightarrow> (z # zs)!i=Some c")
   apply(rename_tac d da e ea q' z zs)(*strict*)
   prefer 2
   apply(rule_tac
      zs="w@[a]"
      and n="(Suc (length w))"
      in get_configurations_elem2)
     apply(rename_tac d da e ea q' z zs)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(subgoal_tac "length (get_configurations (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) (Suc (Suc (length w)))) = Suc (Suc (Suc (length w)))")
   apply(rename_tac d da e ea q' z zs)(*strict*)
   prefer 2
   apply(rule get_configurations_length)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(subgoal_tac "\<forall>i<Suc (Suc (Suc (length w))). \<forall>c e. (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) i=Some (pair e c) \<longrightarrow> ((get_configurations (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) (Suc (Suc (length w)))))!i=Some c")
   apply(rename_tac d da e ea q' z zs)(*strict*)
   prefer 2
   apply(rule_tac
      t="Suc (Suc (Suc (length w)))"
      and s="length (get_configurations (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) (Suc (Suc (length w))))"
      in ssubst)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(rule_tac
      zs="w@[a,b]"
      and n="Suc(Suc (length w))"
      in get_configurations_elem2)
     apply(rename_tac d da e ea q' z zs)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(rule epdaS.derivation_concat2)
      apply(rename_tac d da e ea q' z zs)(*strict*)
      apply(rule epdaS.derivation_map_preserves_derivation2)
       apply(rename_tac d da e ea q' z zs)(*strict*)
       apply(blast)
      apply(rename_tac d da e ea q' z zs)(*strict*)
      apply(clarsimp)
      apply(rename_tac d da e ea q' z zs aa eb ba)(*strict*)
      apply(simp add: epdaS_step_relation_def)
     apply(rename_tac d da e ea q' z zs)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(clarsimp)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
   apply(erule_tac
      x="(Suc (length w))"
      and P="\<lambda>x. x < Suc (Suc (length w)) \<longrightarrow> (\<forall>c. (\<exists>e. da x = Some (pair e c)) \<longrightarrow> (z # zs) ! x = Some c)"
      in allE)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(erule impE)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(clarsimp)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="last (map (case_option q epdaS_conf_state) zs)"
      and s="(case_option q epdaS_conf_state) (last zs)"
      in ssubst)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(rule last_map)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(rule_tac
      t="last zs"
      and s="zs!(length w)"
      in ssubst)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(rule last_nth3)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(rule_tac
      t="Suc(Suc(length w))"
      and s="((length (w@[a])))+(Suc 0)"
      in ssubst)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d da e ea q' z zs)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(clarsimp)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da e ea q' z zs)(*strict*)
  apply(rule listEqI)
   apply(rename_tac d da e ea q' z zs)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da e ea q' z zs i)(*strict*)
  apply(simp add: get_configurations_def)
  apply(clarsimp)
  apply(rename_tac d da e ea q' i za zsa)(*strict*)
  apply(rule_tac
      t="map (case_option q epdaS_conf_state) (get_configurations (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) (Suc (Suc (length w)))) ! i"
      and s="(case_option q epdaS_conf_state) (get_configurations (derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ [b]\<rparr>)) d (Suc (length w))) (Suc (Suc (length w))) ! i)"
      in ssubst)
   apply(rename_tac d da e ea q' i za zsa)(*strict*)
   apply(rule nth_map)
   apply(simp add: get_configurations_def)
  apply(rename_tac d da e ea q' i za zsa)(*strict*)
  apply(subgoal_tac "nat_seq 0 (Suc (Suc (length w))) ! i = 0+i")
   apply(rename_tac d da e ea q' i za zsa)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac d da e ea q' i za zsa)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' i za zsa)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' i za zsa)(*strict*)
  apply(case_tac i)
   apply(rename_tac d da e ea q' i za zsa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da e ea q' za zsa)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def get_configurations_def get_configuration_def)
  apply(rename_tac d da e ea q' i za zsa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(case_tac "nat=Suc(length w)")
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da e ea q' za zsa)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def get_configurations_def get_configuration_def)
   apply(rule_tac
      t="Suc(length w)"
      and s="length zsa"
      in ssubst)
    apply(rename_tac d da e ea q' za zsa)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' za zsa)(*strict*)
   apply(rule_tac
      t="length zsa"
      and s="length ((map (\<lambda>a. case case da a of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c of None \<Rightarrow> q | Some a \<Rightarrow> epdaS_conf_state a) zsa))"
      in ssubst)
    apply(rename_tac d da e ea q' za zsa)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' za zsa)(*strict*)
   apply(rule nth_append_length)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(simp (no_asm) add: derivation_append_def derivation_map_def get_configurations_def get_configuration_def)
  apply(rule_tac
      t="map (\<lambda>i. case if i \<le> Suc (length w) then case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e (c\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler c @ [b]\<rparr>)))) (da i) else case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e c))) (d (i - Suc (length w))) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c) (nat_seq 0 (Suc (Suc (length w)))) ! Suc nat"
      and s="(\<lambda>i. case if i \<le> Suc (length w) then case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e (c\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler c @ [b]\<rparr>)))) (da i) else case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e c))) (d (i - Suc (length w))) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> Some c) (nat_seq 0 (Suc (Suc (length w))) ! Suc nat)"
      in ssubst)
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(rule nth_map)
   apply(rule_tac
      t="length(nat_seq 0 (Suc (Suc (length w))))"
      and s="(Suc (Suc (length w))) - 0 + 1"
      in ssubst)
    apply(rename_tac d da e ea q' za zsa nat)(*strict*)
    apply(rule nat_seq_length)
    apply(force)
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(rule_tac
      t="(nat_seq 0 (Suc (Suc (length w)))) ! (Suc nat)"
      and s="0+(Suc nat)"
      in ssubst)
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac d da e ea q' za zsa nat)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc nat"
      and P="\<lambda>x. x < Suc (Suc (length w)) \<longrightarrow> (\<forall>c. (\<exists>e. da x = Some (pair e c)) \<longrightarrow> (get_configuration (da za) # map (\<lambda>i. get_configuration (da i)) zsa) ! x = Some c)"
      in allE)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. da (Suc nat) = Some (pair e c)")
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac d da e ea q' za zsa nat)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' za zsa nat)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' za zsa nat)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' za zsa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e ea q' za zsa nat eb c)(*strict*)
  apply(rule_tac
      t="(map (\<lambda>a. case_option q epdaS_conf_state (case_option None (case_derivation_configuration (\<lambda>e. Some)) (da a))) zsa @ [b_q]) ! nat"
      and s="(map (\<lambda>a. case_option q epdaS_conf_state (case_option None (case_derivation_configuration (\<lambda>e. Some)) (da a))) zsa) ! nat"
      in ssubst)
   apply(rename_tac d da e ea q' za zsa nat eb c)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac d da e ea q' za zsa nat eb c)(*strict*)
  apply(simp add: get_configuration_def)
  done

lemma F_DFA_GOTO_to_F_EPDA_GOTO: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> X \<in> epda_events M
  \<Longrightarrow> {F_DFA_GOTO M q X} = F_EPDA_GOTO M q X"
  apply(rule sym)
  apply(rule ex1_set)
   prefer 2
   apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
       apply(blast)+
  apply(simp add: some_step_from_every_configuration_def)
  apply(erule_tac
      x="q"
      in ballE)
   prefer 2
   apply(force)
  apply(erule_tac
      x="X"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
      apply(rename_tac e)(*strict*)
      apply(blast)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

lemma equalsFUNF_DFA_GOTO: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p \<in> epda_states M
  \<Longrightarrow> X \<in> epda_events M
  \<Longrightarrow> \<lparr>edge_src = p, edge_event = Some X, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = q\<rparr> \<in> epda_delta M
  \<Longrightarrow> q = F_DFA_GOTO M p X"
  apply(subgoal_tac "q \<in> F_EPDA_GOTO M p X")
   apply(subgoal_tac "{F_DFA_GOTO M p X}=F_EPDA_GOTO M p X")
    apply(force)
   apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
       apply(blast)+
  apply(simp add: F_EPDA_GOTO_def)
  done

lemma F_EPDA_GOTO_proves_existence_of_edge: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> x \<in> epda_events M
  \<Longrightarrow> pb \<in> F_EPDA_GOTO M p x
  \<Longrightarrow> \<lparr>edge_src = p, edge_event = Some x, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = pb\<rparr> \<in> epda_delta M"
  apply(simp add: F_EPDA_GOTO_def)
  done

lemma F_EPDA_GOTO_SEQUENCESound_main2b: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set (iw @ [ia] @ iv) \<subseteq> epda_events M
  \<Longrightarrow> length w = length iw
  \<Longrightarrow> w @ [a] @ v \<in> F_EPDA_GOTO_SEQUENCE M q (iw @ [ia] @ iv)
  \<Longrightarrow> a \<in> F_EPDA_GOTO M (last (q # w)) ia"
  apply(subgoal_tac "(\<forall>i<(length (iw@[ia]@iv)). ((w @ [a] @ v)!i) \<in> F_EPDA_GOTO M ((q#(w @ [a] @ v))!i) ((iw@[ia]@iv)!i))")
   prefer 2
   apply(rule F_EPDA_GOTO_SEQUENCESound_main2)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule_tac
      x="length w"
      in allE)
  apply(auto)
  apply(rule_tac
      t="a"
      and s="(w @ a # v) ! length iw"
      in ssubst)
   apply(rule_tac
      t="length iw"
      and s="length w"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="(w @ a # v) ! length w"
      and s="(if length w < length w then w ! length w else (a#v) ! (length w - length w))"
      in ssubst)
    apply (metis List.nth_append)
   apply(force)
  apply(rule_tac
      t="last w"
      and s="((q # w @ a # v) ! length iw)"
      in ssubst)
   apply(rule_tac
      t="length iw"
      and s="length w"
      in ssubst)
    apply(force)
   apply(thin_tac "length w=length iw")
   apply(rule_tac
      t="q # w @ a # v"
      and s="(q # w) @ (a # v)"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="((q # w) @ (a # v)) ! length w"
      and s="(if length w < length (q # w) then (q # w) ! length w else (a#v) ! (length w - length (q#w)))"
      in ssubst)
    apply (metis List.nth_append)
   apply(clarsimp)
   apply(rule last_nth3)
   apply(force)
  apply(force)
  done

theorem F_EPDA_GOTO_SEQUENCE_simulate_each_on_prefix: "
  valid_dfa M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set (wi @ v'i) \<subseteq> epda_events M
  \<Longrightarrow> w \<in> F_EPDA_GOTO_SEQUENCE M q wi
  \<Longrightarrow> w' @ v' \<in> F_EPDA_GOTO_SEQUENCE M q (wi @ v'i)
  \<Longrightarrow> length w = length wi
  \<Longrightarrow> length w' = length wi
  \<Longrightarrow> length v' = length v'i
  \<Longrightarrow> w' = w"
  apply(subgoal_tac "w \<in> {qseq. \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=wi,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length wi) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#qseq=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length wi)) \<and> maximum_of_domain d (length wi) }")
   prefer 2
   apply(rule_tac
      P="\<lambda>x. w \<in> x"
      and s="F_EPDA_GOTO_SEQUENCE M q wi"
      in subst)
    apply(rule F_EPDA_GOTO_SEQUENCE_to_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "w'@v' \<in> {qseq. \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=(wi@v'i),epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length (wi@v'i)) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#qseq=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length (wi@v'i))) \<and> maximum_of_domain d (length (wi@v'i)) }")
   prefer 2
   apply(rule_tac
      P="\<lambda>x. w'@v' \<in> x"
      and s="F_EPDA_GOTO_SEQUENCE M q (wi@v'i)"
      in subst)
    apply(rule F_EPDA_GOTO_SEQUENCE_to_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d da e q' ea q'a z zs za zsa)(*strict*)
  apply(rule listEqI)
   apply(rename_tac d da e q' ea q'a z zs za zsa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
     apply(blast)+
   apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
   apply(arith)
  apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
  apply(subgoal_tac "\<exists>e c. da (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
     apply(blast)+
   apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
   apply(arith)
  apply(rename_tac d da e q' ea q'a z zs za zsa i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "epdaS_conf_state c=epdaS_conf_state ca")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(subgoal_tac "case_option undefined (\<lambda>x. x) (get_configuration (d (Suc i))) = case_option undefined (\<lambda>c. c\<lparr>epdaS_conf_scheduler:=take ((length wi) - (Suc i)) (epdaS_conf_scheduler c)\<rparr>) (get_configuration (da (Suc i)))")
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    prefer 2
    apply(rule DFA_derivation_input_restriction_still_simulates)
               apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
               apply(force)
              apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
              apply(force)
             apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
             apply(force)
            apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
            apply(force)
           apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
           apply(force)
          apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
          apply(force)
         apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
         apply(force)
        apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
        apply(force)
       apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
       apply(force)
      apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
      apply(force)
     apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
     apply(force)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "length (get_configurations d (length wi)) = Suc (length wi)")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule get_configurations_length)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "length (get_configurations da (length wi + length v'i)) = Suc (length wi + length v'i)")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule get_configurations_length)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "\<forall>i<length(za#zsa). \<forall>c e. da i=Some (pair e c) \<longrightarrow> (za#zsa)!i=Some c")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule_tac
      n="length wi + length v'i"
      in get_configurations_elem)
     apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
     apply(arith)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(blast)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(subgoal_tac "length (za#zsa) = Suc(length wi + length v'i)")
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(force)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "\<forall>i<length(z#zs). \<forall>c e. d i=Some (pair e c) \<longrightarrow> (z#zs)!i=Some c")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule_tac
      n="length wi"
      in get_configurations_elem)
     apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
     apply(arith)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(blast)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(subgoal_tac "length (z#zs) = Suc(length wi)")
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(force)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "w'!i=epdaS_conf_state ca")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="w'!i"
      and s="(w' @ v')!i"
      in subst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(rule_tac
      t="w'@v'"
      and s="map (case_option q epdaS_conf_state) zsa"
      in ssubst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(rule_tac
      t="map (case_option q epdaS_conf_state) zsa ! i"
      and s="(case_option q epdaS_conf_state) (zsa ! i)"
      in ssubst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(rule_tac
      t="zsa!i"
      and s="(za#zsa)!(Suc i)"
      in ssubst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(rule_tac
      t="(za#zsa)!(Suc i)"
      and s="Some ca"
      in ssubst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(erule_tac
      x="Suc i"
      and P="\<lambda>x. x < length (za # zsa) \<longrightarrow> (\<forall>c e. da x = Some (pair e c) \<longrightarrow> (za # zsa) ! x = Some c)"
      in allE)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(erule impE)
     apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
     apply(force)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(erule_tac
      x="ca"
      in allE)
    apply(erule_tac
      x="Some ec"
      in allE)
    apply(clarsimp)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(force)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(subgoal_tac "case_option q epdaS_conf_state (zs ! i) = epdaS_conf_state c")
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="zs!i"
      and s="(z#zs)!(Suc i)"
      in ssubst)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(erule_tac
      x="Suc i"
      and P="\<lambda>x. x < length (z # zs) \<longrightarrow> (\<forall>c e. d x = Some (pair e c) \<longrightarrow> (z # zs) ! x = Some c)"
      in allE)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(erule impE)
    apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
    apply(force)
   apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
   apply(erule_tac
      x="c"
      in allE)
   apply(erule_tac
      x="Some eb"
      in allE)
   apply(clarsimp)
  apply(rename_tac d da e q' ea q'a z zs za zsa i eb ec c ca)(*strict*)
  apply(force)
  done

theorem F_DFA_GOTO_SEQUENCE_in_F_EPDA_GOTO_SEQUENCE_for_complete_DFA: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w \<in> F_EPDA_GOTO_SEQUENCE M q w"
  apply(simp add: F_DFA_GOTO_SEQUENCE_def)
  apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO_SEQUENCE M q w")
   apply(rule Fun_Def.THE_defaultI')
   apply(clarsimp)
  apply(induct w arbitrary: q rule: rev_induct)
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs q)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO_SEQUENCE M q xs")
   apply(rename_tac x xs q)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs q)(*strict*)
  apply(thin_tac "\<And>q. q \<in> epda_states M \<Longrightarrow> \<exists>!x. x \<in> F_EPDA_GOTO_SEQUENCE M q xs")
  apply(erule ex1E)
  apply(rename_tac x xs q xa)(*strict*)
  apply(subgoal_tac "length xs=length xa")
   apply(rename_tac x xs q xa)(*strict*)
   prefer 2
   apply(rule_tac
      M="M"
      and q="q"
      in F_EPDA_GOTO_SEQUENCESound_main1)
       apply(rename_tac x xs q xa)(*strict*)
       apply(force)
      apply(rename_tac x xs q xa)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa)(*strict*)
     apply(force)
    apply(rename_tac x xs q xa)(*strict*)
    apply(force)
   apply(rename_tac x xs q xa)(*strict*)
   apply(force)
  apply(rename_tac x xs q xa)(*strict*)
  apply(case_tac xs)
   apply(rename_tac x xs q xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x q)(*strict*)
   apply(subgoal_tac "F_DFA_GOTO M q x \<in> F_EPDA_GOTO M q x")
    apply(rename_tac x q)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac x q)(*strict*)
        apply(force)
       apply(rename_tac x q)(*strict*)
       apply(force)
      apply(rename_tac x q)(*strict*)
      apply(force)
     apply(rename_tac x q)(*strict*)
     apply(force)
    apply(rename_tac x q)(*strict*)
    apply(force)
   apply(rename_tac x q)(*strict*)
   apply(rule_tac
      a="[F_DFA_GOTO M q x]"
      in ex1I)
    apply(rename_tac x q)(*strict*)
    apply(clarsimp)
   apply(rename_tac x q xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x q p)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
   apply(rule sym)
   apply(rule_tac
      ?e1.0="\<lparr>edge_src = q, edge_event = Some x, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = F_DFA_GOTO M q x\<rparr>"
      and ?e2.0="\<lparr>edge_src = q, edge_event = Some x, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = p\<rparr>"
      in valid_dfa_Connected_use_FEdetermR)
          apply(rename_tac x q p)(*strict*)
          apply(force)
         apply(rename_tac x q p)(*strict*)
         apply(force)
        apply(rename_tac x q p)(*strict*)
        apply(force)
       apply(rename_tac x q p)(*strict*)
       apply(force)
      apply(rename_tac x q p)(*strict*)
      apply(force)
     apply(rename_tac x q p)(*strict*)
     apply(force)
    apply(rename_tac x q p)(*strict*)
    apply(force)
   apply(rename_tac x q p)(*strict*)
   apply(force)
  apply(rename_tac x xs q xa a list)(*strict*)
  apply(subgoal_tac "\<exists>xs' xt. xs=xs'@[xt]")
   apply(rename_tac x xs q xa a list)(*strict*)
   prefer 2
   apply(rule emptyString)
   apply(force)
  apply(rename_tac x xs q xa a list)(*strict*)
  apply(erule exE)+
  apply(rename_tac x xs q xa a list xs' xt)(*strict*)
  apply(rule_tac
      a="xa@[F_DFA_GOTO M (last xa) x]"
      in ex1I)
   apply(rename_tac x xs q xa a list xs' xt)(*strict*)
   apply(subgoal_tac "F_DFA_GOTO M (last xa) x \<in> F_EPDA_GOTO M (last xa) x")
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac x xs q xa a list xs' xt)(*strict*)
        apply(force)
       apply(rename_tac x xs q xa a list xs' xt)(*strict*)
       apply(force)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(rule_tac
      A="set xa"
      in set_mp)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(rule_tac
      q="q"
      and w="xs"
      in F_EPDA_GOTO_SEQUENCESound_main3)
          apply(rename_tac x xs q xa a list xs' xt)(*strict*)
          apply(force)
         apply(rename_tac x xs q xa a list xs' xt)(*strict*)
         apply(force)
        apply(rename_tac x xs q xa a list xs' xt)(*strict*)
        apply(force)
       apply(rename_tac x xs q xa a list xs' xt)(*strict*)
       apply(force)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(rule last_in_set)
     apply(force)
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    apply(force)
   apply(rename_tac x xs q xa a list xs' xt)(*strict*)
   apply(rule_tac
      t="xs@[x]"
      and s="xs'@[xt,x]"
      in ssubst)
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    apply(rule_tac
      t="xs"
      and s="xs'@[xt]"
      in ssubst)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(force)
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac x xs q xa a list xs' xt)(*strict*)
   apply(rule F_EPDA_GOTO_SEQUENCE_add_tailStep)
        apply(rename_tac x xs q xa a list xs' xt)(*strict*)
        apply(force)
       apply(rename_tac x xs q xa a list xs' xt)(*strict*)
       apply(force)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(rule_tac
      s="xs@[x]"
      and t="xs'@[xt,x]"
      in ssubst)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(rule_tac
      t="xs"
      and s="xs'@[xt]"
      in ssubst)
       apply(rename_tac x xs q xa a list xs' xt)(*strict*)
       apply(force)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(simp (no_asm_use))
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(rule set_concat_subset)
      apply(rename_tac x xs q xa a list xs' xt)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    apply(rule_tac
      s="xs"
      and t="xs'@[xt]"
      in subst)
     apply(rename_tac x xs q xa a list xs' xt)(*strict*)
     apply(force)
    apply(rename_tac x xs q xa a list xs' xt)(*strict*)
    apply(force)
   apply(rename_tac x xs q xa a list xs' xt)(*strict*)
   apply(force)
  apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
  apply(subgoal_tac "\<exists>xb' xbt. xb=xb'@[xbt]")
   apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
   apply(erule exE)+
   apply(rename_tac x xs q xa a list xs' xt xb xb' xbt)(*strict*)
   apply(erule_tac
      x="xb'"
      in allE)
   apply(clarsimp)
   apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
   apply(rule conjI)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q a p pb)(*strict*)
    apply(rule equalsFUNF_DFA_GOTO)
         apply(rename_tac x q a p pb)(*strict*)
         apply(force)
        apply(rename_tac x q a p pb)(*strict*)
        apply(force)
       apply(rename_tac x q a p pb)(*strict*)
       apply(force)
      apply(rename_tac x q a p pb)(*strict*)
      apply(rule_tac
      a="a"
      in F_EPDA_GOTO_closed_for_states)
         apply(rename_tac x q a p pb)(*strict*)
         apply(force)
        apply(rename_tac x q a p pb)(*strict*)
        apply(force)
       apply(rename_tac x q a p pb)(*strict*)
       apply(force)
      apply(rename_tac x q a p pb)(*strict*)
      apply(force)
     apply(rename_tac x q a p pb)(*strict*)
     apply(force)
    apply(rename_tac x q a p pb)(*strict*)
    apply(rule_tac F_EPDA_GOTO_proves_existence_of_edge)
        apply(rename_tac x q a p pb)(*strict*)
        apply(force)
       apply(rename_tac x q a p pb)(*strict*)
       apply(force)
      apply(rename_tac x q a p pb)(*strict*)
      apply(force)
     apply(rename_tac x q a p pb)(*strict*)
     apply(force)
    apply(rename_tac x q a p pb)(*strict*)
    apply(force)
   apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
   apply(subgoal_tac "pa \<in> epda_states M")
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    prefer 2
    apply(rule_tac
      a="a"
      in F_EPDA_GOTO_closed_for_states)
       apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    apply(force)
   apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
   apply(subgoal_tac "p=pa")
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q a list xs' xt xb' xbt pa p_seq p_seqa)(*strict*)
    apply(subgoal_tac "p_seq@[xbt]=p_seqa")
     apply(rename_tac x q a list xs' xt xb' xbt pa p_seq p_seqa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(subgoal_tac "\<exists>pseq' pseqt. p_seq=pseq'@[pseqt]")
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      prefer 2
      apply(rule emptyString)
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(rule equalsFUNF_DFA_GOTO)
          apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
          apply(force)
         apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
         apply(force)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(rule_tac
      A="set p_seq"
      in set_mp)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(rule_tac
      q="pa"
      in F_EPDA_GOTO_SEQUENCESound_main3)
            apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
            apply(force)
           apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
           apply(force)
          apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
          apply(force)
         apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
         apply(force)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(rule_tac F_EPDA_GOTO_proves_existence_of_edge)
         apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
         apply(force)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(subgoal_tac "(\<forall>i<(length (list @ [x])). ((p_seq @ [xbt])!i) \<in> F_EPDA_GOTO M ((pa#p_seq @ [xbt])!i) ((list @ [x])!i))")
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      prefer 2
      apply(rule F_EPDA_GOTO_SEQUENCESound_main2)
          apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
          apply(force)
         apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
         apply(force)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(subgoal_tac "length (list@[x]) = length(p_seq @ [xbt])")
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(erule_tac
      x="length list"
      in allE)
      apply(erule impE)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(clarsimp)
      apply(rename_tac x q a list xs' xt xbt pa pseq' pseqt)(*strict*)
      apply(subgoal_tac "x=((list @ [x]) ! Suc (length pseq'))")
       apply(rename_tac x q a list xs' xt xbt pa pseq' pseqt)(*strict*)
       apply(clarsimp)
      apply(rename_tac x q a list xs' xt xbt pa pseq' pseqt)(*strict*)
      apply(rule_tac
      t="Suc (length pseq')"
      and s="length list"
      in ssubst)
       apply(rename_tac x q a list xs' xt xbt pa pseq' pseqt)(*strict*)
       apply(clarsimp)
      apply(rename_tac x q a list xs' xt xbt pa pseq' pseqt)(*strict*)
      apply(thin_tac "length list = Suc (length pseq')")
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(rule_tac
      q="pa"
      in F_EPDA_GOTO_SEQUENCESound_main1)
         apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
         apply(force)
        apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
       apply(force)
      apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xbt pa p_seq)(*strict*)
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt pa p_seq p_seqa)(*strict*)
    apply(subgoal_tac "\<exists>pseq' pseqt. p_seq=pseq'@[pseqt]")
     apply(rename_tac x q a list xs' xt xb' xbt pa p_seq p_seqa)(*strict*)
     prefer 2
     apply(rule emptyString)
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt pa p_seq p_seqa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q a list xs' xt xb' xbt pa p_seqa pseq' pseqt)(*strict*)
    apply(subgoal_tac "\<exists>list' listt. list=list'@[listt]")
     apply(rename_tac x q a list xs' xt xb' xbt pa p_seqa pseq' pseqt)(*strict*)
     prefer 2
     apply(rule emptyString)
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt pa p_seqa pseq' pseqt)(*strict*)
    apply(clarsimp)
    apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
    apply(subgoal_tac "length p_seqa = length (list' @ [listt, x])")
     apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>pseq' pseqt. p_seqa=pseq'@[pseqt]")
      apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
     apply(clarsimp)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseq'a pseqta)(*strict*)
     apply(subgoal_tac "\<exists>w a. pseq'a=w@[a]")
      apply(rename_tac x q a pa pseq' pseqt list' listt pseq'a pseqta)(*strict*)
      prefer 2
      apply(rule emptyString)
      apply(force)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseq'a pseqta)(*strict*)
     apply(clarsimp)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
     apply(case_tac "pseq' = w \<and> pseqt = aa")
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(force)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
     apply(clarsimp)
     apply(case_tac "pseq' = w")
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(erule impE)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(clarify)
      apply(subgoal_tac "set (w@[aa,pseqta])\<subseteq> epda_states M")
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       prefer 2
       apply(rule_tac
      w="list'@[listt,x]"
      and q="pa"
      in F_EPDA_GOTO_SEQUENCESound_main3)
           apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
           apply(force)
          apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
          apply(force)
         apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
         apply(force)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(subgoal_tac "pseqt \<in> F_EPDA_GOTO M (last (pa#w)) listt")
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       prefer 2
       apply(rule_tac
      iv="[]"
      and v="[]"
      in F_EPDA_GOTO_SEQUENCESound_main2b)
            apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
            apply(force)
           apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
           apply(force)
          apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
          apply(force)
         apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
         apply(force)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(subgoal_tac "aa \<in> F_EPDA_GOTO M (last (pa#w)) listt")
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       prefer 2
       apply(rule_tac
      iv="[x]"
      and v="[pseqta]"
      in F_EPDA_GOTO_SEQUENCESound_main2b)
            apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
            apply(force)
           apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
           apply(force)
          apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
          apply(force)
         apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
         apply(force)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO M (last (pa#w)) listt")
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       prefer 2
       apply(simp only: some_step_from_every_configuration_def)
       apply(erule_tac
      x="last (pa # w)"
      in ballE)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(erule_tac
      x="listt"
      in ballE)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(erule bexE)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
       apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
           apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
           apply(force)
          apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
          apply(force)
         apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
         apply(force)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa e)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(force)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
     apply(subgoal_tac "pseq'=w")
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      prefer 2
      apply(subgoal_tac "w@[aa]=pseq' @ [pseqt]")
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       prefer 2
       apply(rule F_EPDA_GOTO_SEQUENCE_simulate_each_on_prefix)
               apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
               apply(force)
              apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
              apply(force)
             apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
             prefer 3
             apply(force)
            apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
            prefer 3
            apply(force)
           apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
           apply(force)
          apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
          apply(force)
         apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
         apply(force)
        apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
        apply(force)
       apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
       apply(force)
      apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
      apply(force)
     apply(rename_tac x q a pa pseq' pseqt list' listt pseqta w aa)(*strict*)
     apply(force)
    apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
    apply(rule sym)
    apply(rule_tac
      q="pa"
      in F_EPDA_GOTO_SEQUENCESound_main1)
        apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
        apply(force)
       apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
       apply(force)
      apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
      apply(force)
     apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
     apply(force)
    apply(rename_tac x q a xb' xbt pa p_seqa pseq' pseqt list' listt)(*strict*)
    apply(force)
   apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
   apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO M q a")
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    prefer 2
    apply(simp only: some_step_from_every_configuration_def)
    apply(erule_tac
      x="q"
      in ballE)
     apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    apply(erule_tac
      x="a"
      in ballE)
     apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
    apply(erule bexE)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
    apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
        apply(force)
       apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
       apply(simp add: some_step_from_every_configuration_def)
      apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
      apply(force)
     apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
     apply(force)
    apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa e)(*strict*)
    apply(force)
   apply(rename_tac x q a list xs' xt xb' xbt p pa p_seq p_seqa)(*strict*)
   apply(force)
  apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
  apply(subgoal_tac "length (xs@[x]) = length xb")
   apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
   apply(rule_tac
      n="length xs"
      in NonEmptyListHasTailElem)
   apply(thin_tac "xs = a # list")
   apply(thin_tac "xs = xs' @ [xt]")
   apply(thin_tac "length xs = length xa")
   apply(force)
  apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
  apply(rule_tac
      M="M"
      and q="q"
      in F_EPDA_GOTO_SEQUENCESound_main1)
      apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
      apply(force)
     apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
     apply(force)
    apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
    apply(force)
   apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
    apply(force)
   apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
   apply(rule set_subset_in2)
   apply(force)
  apply(rename_tac x xs q xa a list xs' xt xb)(*strict*)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCESound_main: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = qseq
  \<Longrightarrow> length w = length qseq \<and> (\<forall>i < length w. F_DFA_GOTO M ((q # qseq) ! i) (w ! i) = qseq ! i) \<and> set qseq \<subseteq> epda_states M"
  apply(subgoal_tac "qseq \<in> F_EPDA_GOTO_SEQUENCE M q w")
   prefer 2
   apply(rule_tac
      t="qseq"
      and s="F_DFA_GOTO_SEQUENCE M q w"
      in ssubst)
    apply(force)
   apply(rule F_DFA_GOTO_SEQUENCE_in_F_EPDA_GOTO_SEQUENCE_for_complete_DFA)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_EPDA_GOTO_SEQUENCESound_main1)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rule F_EPDA_GOTO_SEQUENCESound_main3)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "(q # F_DFA_GOTO_SEQUENCE M q w) ! i \<in> epda_states M")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(rule_tac
      t="(q # F_DFA_GOTO_SEQUENCE M q w) ! i"
      and s="(F_DFA_GOTO_SEQUENCE M q w)!nat"
      in ssubst)
    apply(rename_tac i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(rule_tac
      A="set(F_DFA_GOTO_SEQUENCE M q w)"
      in set_mp)
    apply(rename_tac i nat)(*strict*)
    apply(force)
   apply(rename_tac i nat)(*strict*)
   apply(rule nth_mem)
   apply(arith)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "(\<forall>i < length w. ((F_DFA_GOTO_SEQUENCE M q w)!i) \<in> F_EPDA_GOTO M ((q#(F_DFA_GOTO_SEQUENCE M q w))!i) (w!i))")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule F_EPDA_GOTO_SEQUENCESound_main2)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO M ((q # F_DFA_GOTO_SEQUENCE M q w) ! i) (w ! i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(simp add: some_step_from_every_configuration_def)
   apply(erule_tac
      x="((q # F_DFA_GOTO_SEQUENCE M q w) ! i)"
      in ballE)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="w!i"
      in ballE)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e)(*strict*)
   apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
       apply(rename_tac i e)(*strict*)
       apply(force)
      apply(rename_tac i e)(*strict*)
      apply(force)
     apply(rename_tac i e)(*strict*)
     apply(force)
    apply(rename_tac i e)(*strict*)
    apply(force)
   apply(rename_tac i e)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO M ((q # F_DFA_GOTO_SEQUENCE M q w) ! i) (w ! i) \<in> F_EPDA_GOTO M ((q # F_DFA_GOTO_SEQUENCE M q w) ! i) (w ! i)")
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(q # F_DFA_GOTO_SEQUENCE M q w) ! i"
      and s="(q # F_DFA_GOTO_SEQUENCE M q w) ! i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCESound_main1: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = qseq
  \<Longrightarrow> length w = length qseq"
  apply(simp add: F_DFA_GOTO_SEQUENCESound_main)
  done

lemma F_DFA_GOTO_SEQUENCESound_main2: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = qseq
  \<Longrightarrow> \<forall>i < length w. F_DFA_GOTO M ((q # qseq) ! i) (w ! i) = qseq ! i"
  apply(simp add: F_DFA_GOTO_SEQUENCESound_main)
  done

lemma F_DFA_GOTO_SEQUENCESound_main3: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = qseq
  \<Longrightarrow> set qseq \<subseteq> epda_states M"
  apply(simp add: F_DFA_GOTO_SEQUENCESound_main)
  done

theorem F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> {F_DFA_GOTO_SEQUENCE M q w} = F_EPDA_GOTO_SEQUENCE M q w"
  apply(rule sym)
  apply(rule ex1_set)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_in_F_EPDA_GOTO_SEQUENCE_for_complete_DFA)
       apply(blast)+
  apply(case_tac "F_DFA_GOTO_SEQUENCE M q w")
   apply(subgoal_tac "(length w = length [])")
    apply(clarsimp)
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(rename_tac a list)(*strict*)
  apply(simp add: F_DFA_GOTO_SEQUENCE_def)
  apply(rule_tac
      a="[]"
      in THE_default_ex1I)
   apply(rename_tac a list)(*strict*)
   apply(blast)
  apply(rename_tac a list)(*strict*)
  apply(blast)
  done

lemma F_DFA_GOTO_SEQUENCE_F_EPDA_GOTO_SEQUENCE_elem: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> x \<in> F_EPDA_GOTO_SEQUENCE M q w
  \<Longrightarrow> x = F_DFA_GOTO_SEQUENCE M q w"
  apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q w} = F_EPDA_GOTO_SEQUENCE M q w")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
       apply(auto)
  done

corollary determinism_implies_extension_to_goto: "
  epdaS.is_forward_edge_deterministic M
  \<Longrightarrow> x \<in> F_EPDA_GOTO M q X
  \<Longrightarrow> y \<in> F_EPDA_GOTO M q X
  \<Longrightarrow> x = y"
  apply(simp add: F_EPDA_GOTO_def)
  apply(simp add: epdaS.is_forward_edge_deterministic_def)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=[X],epdaS_conf_stack=[epda_box M]\<rparr> "
      in allE)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state=x,epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>epdaS_conf_state=y,epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>edge_src = q, edge_event = Some X, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = x\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>edge_src = q, edge_event = Some X, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = y\<rparr>"
      in allE)
  apply(erule impE)
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: option_to_list_def)
  apply(force)
  done

lemma DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> A \<in> (epda_events M)
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q [A] = [F_DFA_GOTO M q A]"
  apply(simp add: some_step_from_every_configuration_def)
  apply(erule_tac
      x="q"
      in ballE)
   apply(erule_tac
      x="A"
      in ballE)
    apply(subgoal_tac "\<exists>!x. x \<in> (F_EPDA_GOTO_SEQUENCE M q [A])")
     apply(subgoal_tac "\<exists>!x. x \<in> (F_EPDA_GOTO M q A)")
      apply(subgoal_tac "\<exists>x. x \<in> (F_EPDA_GOTO_SEQUENCE M q [A])")
       apply(subgoal_tac "\<exists>x. x \<in> (F_EPDA_GOTO M q A)")
        apply(erule exE)+
        apply(rename_tac x xa)(*strict*)
        apply(unfold F_DFA_GOTO_SEQUENCE_def)
        apply(rule_tac
      t="THE_default [] (\<lambda>x. x \<in> F_EPDA_GOTO_SEQUENCE M q [A])"
      and s="x"
      in ssubst)
         apply(rename_tac x xa)(*strict*)
         apply(rule Fun_Def.THE_default1_equality)
          apply(rename_tac x xa)(*strict*)
          apply(blast)
         apply(rename_tac x xa)(*strict*)
         apply(blast)
        apply(rename_tac x xa)(*strict*)
        apply(unfold F_DFA_GOTO_def)
        apply(rule_tac
      t="THE_default q (\<lambda>x. x \<in> F_EPDA_GOTO M q A)"
      and s="xa"
      in ssubst)
         apply(rename_tac x xa)(*strict*)
         apply(rule Fun_Def.THE_default1_equality)
          apply(rename_tac x xa)(*strict*)
          apply(blast)
         apply(rename_tac x xa)(*strict*)
         apply(blast)
        apply(rename_tac x xa)(*strict*)
        apply(clarsimp)
       apply(rule HOL.ex1_implies_ex)
       apply(blast)
      apply(rule HOL.ex1_implies_ex)
      apply(blast)
     apply(clarsimp)
     apply(rename_tac e p)(*strict*)
     apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
         apply(rename_tac e p)(*strict*)
         apply(blast,blast)
       apply(rename_tac e p)(*strict*)
       apply(force)
      apply(rename_tac e p)(*strict*)
      apply(force)
     apply(rename_tac e p)(*strict*)
     apply(force)
    apply(simp add: F_EPDA_GOTO_SEQUENCE_def)
    apply(subgoal_tac "\<exists>!x. x \<in> F_EPDA_GOTO M q A")
     prefer 2
     apply(clarsimp)
     apply(rename_tac e)(*strict*)
     apply(rule EX1_F_EPDA_GOTO_for_complete_DFA)
         apply(rename_tac e)(*strict*)
         apply(blast,blast)
       apply(rename_tac e)(*strict*)
       apply(force)
      apply(rename_tac e)(*strict*)
      apply(force)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_to_derivation: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> \<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>) \<and> q # (F_DFA_GOTO_SEQUENCE M q w) = map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)"
  apply(rule_tac
      A="F_EPDA_GOTO_SEQUENCE M q w"
      and a="F_DFA_GOTO_SEQUENCE M q w"
      in propForElem)
   apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
       apply(blast)+
  apply(rule F_EPDA_GOTO_SEQUENCE_to_derivation)
    apply(force)+
  done

lemma F_DFA_GOTO_SEQUENCE_injective: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set v \<subseteq> (epda_events M)
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = r
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q v = r
  \<Longrightarrow> \<forall>e1 e2. e1 \<in> (epda_delta M) \<and> e2 \<in> (epda_delta M) \<and> edge_trg e2 = edge_trg e1 \<longrightarrow> edge_event e1 = edge_event e2
  \<Longrightarrow> w = v"
  apply(subgoal_tac "length w=length r")
   prefer 2
   apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(subgoal_tac "length v=length r")
   prefer 2
   apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "F_DFA_GOTO M ((q#r)!i) (w!i) = (r!i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>i < length w. F_DFA_GOTO M ((q#r)!i) (w!i) = (r!i))")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac i)(*strict*)
         apply(blast)+
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO M ((q#r)!i) (v!i) = (r!i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>i<(length v). F_DFA_GOTO M ((q#r)!i) (v!i) = (r!i))")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac i)(*strict*)
         apply(blast)+
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src=(q#r)!i,edge_event=Some (w!i),edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=r!i\<rparr> \<in> epda_delta M")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "F_DFA_GOTO M ((q # r) ! i) (w ! i) \<in> F_EPDA_GOTO M ((q # r) ! i) (w ! i)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(case_tac i)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      A="set r"
      in set_mp)
      apply(rename_tac i nat)(*strict*)
      apply(rule F_DFA_GOTO_SEQUENCESound_main3)
           apply(rename_tac i nat)(*strict*)
           apply(force)
          apply(rename_tac i nat)(*strict*)
          apply(force)
         apply(rename_tac i nat)(*strict*)
         apply(force)
        apply(rename_tac i nat)(*strict*)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      n="nat"
      in nth_set)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      A="set w"
      in set_mp)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src=(q#r)!i,edge_event=Some (v!i),edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=r!i\<rparr> \<in> epda_delta M")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "F_DFA_GOTO M ((q # r) ! i) (v ! i) \<in> F_EPDA_GOTO M ((q # r) ! i) (v ! i)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(case_tac i)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      A="set r"
      in set_mp)
      apply(rename_tac i nat)(*strict*)
      apply(rule F_DFA_GOTO_SEQUENCESound_main3)
           apply(rename_tac i nat)(*strict*)
           apply(force)
          apply(rename_tac i nat)(*strict*)
          apply(force)
         apply(rename_tac i nat)(*strict*)
         apply(force)
        apply(rename_tac i nat)(*strict*)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      n="nat"
      in nth_set)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      A="set v"
      in set_mp)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_injective_prime: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set v \<subseteq> (epda_events M)
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w = r
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q v = r
  \<Longrightarrow> \<forall>i < length r. P (r ! i)
  \<Longrightarrow> \<forall>e1 e2. e1 \<in> (epda_delta M) \<and> e2 \<in> (epda_delta M) \<and> edge_trg e2 = edge_trg e1 \<and> P (edge_trg e1) \<longrightarrow> edge_event e1 = edge_event e2
  \<Longrightarrow> w = v"
  apply(subgoal_tac "length w=length r")
   prefer 2
   apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(subgoal_tac "length v=length r")
   prefer 2
   apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "F_DFA_GOTO M ((q#r)!i) (w!i) = (r!i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>i < length w. F_DFA_GOTO M ((q#r)!i) (w!i) = (r!i))")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac i)(*strict*)
         apply(blast)+
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO M ((q#r)!i) (v!i) = (r!i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "(\<forall>i<(length v). F_DFA_GOTO M ((q#r)!i) (v!i) = (r!i))")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac i)(*strict*)
         apply(blast)+
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length r \<longrightarrow> P (r ! i)"
      in allE)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src=(q#r)!i,edge_event=Some (w!i),edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=r!i\<rparr> \<in> epda_delta M")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "F_DFA_GOTO M ((q # r) ! i) (w ! i) \<in> F_EPDA_GOTO M ((q # r) ! i) (w ! i)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(case_tac i)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      A="set r"
      in set_mp)
      apply(rename_tac i nat)(*strict*)
      apply(rule F_DFA_GOTO_SEQUENCESound_main3)
           apply(rename_tac i nat)(*strict*)
           apply(force)
          apply(rename_tac i nat)(*strict*)
          apply(force)
         apply(rename_tac i nat)(*strict*)
         apply(force)
        apply(rename_tac i nat)(*strict*)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      n="nat"
      in nth_set)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      A="set w"
      in set_mp)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src=(q#r)!i,edge_event=Some (v!i),edge_pop=[epda_box M],edge_push=[epda_box M],edge_trg=r!i\<rparr> \<in> epda_delta M")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(subgoal_tac "F_DFA_GOTO M ((q # r) ! i) (v ! i) \<in> F_EPDA_GOTO M ((q # r) ! i) (v ! i)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(case_tac i)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      A="set r"
      in set_mp)
      apply(rename_tac i nat)(*strict*)
      apply(rule F_DFA_GOTO_SEQUENCESound_main3)
           apply(rename_tac i nat)(*strict*)
           apply(force)
          apply(rename_tac i nat)(*strict*)
          apply(force)
         apply(rename_tac i nat)(*strict*)
         apply(force)
        apply(rename_tac i nat)(*strict*)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(rule_tac
      n="nat"
      in nth_set)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      A="set v"
      in set_mp)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_EPDA_GOTO_def)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = (q # r) ! i, edge_event = Some (v ! i), edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = r ! i\<rparr>"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = (q # r) ! i, edge_event = Some (w ! i), edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = r ! i\<rparr>"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(erule impE)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

corollary F_DFA_GOTO_SEQUENCE_injective2_1: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set v \<subseteq> (epda_events M)
  \<Longrightarrow> last (q # (F_DFA_GOTO_SEQUENCE M q w)) = r
  \<Longrightarrow> last (q # (F_DFA_GOTO_SEQUENCE M q v)) = r
  \<Longrightarrow> \<forall>e1 e2. e1 \<in> (epda_delta M) \<and> e2 \<in> (epda_delta M) \<and> edge_trg e2 = edge_trg e1 \<longrightarrow> e1 = e2
  \<Longrightarrow> \<forall>e. e \<in> (epda_delta M) \<longrightarrow> edge_trg e \<noteq> q
  \<Longrightarrow> w = []
  \<Longrightarrow> v = a # list
  \<Longrightarrow> Q"
  apply(subgoal_tac "length v= length (F_DFA_GOTO_SEQUENCE M q v)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(subgoal_tac "length w= length (F_DFA_GOTO_SEQUENCE M q w)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(blast)+
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M q v) = q")
   prefer 2
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M q v)"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q v)"
      in ssubst)
    apply(rule sym)
    apply(rule lengthGT)
    apply(force)
   apply(rule_tac
      P="\<lambda>x. last (q # F_DFA_GOTO_SEQUENCE M q v) = x"
      and s="r"
      in ssubst)
    apply(rule_tac
      t="r"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q w)"
      in ssubst)
     apply(blast)
    apply(rule sym)
    apply(rule length0)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=v,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length v) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q v)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length v)) \<and> maximum_of_domain d (length v)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac d e q')(*strict*)
  apply(erule conjE)+
  apply(case_tac "length v")
   apply(rename_tac d e q')(*strict*)
   apply(force)
  apply(rename_tac d e q' nat)(*strict*)
  apply(case_tac e)
   apply(rename_tac d e q' nat)(*strict*)
   apply(rule epdaS.derivation_Always_PreEdge_prime)
    apply(rename_tac d e q' nat)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat)(*strict*)
   apply(force)
  apply(rename_tac d e q' nat aa)(*strict*)
  apply(subgoal_tac "edge_trg aa=q' \<and> aa \<in> epda_delta M")
   apply(rename_tac d e q' nat aa)(*strict*)
   prefer 2
   apply(case_tac "d nat")
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(rule_tac
      i="nat"
      and n="Suc nat"
      in epdaS.derivationNoFromNone2)
       apply(rename_tac d e q' nat aa)(*strict*)
       apply(force)
      apply(rename_tac d e q' nat aa)(*strict*)
      apply(force)
     apply(rename_tac d e q' nat aa)(*strict*)
     apply(force)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa aaa)(*strict*)
   apply(case_tac aaa)
   apply(rename_tac d e q' nat aa aaa option b)(*strict*)
   apply(subgoal_tac "epdaS_step_relation M b aa \<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>")
    apply(rename_tac d e q' nat aa aaa option b)(*strict*)
    prefer 2
    apply(rule epdaS.position_change_due_to_step_relation)
      apply(rename_tac d e q' nat aa aaa option b)(*strict*)
      apply(force)
     apply(rename_tac d e q' nat aa aaa option b)(*strict*)
     apply(force)
    apply(rename_tac d e q' nat aa aaa option b)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa aaa option b)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac d e q' nat aa)(*strict*)
  apply(subgoal_tac "length (get_configurations d (length v)) = Suc (length v)")
   apply(rename_tac d e q' nat aa)(*strict*)
   prefer 2
   apply(rule get_configurations_length)
  apply(rename_tac d e q' nat aa)(*strict*)
  apply(subgoal_tac "q=q'")
   apply(rename_tac d e q' nat aa)(*strict*)
   prefer 2
   apply(rule_tac
      t="q"
      and s="last (F_DFA_GOTO_SEQUENCE M q v)"
      in ssubst)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M q v)"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q v)"
      in ssubst)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(rule_tac
      t="q # F_DFA_GOTO_SEQUENCE M q v"
      and s="map (case_option q epdaS_conf_state) (get_configurations d (length v))"
      in ssubst)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(rule_tac
      t="last (map (case_option q epdaS_conf_state) (get_configurations d (length v)))"
      and s="(case_option q epdaS_conf_state) (last (get_configurations d (length v)))"
      in ssubst)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(rule last_map)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(rule_tac
      t="(last (get_configurations d (length v)))"
      and s="(get_configurations d (length v))!(length (get_configurations d (length v)) - 1)"
      in ssubst)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(rule last_conv_nth)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(subgoal_tac "\<forall>i<length(get_configurations d (length v)). \<forall>c e. d i=Some (pair e c) \<longrightarrow> (get_configurations d (length v))!i=Some c")
    apply(rename_tac d e q' nat aa)(*strict*)
    prefer 2
    apply(rule_tac
      zs="v"
      and n="length v"
      in get_configurations_elem2)
      apply(rename_tac d e q' nat aa)(*strict*)
      apply(force)
     apply(rename_tac d e q' nat aa)(*strict*)
     apply(force)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(erule_tac
      x="(length (get_configurations d (length v)) - 1)"
      in allE)
   apply(erule impE)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(erule_tac
      x="\<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule impE)
    apply(rename_tac d e q' nat aa)(*strict*)
    apply(force)
   apply(rename_tac d e q' nat aa)(*strict*)
   apply(force)
  apply(rename_tac d e q' nat aa)(*strict*)
  apply(force)
  done

theorem F_DFA_GOTO_SEQUENCE_concat: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p = epda_initial M
  \<Longrightarrow> set w1 \<subseteq> epda_events M
  \<Longrightarrow> set w2 \<subseteq> epda_events M
  \<Longrightarrow> w1 \<noteq> []
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M p w1)) w2) = last (F_DFA_GOTO_SEQUENCE M p (w1 @ w2))"
  apply(subgoal_tac "\<forall>w q. q=p \<and> w=w1@w2 \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)+
    apply(rename_tac w q)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w q)(*strict*)
   apply(force)
  apply(subgoal_tac "\<forall>w q. q=p \<and> w=w1 \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)
      apply(rename_tac w q)(*strict*)
      apply(blast)
     apply(rename_tac w q)(*strict*)
     apply(blast)
    apply(rename_tac w q)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w q)(*strict*)
   apply(blast)
  apply(subgoal_tac "\<forall>w q. q=(last (F_DFA_GOTO_SEQUENCE M p w1)) \<and> w=w2 \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)
      apply(rename_tac w q)(*strict*)
      apply(blast)
     apply(rename_tac w q)(*strict*)
     apply(force)
    apply(rename_tac w q)(*strict*)
    apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M p w1)"
      in set_mp)
     apply(rename_tac w q)(*strict*)
     apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main3)
          apply(rename_tac w q)(*strict*)
          apply(blast)
         apply(rename_tac w q)(*strict*)
         apply(force)
        apply(rename_tac w q)(*strict*)
        apply(blast)
       apply(rename_tac w q)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac w q)(*strict*)
      apply(blast)
     apply(rename_tac w q)(*strict*)
     apply(blast)
    apply(rename_tac w q)(*strict*)
    apply(rule_tac
      t="q"
      and s="last (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
     apply(rename_tac w q)(*strict*)
     apply(blast)
    apply(rename_tac w q)(*strict*)
    apply(rule List.last_in_set)
    apply(subgoal_tac "length w1=length (F_DFA_GOTO_SEQUENCE M p w1)")
     apply(rename_tac w q)(*strict*)
     apply(force)
    apply(rename_tac w q)(*strict*)
    apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac w q)(*strict*)
         apply(blast)
        apply(rename_tac w q)(*strict*)
        apply(blast)
       apply(rename_tac w q)(*strict*)
       apply(blast)
      apply(rename_tac w q)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac w q)(*strict*)
     apply(blast)
    apply(rename_tac w q)(*strict*)
    apply(blast)
   apply(rename_tac w q)(*strict*)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
  apply(case_tac w1)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb a list)(*strict*)
  apply(case_tac w2)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb a list aa lista)(*strict*)
  apply(rename_tac w1a w1' w2a w2')
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (z#zs)=Suc(Suc(Suc(length (w1'@w2'))))")
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(subgoal_tac "length (za#zsa)=Suc(Suc(length w1'))")
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(subgoal_tac "length (zb#zsb)=Suc(Suc(length w2'))")
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(subgoal_tac "d=derivation_append (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler:=(epdaS_conf_scheduler v)@(w2a#w2')\<rparr>)) db (Suc (length w1'))")
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(rule_tac
      t="last (map (case_option (epda_initial M) epdaS_conf_state) zs)"
      and s="q'"
      in ssubst)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule_tac
      t="last (map (case_option (epda_initial M) epdaS_conf_state) zs)"
      and s="(case_option (epda_initial M) epdaS_conf_state) (last zs)"
      in ssubst)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(rule last_map)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(subgoal_tac "\<forall>i<length(z#zs). \<forall>c e. d i=Some (pair e c) \<longrightarrow> (z#zs)!i=Some c")
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        prefer 2
        apply(rule_tac
      n="Suc(Suc(length(w1'@w2')))"
      in get_configurations_elem)
          apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
          apply(force)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
         apply(force)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(erule_tac
      x="length zs"
      in allE)
       apply(erule impE)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(erule_tac
      x="\<lparr>epdaS_conf_state = q', epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
       apply(erule_tac
      x="e"
      in allE)
       apply(erule impE)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule_tac
      t="last zs"
      and s="(z#zs)!(length zs)"
      in ssubst)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(rule_tac
      t="last zs"
      and s="last (z#zs)"
      in ssubst)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
         apply(force)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(rule last_nth3)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(rule_tac
      t="last (map (case_option (case zb of None \<Rightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w1a # w1')) | Some a \<Rightarrow> epdaS_conf_state a) epdaS_conf_state) zsb)"
      and s="((case_option (case zb of None \<Rightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w1a # w1')) | Some a \<Rightarrow> epdaS_conf_state a) epdaS_conf_state)) (last zsb)"
      in ssubst)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule last_map)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(subgoal_tac "\<forall>i<length(zb#zsb). \<forall>c e. db i=Some (pair e c) \<longrightarrow> (zb#zsb)!i=Some c")
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       prefer 2
       apply(rule_tac
      n="Suc(length w2')"
      in get_configurations_elem)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
         apply(force)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(erule_tac
      x="length zsb"
      in allE)
      apply(erule impE)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(erule_tac
      x="\<lparr>epdaS_conf_state = q'b, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
      apply(erule_tac
      x="eb"
      in allE)
      apply(erule impE)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(rule_tac
      t="last zsb"
      and s="(zb#zsb)!(length zsb)"
      in ssubst)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule_tac
      t="last zsb"
      and s="last (zb#zsb)"
      in ssubst)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule last_nth3)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(rule_tac
      t="(zb # zsb) ! length zsb"
      and s="Some \<lparr>epdaS_conf_state = q'b, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in ssubst)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(simp (no_asm))
      apply(rule sym)
      apply(rule_tac
      ?d1.0="d"
      and f="\<lambda>d. case (d (Suc (Suc (length w1' + length w2')))) of Some (pair e c) \<Rightarrow> (epdaS_conf_state c)"
      in applyFunctionBack)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(blast)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(clarsimp)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(simp add: derivation_append_def derivation_map_def)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     defer
     apply(rule_tac
      t="zb#zsb"
      and s="get_configurations db (Suc (length w2'))"
      in ssubst)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(rule get_configurations_length)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(rule_tac
      t="za#zsa"
      and s="get_configurations da (Suc (length w1'))"
      in ssubst)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(force)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(rule get_configurations_length)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(rule_tac
      t="z#zs"
      and s="get_configurations d (Suc (Suc(length (w1'@w2'))))"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(rule get_configurations_length)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(rule_tac
      M="M"
      in epdaS.derivationsCoincideR)
          apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
          defer
          apply(blast)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
         apply(blast)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
        apply(blast)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(blast)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      defer
      apply(rule_tac
      t="Suc (Suc (length w1' + length w2'))"
      and s="Suc(length w1')+Suc(length w2')"
      in ssubst)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(rule_tac concat_has_max_dom)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
       apply(rule derivation_map_preserves_maximum_of_domain)
       apply(blast)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(blast)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(simp add: derivation_append_def derivation_map_def)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(simp add: derivation_append_def derivation_map_def)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(simp (no_asm) only: epdaS.is_forward_deterministic_accessible_def)
   apply(rule conjI)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rule epda_is_is_forward_target_deterministic_accessible)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(simp add: valid_dfa_def valid_dpda_def)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(subgoal_tac "epdaS.derivation M (derivation_map da (\<lambda>v. v\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler v @ w2a # w2'\<rparr>))")
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   prefer 2
   apply(rule epdaS.derivation_map_preserves_derivation2)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(clarsimp)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2' a ec b)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(rule epdaS.derivation_append_preserves_derivation_initial)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   prefer 2
   apply(rule epdaS.derivation_concat2)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(rule_tac
      t="case_option (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w1a # w1'))) epdaS_conf_state zb"
      and s="last (map (case_option (epda_initial M) epdaS_conf_state) zsa)"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(rule_tac
      t="last (map (case_option (epda_initial M) epdaS_conf_state) zsa)"
      and s="(case_option (epda_initial M) epdaS_conf_state) (last zsa)"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(rule last_map)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(subgoal_tac "\<forall>i<length(za#zsa). \<forall>c e. da i=Some (pair e c) \<longrightarrow> (za#zsa)!i=Some c")
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    prefer 2
    apply(rule get_configurations_elem)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(blast)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(blast)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(erule_tac
      x="length zsa"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      t="(last zsa)"
      and s="zsa ! length w1'"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(rule last_nth3)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   apply(force)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(rule epdaS.derivation_map_preserves_derivation_initial)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
     apply(simp add: epdaS.derivation_initial_def)
     prefer 2
     apply(force)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
   prefer 2
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2' c)(*strict*)
   apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
   apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb w1a w1' w2a w2')(*strict*)
  apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  done

theorem F_DFA_GOTO_SEQUENCE_take_head: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> X \<in> (epda_events M)
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (X # w)) = last (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (epda_initial M) X) w)"
  apply(rule_tac
      t="(F_DFA_GOTO M (epda_initial M) X)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [X])"
      in ssubst)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [X]"
      and s="[F_DFA_GOTO M (epda_initial M) X]"
      in ssubst)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(blast)+
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(blast)+
   apply(force)
  apply(rule sym)
  apply(rule_tac
      t="X#w"
      and s="[X]@w"
      in ssubst)
   apply(force)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
         apply(force)+
  done

lemma DFA_F_DFA_GOTO_in_states: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q0 \<in> epda_states M
  \<Longrightarrow> X \<in> epda_events M
  \<Longrightarrow> q = F_DFA_GOTO M q0 X
  \<Longrightarrow> q \<in> epda_states M"
  apply(subgoal_tac "[q]=F_DFA_GOTO_SEQUENCE M q0 [X]")
   apply(subgoal_tac "set ([q]) \<subseteq> epda_states M")
    apply(rule set_subset_in)
    apply(force)
   apply(rule_tac
      w="[X]"
      in F_DFA_GOTO_SEQUENCESound_main3)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="q"
      and s="F_DFA_GOTO M q0 X"
      in ssubst)
   apply(force)
  apply(rule sym)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma DFA_F_DFA_GOTO_SEQUENCE_last_in_states: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q0 \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> length w > 0
  \<Longrightarrow> qs = F_DFA_GOTO_SEQUENCE M q0 w
  \<Longrightarrow> last qs \<in> epda_states M"
  apply(subgoal_tac "length qs > 0")
   prefer 2
   apply(subgoal_tac "length w = length qs")
    prefer 2
    apply(rule_tac
      w="w"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "set qs \<subseteq> epda_states M")
   apply(rule_tac
      A="set qs"
      in set_mp)
    apply(force)
   apply(force)
  apply(rule_tac
      w="w"
      in F_DFA_GOTO_SEQUENCESound_main3)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem nth_last_commutes_over_F_DFA_GOTO_SEQUENCE: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> i < length w
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w ! i = last (F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))"
  apply(subgoal_tac "\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=take (Suc i) w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length (take (Suc i) w)) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length (take (Suc i) w))) \<and> maximum_of_domain d (length (take (Suc i) w))")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule_tac
      B="set w"
      in subset_trans)
    apply(rule List.set_take_subset)
   apply(force)
  apply(erule exE)+
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q w ! i"
      and s="(map (case_option q epdaS_conf_state) (get_configurations d (length w)))!(Suc i)"
      in ssubst)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(rule_tac
      t="map (case_option q epdaS_conf_state) (get_configurations d (length w)) ! Suc i"
      and s="(case_option q epdaS_conf_state) ((get_configurations d (length w)) ! Suc i)"
      in ssubst)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(rule nth_map)
   apply(rule_tac
      t="length (get_configurations d (length w))"
      and s="Suc (length w)"
      in ssubst)
    apply(rename_tac d da e ea q' q'a)(*strict*)
    apply(rule get_configurations_length)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(subgoal_tac "\<forall>i<length(get_configurations d (length w)). \<forall>c e. d i=Some (pair e c) \<longrightarrow> ((get_configurations d (length w))!i=Some c)")
   apply(rename_tac d da e ea q' q'a)(*strict*)
   prefer 2
   apply(rule_tac
      n="length w"
      in get_configurations_elem2)
     apply(rename_tac d da e ea q' q'a)(*strict*)
     apply(arith)
    apply(rename_tac d da e ea q' q'a)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(erule impE)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(rule_tac
      t="length (get_configurations d (length w))"
      and s="Suc (length w)"
      in ssubst)
    apply(rename_tac d da e ea q' q'a)(*strict*)
    apply(rule get_configurations_length)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair e c)")
   apply(rename_tac d da e ea q' q'a)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac d da e ea q' q'a)(*strict*)
     apply(blast)
    apply(rename_tac d da e ea q' q'a)(*strict*)
    apply(blast)
   apply(rename_tac d da e ea q' q'a)(*strict*)
   apply(arith)
  apply(rename_tac d da e ea q' q'a)(*strict*)
  apply(erule exE)+
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="eb"
      in allE)
  apply(erule impE)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(rule_tac
      t="case_option q epdaS_conf_state (get_configurations d (length w) ! Suc i)"
      and s="epdaS_conf_state c"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))"
      and s="last (q#F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(rule sym)
   apply(rule lengthGT)
   apply(rule_tac
      t="length (F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))"
      and s="length (take (Suc i) w)"
      in subst)
    apply(rename_tac d da e ea q' q'a eb c)(*strict*)
    apply(rule_tac
      w="(take (Suc i) w)"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac d da e ea q' q'a eb c)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q' q'a eb c)(*strict*)
        apply(force)
       apply(rename_tac d da e ea q' q'a eb c)(*strict*)
       apply(force)
      apply(rename_tac d da e ea q' q'a eb c)(*strict*)
      apply(force)
     apply(rename_tac d da e ea q' q'a eb c)(*strict*)
     apply(rule_tac
      B="set w"
      in subset_trans)
      apply(rename_tac d da e ea q' q'a eb c)(*strict*)
      apply(rule List.set_take_subset)
     apply(rename_tac d da e ea q' q'a eb c)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' q'a eb c)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(rule_tac
      t="(q # F_DFA_GOTO_SEQUENCE M q (take (Suc i) w))"
      and s="map (case_option q epdaS_conf_state) (get_configurations da (length (take (Suc i) w)))"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(rule_tac
      t="last (map (case_option q epdaS_conf_state) (get_configurations da (length (take (Suc i) w))))"
      and s="(case_option q epdaS_conf_state) (last(get_configurations da (length (take (Suc i) w))))"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(rule last_map)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(subgoal_tac "\<forall>j<length((get_configurations da (length (take (Suc i) w)))). \<forall>c e. da j=Some (pair e c) \<longrightarrow> ((get_configurations da (length (take (Suc i) w))))!j=Some c")
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(take(Suc i)w)"
      in get_configurations_elem2)
     apply(rename_tac d da e ea q' q'a eb c)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' q'a eb c)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(blast)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(erule_tac
      x="length (take (Suc i) w)"
      in allE)
  apply(erule impE)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(rule_tac
      t="length (get_configurations da (length (take (Suc i) w)))"
      and s="Suc (length (take(Suc i)w))"
      in ssubst)
    apply(rename_tac d da e ea q' q'a eb c)(*strict*)
    apply(rule get_configurations_length)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(subgoal_tac "\<exists>e c. da (length (take (Suc i) w)) = Some (pair e c)")
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac d da e ea q' q'a eb c)(*strict*)
     apply(blast)
    apply(rename_tac d da e ea q' q'a eb c)(*strict*)
    apply(blast)
   apply(rename_tac d da e ea q' q'a eb c)(*strict*)
   apply(arith)
  apply(rename_tac d da e ea q' q'a eb c)(*strict*)
  apply(erule exE)+
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(erule_tac
      x="ca"
      in allE)
  apply(erule_tac
      x="ec"
      in allE)
  apply(erule impE)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(rule_tac
      t="(last (get_configurations da (length (take (Suc i) w))))"
      and s="get_configurations da (length (take (Suc i) w)) ! length (take (Suc i) w)"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(rule last_nth3)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(rule_tac
      t="length (get_configurations da (length (take (Suc i) w)))"
      and s="Suc (length (take(Suc i)w))"
      in ssubst)
    apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
    apply(rule get_configurations_length)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(rule_tac
      t="(case get_configurations da (length (take (Suc i) w)) ! length (take (Suc i) w) of None \<Rightarrow> q | Some a \<Rightarrow> epdaS_conf_state a)"
      and s="epdaS_conf_state ca"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(subgoal_tac "\<forall>j\<le>Suc i. case_option undefined (\<lambda>x. x) (get_configuration (da j)) = case_option undefined (\<lambda>c. c\<lparr>epdaS_conf_scheduler:=take ((Suc i) - j) (epdaS_conf_scheduler c)\<rparr>) (get_configuration (d j))")
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   prefer 2
   apply(rule allI)
   apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
   apply(rule impI)
   apply(rule DFA_derivation_input_restriction_still_simulates)
              apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
              apply(force)
             apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
             apply(blast)
            apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
            apply(force)
           apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
           apply(force)
          apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
          apply(force)
         apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
         apply(force)
        apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
        apply(force)
       apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
       apply(clarsimp)
      apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
      apply(force)
     apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
     apply(force)
    apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' q'a eb c ec ca j)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(erule impE)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(force)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(rule_tac
      t="epdaS_conf_state c"
      and s="case_option undefined epdaS_conf_state (get_configuration (d (Suc i)))"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(rule_tac
      t="epdaS_conf_state ca"
      and s="case_option undefined epdaS_conf_state (get_configuration (da (Suc i)))"
      in ssubst)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(rule_tac
      t="Suc i"
      and s="length (take (Suc i) w)"
      in ssubst)
    apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
    apply(force)
   apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac d da e ea q' q'a eb c ec ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da e q' q'a eb c ec z za zs zsa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "Suc i = ord_class.min (length w) (Suc i)")
   apply(rename_tac d da e q' q'a eb c ec z za zs zsa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d da e q' q'a eb c ec z za zs zsa)(*strict*)
  apply(clarsimp)
  done

lemma F_DFA_GOTO_SEQUENCE_length_last: "
  valid_dfa M
  \<Longrightarrow> M = M'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> q = q'
  \<Longrightarrow> q = q''
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> last (q' # F_DFA_GOTO_SEQUENCE M' q'' [a]) = F_DFA_GOTO M q a"
  apply(rule_tac
      t="last (q' # F_DFA_GOTO_SEQUENCE M' q'' [a])"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q [a])"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q [a]"
      and s="[F_DFA_GOTO M q a]"
      in ssubst)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(blast)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_length_last2: "
  valid_dfa M
  \<Longrightarrow> M = M'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> q = q'
  \<Longrightarrow> q = q''
  \<Longrightarrow> w = w'
  \<Longrightarrow> length w > 0
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> last (q' # F_DFA_GOTO_SEQUENCE M' q'' w') = last (F_DFA_GOTO_SEQUENCE M q w)"
  apply(rule_tac
      t="last (q' # F_DFA_GOTO_SEQUENCE M' q'' w')"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q w)"
      in ssubst)
   apply(force)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M q w)")
   apply(force)
  apply(rule_tac
      w="w"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DFA_GOTO_F_EPDA_GOTO_elem: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> X \<in> epda_events M
  \<Longrightarrow> x \<in> F_EPDA_GOTO M q X
  \<Longrightarrow> x = F_DFA_GOTO M q X"
  apply(subgoal_tac "{F_DFA_GOTO M q X} = F_EPDA_GOTO M q X")
   prefer 2
   apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
       apply(blast)+
  done

lemma nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> i \<le> length w
  \<Longrightarrow> (p # (F_DFA_GOTO_SEQUENCE M p w)) ! i = last (p # (F_DFA_GOTO_SEQUENCE M p (take i w)))"
  apply(case_tac i)
   apply(clarsimp)
   apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M p [])")
    apply(force)
   apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="(p # F_DFA_GOTO_SEQUENCE M p w) ! i"
      and s="F_DFA_GOTO_SEQUENCE M p w ! nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p (take i w))"
      and s="last (F_DFA_GOTO_SEQUENCE M p (take i w))"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "length (take i w) = length (F_DFA_GOTO_SEQUENCE M p (take i w))")
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(rule_tac
      B="set w"
      in subset_trans)
     apply(rename_tac nat)(*strict*)
     apply(rule List.set_take_subset)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="i"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

theorem DFA_F_DFA_GOTO_SEQUENCE_take_head: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p = epda_initial M
  \<Longrightarrow> set v \<subseteq> epda_events M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M p (a # v) = F_DFA_GOTO M p a # (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M p a) v)"
  apply(rule_tac
      t="F_DFA_GOTO M p a # (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M p a) v)"
      and s="F_DFA_GOTO_SEQUENCE M p [a] @ (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M p a) v)"
      in subst)
   apply(clarsimp)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(force)
  apply(subgoal_tac "length (a#v) = length (F_DFA_GOTO_SEQUENCE M p (a#v))")
   prefer 2
   apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "length [a] = length (F_DFA_GOTO_SEQUENCE M p [a])")
   prefer 2
   apply(rule_tac
      q="p"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "length v = length (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M p a) v)")
   prefer 2
   apply(rule_tac
      q="F_DFA_GOTO M p a"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(rule_tac
      ?q0.0="p"
      in DFA_F_DFA_GOTO_in_states)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<forall>w q. q=p \<and> w=a#v \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)+
    apply(rename_tac w q)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w q)(*strict*)
   apply(force)+
  apply(subgoal_tac "\<forall>w q. q=p \<and> w=[a] \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)
      apply(rename_tac w q)(*strict*)
      apply(blast)
     apply(rename_tac w q)(*strict*)
     apply(force)
    apply(rename_tac w q)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w q)(*strict*)
   apply(force)
  apply(subgoal_tac "\<forall>w q. q=F_DFA_GOTO M p a \<and> w=v \<longrightarrow> (\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w))")
   prefer 2
   apply(rule allI,rule allI,rule impI)
   apply(rename_tac w q)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac w q)(*strict*)
       apply(blast)
      apply(rename_tac w q)(*strict*)
      apply(blast)
     apply(rename_tac w q)(*strict*)
     apply(force)
    apply(rename_tac w q)(*strict*)
    apply(rule DFA_F_DFA_GOTO_in_states)
         apply(rename_tac w q)(*strict*)
         apply(force)
        apply(rename_tac w q)(*strict*)
        apply(force)
       apply(rename_tac w q)(*strict*)
       apply(force)
      apply(rename_tac w q)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(force)
     apply(rename_tac w q)(*strict*)
     apply(force)
    apply(rename_tac w q)(*strict*)
    apply(force)
   apply(rename_tac w q)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
  apply(rule_tac
      t="zs"
      and s="drop (Suc 0) (get_configurations d (length zsb + length zsa))"
      in ssubst)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule_tac
      t="get_configurations d (length zsb + length zsa)"
      and s="z#zs"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule sym)
   apply(rule drop1)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
  apply(rule_tac
      t="zsa"
      and s="drop (Suc 0) (get_configurations da (length zsa))"
      in ssubst)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule_tac
      t="get_configurations da (length zsa)"
      and s="za#zsa"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule sym)
   apply(rule drop1)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
  apply(rule_tac
      t="zsb"
      and s="drop (Suc 0) (get_configurations db (length zsb))"
      in ssubst)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule_tac
      t="get_configurations db (length zsb)"
      and s="zb#zsb"
      in ssubst)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(rule sym)
   apply(rule drop1)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
  apply(rule listEqI)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length zsa=Suc 0")
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length zs=Suc (length v)")
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
     prefer 2
     apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
       apply(blast)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
      apply(blast)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
     apply(arith)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
    apply(erule exE)+
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(rule_tac
      t="zs!i"
      and s="Some c"
      in ssubst)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(subgoal_tac "\<forall>i<length(z#zs). \<forall>c e. d i=Some (pair e c) \<longrightarrow> (z#zs)!i=Some c")
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      prefer 2
      apply(rule_tac
      n="Suc (length zsb)"
      in get_configurations_elem)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(blast)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(blast)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(erule_tac
      x="Suc i"
      in allE)
     apply(erule impE)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(erule_tac
      x="c"
      in allE)
     apply(erule_tac
      x="Some ec"
      in allE)
     apply(erule impE)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(force)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "d=derivation_append (derivation_map da (\<lambda>x. x\<lparr>epdaS_conf_scheduler:=(epdaS_conf_scheduler x)@v\<rparr>)) db (Suc 0)")
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(case_tac i)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(clarsimp)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
      apply(rule_tac
      t="(map (case_option (epda_initial M) epdaS_conf_state) zsa @ map (case_option (F_DFA_GOTO M (epda_initial M) a) epdaS_conf_state) zsb) ! 0"
      and s="(map (case_option (epda_initial M) epdaS_conf_state) zsa) ! 0"
      in ssubst)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
       apply(rule nth_append_1)
       apply(force)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "\<forall>i<length(za#zsa). \<forall>c e. da i=Some (pair e c) \<longrightarrow> (za#zsa)!i=Some c")
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
       prefer 2
       apply(rule_tac
      n="Suc 0"
      in get_configurations_elem)
         apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
         apply(force)
        apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
        apply(blast)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
       apply(blast)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
      apply(erule_tac
      x="Suc 0"
      in allE)
      apply(erule impE)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
       apply(force)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
      apply(erule_tac
      x="\<lparr>epdaS_conf_state = q'a, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
      apply(erule_tac
      x="ea"
      in allE)
      apply(erule impE)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
       apply(force)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_append_def derivation_map_def)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
     apply(rule_tac
      t="(map (case_option (epda_initial M) epdaS_conf_state) zsa @ map (case_option (F_DFA_GOTO M (epda_initial M) a) epdaS_conf_state) zsb) ! Suc nat"
      and s="(map (case_option (F_DFA_GOTO M (epda_initial M) a) epdaS_conf_state) zsb) ! nat"
      in ssubst)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      apply(rule nth_shift_append)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
       apply(force)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      apply(force)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<forall>i<length(zb#zsb). \<forall>c e. db i=Some (pair e c) \<longrightarrow> (zb#zsb)!i=Some c")
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      prefer 2
      apply(rule_tac
      n="length zsb"
      in get_configurations_elem)
        apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
        apply(force)
       apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
       apply(blast)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      apply(blast)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
     apply(erule_tac
      x="Suc nat"
      in allE)
     apply(erule impE)
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      apply(force)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
     apply(subgoal_tac "\<exists>e c. db (Suc nat) = Some (pair e c)")
      apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
      prefer 2
      apply(simp add: derivation_append_def derivation_map_def)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat ed ca)(*strict*)
     apply(case_tac c)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat ed ca epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stack)(*strict*)
     apply(case_tac ca)
     apply(rename_tac da db e q' ea q'a eb q'b z zs za zsa zb zsb ec c nat ed ca epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stack epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stacka)(*strict*)
     apply(simp add: derivation_append_def derivation_map_def)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(rule_tac
      M="M"
      and ?e2.0="if zsb=[] then ea else eb"
      and ?c2.0="if zsb=[] then \<lparr>epdaS_conf_state = q'a, epdaS_conf_scheduler = v, epdaS_conf_stack = [epda_box M]\<rparr> else \<lparr>epdaS_conf_state = q'b, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in epdaS.derivationsCoincideR)
            apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
            defer
            apply(blast)
           apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
           apply(blast)
          apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
          apply(blast)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
         apply(blast)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
        defer
        apply(rule_tac
      t="Suc (length zsb)"
      and s="Suc 0+length zsb"
      in ssubst)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
         apply(force)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
        apply(rule_tac concat_has_max_dom)
         apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
         apply(rule derivation_map_preserves_maximum_of_domain)
         apply(blast)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(simp add: derivation_append_def derivation_map_def)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(case_tac "zsb")
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(simp add: derivation_append_def derivation_map_def)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c aa list)(*strict*)
      apply(subgoal_tac "zsb\<noteq>[]")
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c aa list)(*strict*)
       apply(thin_tac "zsb=aa#list")
       apply(clarsimp)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(simp add: derivation_append_def derivation_map_def)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c aa list)(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
    prefer 2
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(simp (no_asm) only: epdaS.is_forward_deterministic_accessible_def)
    apply(rule conjI)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
     apply(rule epda_is_is_forward_target_deterministic_accessible)
     apply(blast)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
  apply(subgoal_tac "epdaS.derivation M (derivation_map da (\<lambda>x. x\<lparr>epdaS_conf_scheduler := epdaS_conf_scheduler x @ v\<rparr>))")
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   prefer 2
   apply(rule epdaS.derivation_map_preserves_derivation2)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c aa ed b)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
  apply(rule epdaS.derivation_append_preserves_derivation_initial)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(rule epdaS.derivation_map_preserves_derivation_initial)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      defer
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(force)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c ca)(*strict*)
    apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
    apply(clarsimp)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(rule epdaS.derivation_concat2)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(rule epdaS.derivation_map_preserves_derivation2)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(blast)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(clarsimp)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c aa ed b)(*strict*)
      apply(simp add: epdaS_step_relation_def)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(blast)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(simp add: derivation_map_def)
   apply(rule equalsFUNF_DFA_GOTO)
        apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
        apply(force)
       apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
       apply(force)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(force)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(force)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(subgoal_tac "\<exists>e c. da (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    prefer 2
    apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
      apply(blast)
     apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
     apply(blast)
    apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
    apply(arith)
   apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
   apply(subgoal_tac "epdaS_step_relation M \<lparr>epdaS_conf_state = (epda_initial M), epdaS_conf_scheduler = [a], epdaS_conf_stack = [epda_box M]\<rparr> ed \<lparr>epdaS_conf_state = q'a, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>")
    apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
    prefer 2
    apply(rule_tac
      d="da"
      in epdaS.position_change_due_to_step_relation)
      apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
      apply(force)
     apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
     apply(force)
    apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
    apply(force)
   apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
   apply(simp add: epdaS_step_relation_def)
   apply(rule_tac
      t="\<lparr>edge_src = epda_initial M, edge_event = Some a, edge_pop = [epda_box M], edge_push = [epda_box M], edge_trg = edge_trg ed\<rparr>"
      and s="ed"
      in ssubst)
    apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed)(*strict*)
   apply(case_tac ed)
   apply(rename_tac d da db e q' q'a eb q'b z zs za zsa zb zsb i ec c ed edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_event edge_pop edge_trg w)(*strict*)
   apply(case_tac edge_event)
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_event edge_pop edge_trg w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_pop edge_trg w)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_event edge_pop edge_trg w aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_pop edge_trg w aa)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac edge_pop)
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_pop edge_trg w aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_trg)(*strict*)
    prefer 2
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_pop edge_trg w aa aaa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_trg)(*strict*)
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>edge_src = epda_initial M, edge_event = Some a, edge_pop = [], edge_push = [], edge_trg = edge_trg\<rparr>"
      in ballE)
    apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_trg)(*strict*)
    apply(clarsimp)
   apply(rename_tac d da db e q' eb q'b z zs za zsa zb zsb i ec c edge_trg)(*strict*)
   apply(force)
  apply(rename_tac d da db e q' ea q'a eb q'b z zs za zsa zb zsb i ec c)(*strict*)
  apply(simp add: epdaS.derivation_initial_def)
  apply(simp add: epdaS_initial_configurations_def epdaS_configurations_def)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  done

corollary DFA_F_DFA_GOTO_SEQUENCE_take_head_prime: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p = epda_initial M
  \<Longrightarrow> set v \<subseteq> epda_events M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> w = a # v
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M p w = F_DFA_GOTO M p a # (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M p a) v)"
  apply(rule_tac
      t="w"
      and s="a#v"
      in ssubst)
   apply(force)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_take_head)
       apply(force)+
  done

lemma F_DFA_GOTO_SEQUENCE_not_empty: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q w \<noteq> []"
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M q w)")
   prefer 2
   apply(rule_tac
      w="w"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_dropTerminal_last: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q = epda_initial M
  \<Longrightarrow> set (w @ [x]) \<subseteq> epda_events M
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M q (w @ [x])) = F_DFA_GOTO M (last (q # F_DFA_GOTO_SEQUENCE M q w)) x"
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M q w)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (w@[x]) = length (F_DFA_GOTO_SEQUENCE M q (w@[x]))")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac w)
   apply(clarsimp)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [x]"
      and s="[F_DFA_GOTO M (epda_initial M) x]"
      in ssubst)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M q (w @ [x]))"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M q w)) [x])"
      in subst)
   apply(rename_tac a list)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_concat)
          apply(rename_tac a list)(*strict*)
          apply(force)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<forall>i<length (w@[x]). F_DFA_GOTO SSM ((q # (F_DFA_GOTO_SEQUENCE M q (w@[x]))) ! i) ((w@[x]) ! i) = (F_DFA_GOTO_SEQUENCE M q (w@[x])) ! i" for SSM)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main2)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "w\<noteq>[]")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(erule_tac
      x="length w"
      in allE)
  apply(auto)
  apply(subgoal_tac "set (F_DFA_GOTO_SEQUENCE M (epda_initial M) w) \<subseteq> epda_states M")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main3)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="(F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [x])"
      and s="([F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) x])"
      in ssubst)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma last_F_DFA_GOTO_SEQUENCE_append: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M q w) = last (x @ (F_DFA_GOTO_SEQUENCE M q w))"
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M q w)")
   prefer 2
   apply(rule_tac
      M="M"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule last_append)
  apply(force)
  done

lemma last_F_DFA_GOTO_SEQUENCE_Cons: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M q w) = last (x # (F_DFA_GOTO_SEQUENCE M q w))"
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M q w)")
   prefer 2
   apply(rule_tac
      M="M"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(case_tac w)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_injective_rev: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set v \<subseteq> (epda_events M)
  \<Longrightarrow> length w > 0
  \<Longrightarrow> length v > 0
  \<Longrightarrow> qseq_w = F_DFA_GOTO_SEQUENCE M q w
  \<Longrightarrow> qseq_v = F_DFA_GOTO_SEQUENCE M q v
  \<Longrightarrow> last qseq_w = last qseq_v
  \<Longrightarrow> \<forall>e. e \<in> (epda_delta M) \<longrightarrow> edge_trg e \<noteq> q
  \<Longrightarrow> \<forall>q' e1 e2. q' \<in> set (q # qseq_w) \<and> e1 \<in> (epda_delta M) \<and> e2 \<in> (epda_delta M) \<and> edge_trg e2 = edge_trg e1 \<and> (edge_trg e1 = q') \<longrightarrow> e1 = e2
  \<Longrightarrow> w = v"
  apply(subgoal_tac "\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=w,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q w)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length w)) \<and> maximum_of_domain d (length w)")
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d e q' z zs)(*strict*)
  apply(subgoal_tac "\<exists>d e q'. epdaS.derivation M d \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=q,epdaS_conf_scheduler=v,epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length v) = Some (pair e \<lparr>epdaS_conf_state=q',epdaS_conf_scheduler=[],epdaS_conf_stack=[epda_box M]\<rparr>) \<and> q#(F_DFA_GOTO_SEQUENCE M q v)=map (\<lambda>x. case x of None \<Rightarrow> q | Some x \<Rightarrow> epdaS_conf_state x) (get_configurations d (length v)) \<and> maximum_of_domain d (length v)")
   apply(rename_tac d e q' z zs)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCE_to_derivation)
       apply(rename_tac d e q' z zs)(*strict*)
       apply(force)
      apply(rename_tac d e q' z zs)(*strict*)
      apply(force)
     apply(rename_tac d e q' z zs)(*strict*)
     apply(force)
    apply(rename_tac d e q' z zs)(*strict*)
    apply(force)
   apply(rename_tac d e q' z zs)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e q' z zs)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e q' z zs da ea q'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e q' z zs da ea q'a za zsa)(*strict*)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
  apply(subgoal_tac "length w = length d1seq")
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   prefer 2
   apply(subgoal_tac "length w=length (map (case_option q epdaS_conf_state) d1seq)")
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
         apply(force)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(force)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(force)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
     apply(force)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
    apply(force)
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   apply(force)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
  apply(subgoal_tac "length v = length d2seq")
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   prefer 2
   apply(subgoal_tac "length v=length (map (case_option q epdaS_conf_state) d2seq)")
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
         apply(force)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(force)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(force)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
     apply(force)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
    apply(force)
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   apply(force)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
  apply(subgoal_tac "\<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = w, epdaS_conf_stack = [epda_box M]\<rparr> = \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = v, epdaS_conf_stack = [epda_box M]\<rparr>")
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   apply(force)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
  apply(rule_tac
      M="M"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in epdaS.derivation_injective)
               apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
               apply(rule epda_is_backward_target_deterministic)
               apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
              apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
              apply(force)
             apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
             apply(force)
            apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
            apply(force)
           apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
           apply(force)
          apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
          apply(force)
         apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
         apply(force)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(simp add: epdaS_configurations_def)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(simp add: epdaS_configurations_def)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(force)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
     apply(rule_tac
      t="d1fin"
      and s="d2fin"
      in ssubst)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(rule_tac
      t="d1fin"
      and s="last (map (case_option q epdaS_conf_state) d1seq)"
      in ssubst)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last (map (case_option q epdaS_conf_state) d1seq)"
      and s="(case_option q epdaS_conf_state) (last d1seq)"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(rule last_map)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(subgoal_tac "\<forall>i<length(d1seq1#d1seq). \<forall>c e. d1 i=Some (pair e c) \<longrightarrow> (d1seq1#d1seq)!i=Some c")
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        prefer 2
        apply(rule_tac
      n="length w"
      in get_configurations_elem)
          apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
          apply(force)
         apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
         apply(force)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(erule_tac
      x="length d1seq"
      in allE)
       apply(erule impE)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(erule_tac
      x="\<lparr>epdaS_conf_state = d1fin, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
       apply(erule_tac
      x="d1e"
      in allE)
       apply(erule impE)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last d1seq"
      and s="last (d1seq1#d1seq)"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last (d1seq1#d1seq)"
      and s="(d1seq1 # d1seq) ! (length d1seq) "
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(rule last_nth3)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="(d1seq1 # d1seq) ! length d1seq"
      and s="Some \<lparr>epdaS_conf_state = d1fin, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(force)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(rule_tac
      t="d2fin"
      and s="last (map (case_option q epdaS_conf_state) d2seq)"
      in ssubst)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last (map (case_option q epdaS_conf_state) d2seq)"
      and s="(case_option q epdaS_conf_state) (last d2seq)"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(rule last_map)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(subgoal_tac "\<forall>i<length(d2seq1#d2seq). \<forall>c e. d2 i=Some (pair e c) \<longrightarrow> (d2seq1#d2seq)!i=Some c")
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        prefer 2
        apply(rule_tac
      n="length v"
      in get_configurations_elem)
          apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
          apply(force)
         apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
         apply(force)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(erule_tac
      x="length d2seq"
      in allE)
       apply(erule impE)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(erule_tac
      x="\<lparr>epdaS_conf_state = d2fin, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in allE)
       apply(erule_tac
      x="d2e"
      in allE)
       apply(erule impE)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last d2seq"
      and s="last (d2seq1#d2seq)"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="last (d2seq1#d2seq)"
      and s="(d2seq1 # d2seq) ! (length d2seq) "
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(rule last_nth3)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(rule_tac
      t="(d2seq1 # d2seq) ! length d2seq"
      and s="Some \<lparr>epdaS_conf_state = d2fin, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>"
      in ssubst)
        apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
        apply(force)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
       apply(force)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
      apply(force)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
     apply(force)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
    apply(erule_tac
      x="e1"
      and P="\<lambda>e1. \<forall>e2. (edge_trg e1 = q \<or> edge_trg e1 \<in> case_option q epdaS_conf_state ` set d1seq) \<and> e1 \<in> epda_delta M \<and> e2 \<in> epda_delta M \<and> edge_trg e2 = edge_trg e1 \<longrightarrow> e1 = e2"
      in allE)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
    apply(erule_tac
      x="e2"
      and P="\<lambda>e2. (edge_trg e1 = q \<or> edge_trg e1 \<in> case_option q epdaS_conf_state ` set d1seq) \<and> e1 \<in> epda_delta M \<and> e2 \<in> epda_delta M \<and> edge_trg e2 = edge_trg e1 \<longrightarrow> e1 = e2"
      in allE)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
    apply(erule impE)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
     apply(rule conjI)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
      apply(erule disjE)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
       apply(rule disjI1)
       apply(clarsimp)
       apply(rename_tac d1 d1e d1fin d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
       apply(simp add: epdaS_step_relation_def)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
      apply(rule disjI2)
      apply(simp add: epdaS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2 wa waa)(*strict*)
      apply(rule inMap)
      apply(rule_tac
      x="Some c"
      in bexI)
       apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2 wa waa)(*strict*)
       apply(clarsimp)
      apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c' e)(*strict*)
   apply(erule_tac
      x="e"
      and P="\<lambda>e. e \<in> epda_delta M \<longrightarrow> edge_trg e \<noteq> q"
      in allE)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d1e d1fin d1seq1 d1seq d2 d2e d2fin d2seq1 d2seq c' e)(*strict*)
  apply(erule_tac
      x="e"
      and P="\<lambda>e. e \<in> epda_delta M \<longrightarrow> edge_trg e \<noteq> q"
      in allE)
  apply(simp add: epdaS_step_relation_def)
  done

theorem F_DFA_GOTO_SEQUENCE_append_split: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p = epda_initial M
  \<Longrightarrow> set w1 \<subseteq> epda_events M
  \<Longrightarrow> set w2 \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M p (w1 @ w2) = F_DFA_GOTO_SEQUENCE M p w1 @ (F_DFA_GOTO_SEQUENCE M (last (p # (F_DFA_GOTO_SEQUENCE M p w1))) w2)"
  apply(subgoal_tac "length (w1 @ w2) = length (F_DFA_GOTO_SEQUENCE M p (w1 @ w2))")
   prefer 2
   apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "length w1=length (F_DFA_GOTO_SEQUENCE M p w1)")
   prefer 2
   apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(rule listEqI)
   apply(case_tac w2)
    apply(clarsimp)
    apply(rule conjI)
     apply(subgoal_tac "length []=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
      prefer 2
      apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
           apply(force)
          apply(force)
         apply(force)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(subgoal_tac "length []=length (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w1)) [])")
     prefer 2
     apply(rule_tac
      q="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w1)"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(force)
       apply(rule_tac
      ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
             apply(force)
            apply(force)
           apply(force)
          apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "w2\<noteq>[]")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(thin_tac "w2=a#list")
   apply(subgoal_tac "length w2=length(F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2)")
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      q="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(case_tac w1)
      apply(rename_tac a list)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac a list aa lista)(*strict*)
     apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      and s="last (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
      apply(rename_tac a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac a list aa lista)(*strict*)
     apply(rule_tac
      ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
           apply(rename_tac a list aa lista)(*strict*)
           apply(force)
          apply(rename_tac a list aa lista)(*strict*)
          apply(force)
         apply(rename_tac a list aa lista)(*strict*)
         apply(force)
        apply(rename_tac a list aa lista)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac a list aa lista)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac a list aa lista)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M p (w1 @ w2) ! i"
      and s="(p#F_DFA_GOTO_SEQUENCE M p (w1 @ w2)) ! (Suc i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(p # F_DFA_GOTO_SEQUENCE M p (w1 @ w2)) ! Suc i"
      and s="last (p#(F_DFA_GOTO_SEQUENCE M p (take (Suc i) (w1@w2))))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i<length w1")
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(F_DFA_GOTO_SEQUENCE M p w1 @ F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2) ! i"
      and s="F_DFA_GOTO_SEQUENCE M p w1!i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M p w1 ! i"
      and s="(p#F_DFA_GOTO_SEQUENCE M p w1) ! (Suc i)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(p # F_DFA_GOTO_SEQUENCE M p w1) ! Suc i"
      and s="last (p#(F_DFA_GOTO_SEQUENCE M p (take (Suc i) w1)))"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "length w1\<le>i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "i<length (w1@w2)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(F_DFA_GOTO_SEQUENCE M p w1 @ F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2) ! i"
      and s="(F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2) ! (i-length w1)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="length w1"
      and s="length (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2 ! (i - length w1)"
      and s="((last (p # F_DFA_GOTO_SEQUENCE M p w1))#F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2) ! (Suc (i - length w1))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(last (p # F_DFA_GOTO_SEQUENCE M p w1) # F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) w2) ! Suc (i - length w1)"
      and s="last (last (p # F_DFA_GOTO_SEQUENCE M p w1)#(F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) (take (Suc (i - length w1)) w2)))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(case_tac w1)
      apply(rename_tac i)(*strict*)
      apply(clarsimp)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac i a list)(*strict*)
     apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      and s="last (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
      apply(rename_tac i a list)(*strict*)
      apply(force)
     apply(rename_tac i a list)(*strict*)
     apply(rule_tac
      ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
           apply(rename_tac i a list)(*strict*)
           apply(force)
          apply(rename_tac i a list)(*strict*)
          apply(force)
         apply(rename_tac i a list)(*strict*)
         apply(force)
        apply(rename_tac i a list)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac i a list)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac i a list)(*strict*)
      apply(force)
     apply(rename_tac i a list)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(case_tac "w2")
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i a list)(*strict*)
  apply(subgoal_tac "w2\<noteq>[]")
   apply(rename_tac i a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i a list)(*strict*)
  apply(thin_tac "w2=a#list")
  apply(case_tac w1)
   apply(rename_tac i a list)(*strict*)
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(subgoal_tac "w1\<noteq>[]")
   apply(rename_tac i a list aa lista)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(thin_tac "w1=aa#lista")
  apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p (take (Suc i) (w1 @ w2)))"
      and s="last (F_DFA_GOTO_SEQUENCE M p (take (Suc i) (w1 @ w2)))"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(subgoal_tac "length (take(Suc i)(w1@w2))=length(F_DFA_GOTO_SEQUENCE M p (take (Suc i) (w1 @ w2)))")
    apply(rename_tac i a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac i a list aa lista)(*strict*)
        apply(force)
       apply(rename_tac i a list aa lista)(*strict*)
       apply(force)
      apply(rename_tac i a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac i a list aa lista)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i a list aa lista)(*strict*)
    apply (metis set_concat_subset List.set_take_subset subset_trans)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(rule_tac
      t="last (last (p # F_DFA_GOTO_SEQUENCE M p w1) # F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) (take (Suc (i - length w1)) w2))"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) (take (Suc (i - length w1)) w2))"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(subgoal_tac "length (F_DFA_GOTO_SEQUENCE M (last (p # F_DFA_GOTO_SEQUENCE M p w1)) (take (Suc (i - length w1)) w2)) = length (take (Suc (i - length w1)) w2)")
    apply(rename_tac i a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(rule sym)
   apply(rule_tac
      q="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac i a list aa lista)(*strict*)
        apply(force)
       apply(rename_tac i a list aa lista)(*strict*)
       apply(force)
      apply(rename_tac i a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac i a list aa lista)(*strict*)
     apply(case_tac w1)
      apply(rename_tac i a list aa lista)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac i a list aa lista ab listb)(*strict*)
     apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      and s="last (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
      apply(rename_tac i a list aa lista ab listb)(*strict*)
      apply(force)
     apply(rename_tac i a list aa lista ab listb)(*strict*)
     apply(rule_tac
      ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
           apply(rename_tac i a list aa lista ab listb)(*strict*)
           apply(force)
          apply(rename_tac i a list aa lista ab listb)(*strict*)
          apply(force)
         apply(rename_tac i a list aa lista ab listb)(*strict*)
         apply(force)
        apply(rename_tac i a list aa lista ab listb)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac i a list aa lista ab listb)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac i a list aa lista ab listb)(*strict*)
      apply(force)
     apply(rename_tac i a list aa lista ab listb)(*strict*)
     apply(force)
    apply(rename_tac i a list aa lista)(*strict*)
    apply (metis List.set_take_subset subset_trans)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(rule_tac
      t="last (p # F_DFA_GOTO_SEQUENCE M p w1)"
      and s="last (F_DFA_GOTO_SEQUENCE M p w1)"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M p w1)) (take (Suc (i - length w1)) w2))"
      and s="last (F_DFA_GOTO_SEQUENCE M p (w1@(take (Suc (i - length w1)) w2)))"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_concat)
          apply(rename_tac i a list aa lista)(*strict*)
          apply(force)
         apply(rename_tac i a list aa lista)(*strict*)
         apply(force)
        apply(rename_tac i a list aa lista)(*strict*)
        apply(force)
       apply(rename_tac i a list aa lista)(*strict*)
       apply(force)
      apply(rename_tac i a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac i a list aa lista)(*strict*)
     apply (metis List.set_take_subset subset_trans)
    apply(rename_tac i a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac i a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(rule_tac
      t="take (Suc i) (w1 @ w2)"
      and s="w1 @ take (Suc (i - length w1)) w2"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i a list aa lista)(*strict*)
  apply(thin_tac "length (w1 @ w2) = length (F_DFA_GOTO_SEQUENCE M p (w1 @ w2))")
  apply(thin_tac "length w1 = length (F_DFA_GOTO_SEQUENCE M p w1)")
  apply(thin_tac "i < length (F_DFA_GOTO_SEQUENCE M p (w1 @ w2))")
  apply(thin_tac "valid_dfa M")
  apply(thin_tac "some_step_from_every_configuration M")
  apply(thin_tac "every_state_in_some_accessible_configuration M")
  apply(thin_tac "p = epda_initial M")
  apply(thin_tac "set w1 \<subseteq> epda_events M")
  apply(thin_tac "set w2 \<subseteq> epda_events M")
  apply(rule_tac
      t="take (Suc i) (w1 @ w2)"
      and s="w1 @ take (Suc i - length w1) w2"
      in ssubst)
   apply(rename_tac i a list aa lista)(*strict*)
   apply (metis less_Suc_eq_le nat_less_le take_all take_append)
  apply(rename_tac i a list aa lista)(*strict*)
  apply (metis Suc_diff_le)
  done

theorem F_DFA_GOTO_SEQUENCE_append_split_SHORT: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> p = epda_initial M
  \<Longrightarrow> set w1 \<subseteq> epda_events M
  \<Longrightarrow> set w2 \<subseteq> epda_events M
  \<Longrightarrow> rw1 = F_DFA_GOTO_SEQUENCE M p w1
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M p (w1 @ w2) = rw1 @ (F_DFA_GOTO_SEQUENCE M (last (p # rw1)) w2)"
  apply(rule_tac t="rw1" and s="F_DFA_GOTO_SEQUENCE M p w1" in ssubst)
   apply(force)
  apply(rule_tac t="rw1" and s="F_DFA_GOTO_SEQUENCE M p w1" in ssubst)
   apply(force)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
       apply(force)+
  done

lemma F_DFA_GOTO_SEQUENCE_butlast_last: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> (F_DFA_GOTO_SEQUENCE M (epda_initial M) w) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a]))] = (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a]))"
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a])"
      and s="F_DFA_GOTO_SEQUENCE M SSp SSw1 @ (F_DFA_GOTO_SEQUENCE M (last (SSp#(F_DFA_GOTO_SEQUENCE M SSp SSw1))) SSw2)" for SSp SSw1 SSw2
      in ssubst)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(rule_tac
      t="[last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])]"
      and s="F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a]"
      in ssubst)
   prefer 2
   apply(force)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   prefer 2
   apply(rule_tac
      w="w"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(case_tac w)
   apply(clarsimp)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [a]"
      and s="[F_DFA_GOTO M (epda_initial M) a]"
      in ssubst)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(subgoal_tac "w\<noteq>[]")
   apply(rename_tac aa list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(thin_tac "w=aa#list")
  apply(clarsimp)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) w \<noteq> []")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length [a] = length (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])")
   prefer 2
   apply(rule_tac
      w="[a]"
      and q="(last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(rule_tac
      w="w"
      and ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
           apply(force)
          apply(force)
         apply(force)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])"
      in ssubst)
   apply(rule last_appendR)
   apply(force)
  apply(clarsimp)
  apply(rule last_triv)
  apply(force)
  done

corollary F_DFA_GOTO_SEQUENCE_shift_to_last: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> q = epda_initial M
  \<Longrightarrow> set (a # w) \<subseteq> epda_events M
  \<Longrightarrow> [last (F_DFA_GOTO_SEQUENCE M q (a # w))] = F_DFA_GOTO_SEQUENCE M (last (q # (F_DFA_GOTO_SEQUENCE M q (butlast (a # w))))) [last (a # w)]"
  apply(subgoal_tac "set (butlast (a # w)) \<subseteq> epda_events M")
   prefer 2
   apply(rule_tac
      B="set (a#w)"
      in subset_trans)
    apply(rule trivButLast)
   apply(force)
  apply(subgoal_tac "last (a # w) \<in> epda_events M")
   prefer 2
   apply(rule_tac
      A="set (a#w)"
      in set_mp)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q (a#w)"
      and s="F_DFA_GOTO_SEQUENCE M q ((butlast(a#w))@[last(a#w)])"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q (butlast (a # w) @ [last (a # w)])"
      and s="F_DFA_GOTO_SEQUENCE M q (butlast (a # w)) @ (F_DFA_GOTO_SEQUENCE M (last (q#(F_DFA_GOTO_SEQUENCE M q (butlast (a # w))))) [last(a#w)])"
      in ssubst)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (q # F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))) [last (a # w)]"
      and s="[F_DFA_GOTO M (last (q # F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))) (last (a # w))]"
      in ssubst)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(force)
    apply(case_tac "F_DFA_GOTO_SEQUENCE M q (butlast (a # w))")
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac aa list)(*strict*)
    apply(rule_tac
      t="last (q # F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))"
      and s="last (F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))"
      in ssubst)
     apply(rename_tac aa list)(*strict*)
     apply(force)
    apply(rename_tac aa list)(*strict*)
    apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))"
      in set_mp)
     apply(rename_tac aa list)(*strict*)
     apply(rule_tac
      w="butlast(a#w)"
      in F_DFA_GOTO_SEQUENCESound_main3)
          apply(rename_tac aa list)(*strict*)
          apply(force)
         apply(rename_tac aa list)(*strict*)
         apply(force)
        apply(rename_tac aa list)(*strict*)
        apply(force)
       apply(rename_tac aa list)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac aa list)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac aa list)(*strict*)
     apply(force)
    apply(rename_tac aa list)(*strict*)
    apply(force)
   apply(force)
  apply(subgoal_tac "length (butlast (a # w)) = length (F_DFA_GOTO_SEQUENCE M q (butlast (a # w)))")
   prefer 2
   apply(rule_tac
      M="M"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_DFA_GOTOSeq_drop_tail: "
  valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a]))] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a])"
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a]))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a]))"
      in ssubst)
   apply(rule sym)
   apply(rule_tac
      t="epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a])"
      and s="[epda_initial M] @ F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a])"
      in ssubst)
    apply(force)
   apply(rule last_F_DFA_GOTO_SEQUENCE_append)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [a])"
      and s="F_DFA_GOTO_SEQUENCE M SSp SSw1 @ (F_DFA_GOTO_SEQUENCE M (last (SSp#(F_DFA_GOTO_SEQUENCE M SSp SSw1))) SSw2)" for SSp SSw1 SSw2
      in ssubst)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
   prefer 2
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   prefer 2
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) w) \<in> epda_states M")
   prefer 2
   apply(case_tac w)
    apply(clarsimp)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac aa list)(*strict*)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac aa list)(*strict*)
    apply(force)
   apply(rename_tac aa list)(*strict*)
   apply(rule_tac
      w="w"
      and ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
         apply(rename_tac aa list)(*strict*)
         apply(force)
        apply(rename_tac aa list)(*strict*)
        apply(force)
       apply(rename_tac aa list)(*strict*)
       apply(force)
      apply(rename_tac aa list)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac aa list)(*strict*)
     apply(force)
    apply(rename_tac aa list)(*strict*)
    apply(force)
   apply(rename_tac aa list)(*strict*)
   apply(force)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])"
      in ssubst)
   apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a]\<noteq>[]")
    apply(force)
   apply(subgoal_tac "length [a] = length (F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a])")
    prefer 2
    apply(rule_tac
      q="(last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [a]"
      and s="[F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) a]"
      in ssubst)
   prefer 2
   apply(force)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
