section {*FUNCTION\_\_PARSERRTR\_\_REMOVE\_OF\_TOP\_RULES*}
theory
  FUNCTION__PARSERRTR__REMOVE_OF_TOP_RULES

imports
  PRJ_12_06_07__ENTRY

begin

definition F_PARSER_RTR__rules_annotate_word_rev :: "
  ('stack \<times> 'event list) list
  \<Rightarrow> 'stack list"
  where
    "F_PARSER_RTR__rules_annotate_word_rev w \<equiv>
  map (\<lambda>(a, b). a) w"

definition F_PARSER_RTR__word_get_annotation :: "
  ('stack \<times> 'event list) list
  \<Rightarrow> 'event list"
  where
    "F_PARSER_RTR__word_get_annotation w \<equiv>
  snd (last w)"

definition F_PARSER_RTR__rule_annotate :: "
  ('stack, 'event) parser_step_label
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack \<times> 'event list, 'event) parser_step_label"
  where
    "F_PARSER_RTR__rule_annotate e w1 w2 \<equiv>
  \<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop e) w1,
  rule_rpop =
      if w1 = []
      then rule_rpop e
      else [],
  rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush e) w2,
  rule_rpush = []\<rparr>"

definition F_PARSER_RTR__rule_annotate__rev :: "
  ('stack \<times> 'event list, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parser_step_label"
  where
    "F_PARSER_RTR__rule_annotate__rev e \<equiv>
  \<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (rule_lpop e),
  rule_rpop = F_PARSER_RTR__word_get_annotation (rule_lpop e) @ rule_rpop e,
  rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (rule_lpush e),
  rule_rpush = F_PARSER_RTR__word_get_annotation (rule_lpush e)\<rparr>"

definition F_PARSER_RTR__conf_annotate :: "
  ('stack, 'event) parserFS_conf
  \<Rightarrow> ('stack \<times> 'event list, 'event) parserFS_conf"
  where
    "F_PARSER_RTR__conf_annotate c \<equiv>
  \<lparr>parserFS_conf_fixed = [],
  parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack c) (parserFS_conf_fixed c),
  parserFS_conf_scheduler = parserFS_conf_scheduler c\<rparr>"

definition F_PARSER_RTR__conf_annotate__rev :: "
  ('stack \<times> 'event list, 'event) parserFS_conf
  \<Rightarrow> ('stack, 'event) parserFS_conf"
  where
    "F_PARSER_RTR__conf_annotate__rev c \<equiv>
  \<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c),
  parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c),
  parserFS_conf_scheduler = parserFS_conf_scheduler c\<rparr>"

definition F_PARSER_RTR__derivation_annotate__rev :: "
  (('stack \<times> 'event list, 'event) parser_step_label, ('stack \<times> 'event list, 'event) parserFS_conf) derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf) derivation"
  where
    "F_PARSER_RTR__derivation_annotate__rev d \<equiv>
   (\<lambda>n.
    case d n of None \<Rightarrow> None
    | Some (pair e c) \<Rightarrow>
        Some (pair
          (case e of None \<Rightarrow> None | Some e' \<Rightarrow> Some (F_PARSER_RTR__rule_annotate__rev e'))
          (F_PARSER_RTR__conf_annotate__rev c)))"

definition F_PARSER_RTR__conf_get_annotation :: "
  ('stack \<times> 'event list, 'event) parserFS_conf
  \<Rightarrow> 'event list"
  where
    "F_PARSER_RTR__conf_get_annotation c \<equiv>
  F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c)"

lemma F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev: "
  F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word w v) = w"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t="case w of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last w]"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last w]"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac w')(*strict*)
  apply(rule_tac
      t="((\<lambda>(a, b). a) \<circ> (\<lambda>a. (a, [])))"
      and s="id"
      in ssubst)
   apply(rename_tac w')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w')(*strict*)
  apply(clarsimp)
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__rules_annotate_word_sound: "
  length w > 0
  \<Longrightarrow> snd (last (F_PARSER_RTR__rules_annotate_word w v)) = v"
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a w aa list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev: "
  w \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word w v) = v"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a w aa list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__rules_annotate_word_last: "
  (a, v) \<in> set (F_PARSER_RTR__rules_annotate_word (w @ [a]) v)"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rule conjI)
   apply(case_tac w)
    apply(clarsimp)
   apply(rename_tac aa list)(*strict*)
   apply(clarsimp)
  apply(rule disjI1)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_rev_distrib_append: "
  F_PARSER_RTR__rules_annotate_word_rev (w1 @ w2) = F_PARSER_RTR__rules_annotate_word_rev w1 @ F_PARSER_RTR__rules_annotate_word_rev w2"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
  done

lemma F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append: "
  v \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (w @ F_PARSER_RTR__rules_annotate_word v x) = x"
  apply(simp add: F_PARSER_RTR__word_get_annotation_def)
  apply(case_tac "F_PARSER_RTR__rules_annotate_word v x")
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(case_tac v)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(rule_tac
      t="last (w @ F_PARSER_RTR__rules_annotate_word v x)"
      and s="last(F_PARSER_RTR__rules_annotate_word v x)"
      in ssubst)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(fold F_PARSER_RTR__word_get_annotation_def)
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  done

lemma F_PARSER_RTR__rules_annotate_word_to_F_PARSER_RTR__rules_annotate_element: "
  map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) w = F_PARSER_RTR__rules_annotate_word w []"
  apply(induct w)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac a w)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_last_prime: "
  F_PARSER_RTR__rules_annotate_word (w @ [l]) a = (F_PARSER_RTR__rules_annotate_word w []) @ (F_PARSER_RTR__rules_annotate_word [l] a)"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac "w@[l]")
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(subgoal_tac "map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [l])) @ map (\<lambda>aa. F_PARSER_RTR__rules_annotate_element aa a) [last (w @ [l])] = map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [l])) @ map (\<lambda>aa. F_PARSER_RTR__rules_annotate_element aa a) [last (w @ [l])]")
   apply(rename_tac aa list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(rule_tac
      t="(case w @ [l] of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [l])) @ map (\<lambda>aa. F_PARSER_RTR__rules_annotate_element aa a) [last (w @ [l])])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [l])) @ map (\<lambda>aa. F_PARSER_RTR__rules_annotate_element aa a) [last (w @ [l])]"
      in ssubst)
   apply(rename_tac aa list)(*strict*)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(rule_tac
      t="(butlast (w @ [l]))"
      and s="w"
      in ssubst)
   apply(rename_tac aa list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac aa list)(*strict*)
  apply(rule_tac
      t="last(w@[l])"
      and s="l"
      in ssubst)
   apply(rename_tac aa list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac aa list)(*strict*)
  apply(fold F_PARSER_RTR__rules_annotate_word_def)
  apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(rule F_PARSER_RTR__rules_annotate_word_to_F_PARSER_RTR__rules_annotate_element)
  done

lemma F_PARSER_RTR__rules_annotate_word_Cons: "
  F_PARSER_RTR__rules_annotate_word (a # v) [] = (F_PARSER_RTR__rules_annotate_word [a] []) @ (F_PARSER_RTR__rules_annotate_word v [])"
  apply(induct v)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac aa v)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_append: "
  F_PARSER_RTR__rules_annotate_word (w @ v) [] = (F_PARSER_RTR__rules_annotate_word w []) @ (F_PARSER_RTR__rules_annotate_word v [])"
  apply(induct w arbitrary: v)
   apply(rename_tac v)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac a w v)(*strict*)
  apply(rule_tac
      t="(a#w)@v"
      and s="a#(w@v)"
      in ssubst)
   apply(rename_tac a w v)(*strict*)
   apply(force)
  apply(rename_tac a w v)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (a # (w @ v)) []"
      and s="F_PARSER_RTR__rules_annotate_word [a] [] @ (F_PARSER_RTR__rules_annotate_word (w@v) [])"
      in ssubst)
   apply(rename_tac a w v)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_Cons)
  apply(rename_tac a w v)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (a # w) []"
      and s="F_PARSER_RTR__rules_annotate_word [a] [] @ (F_PARSER_RTR__rules_annotate_word w [])"
      in ssubst)
   apply(rename_tac a w v)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_Cons)
  apply(rename_tac a w v)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_append_prime: "
  v \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (w @ v) x = (F_PARSER_RTR__rules_annotate_word w []) @ (F_PARSER_RTR__rules_annotate_word v x)"
  apply(induct v arbitrary: w rule: rev_induct)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa xs w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rule_tac
      t="(case w @ xs @ [xa] of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ xs @ [xa])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (w @ xs @ [xa])])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ xs @ [xa])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (w @ xs @ [xa])]"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply(case_tac "w@xs@[xa]")
    apply(rename_tac xa xs w)(*strict*)
    apply(force)
   apply(rename_tac xa xs w a list)(*strict*)
   apply(force)
  apply(rename_tac xa xs w)(*strict*)
  apply(rule_tac
      t="butlast (w @ xs @ [xa])"
      and s="w@xs"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply (metis butlast_snoc_2)
  apply(rename_tac xa xs w)(*strict*)
  apply(rule_tac
      t="last (w @ xs @ [xa])"
      and s="xa"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply (metis NotemptyString last_appendR last_snoc rotate_simps)
  apply(rename_tac xa xs w)(*strict*)
  apply(rule_tac
      t="case xs @ [xa] of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (xs @ [xa])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (xs @ [xa])]"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (xs @ [xa])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (xs @ [xa])]"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply(case_tac "xs@[xa]")
    apply(rename_tac xa xs w)(*strict*)
    apply(force)
   apply(rename_tac xa xs w a list)(*strict*)
   apply(force)
  apply(rename_tac xa xs w)(*strict*)
  apply(rule_tac
      t="butlast (xs @ [xa])"
      and s="xs"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply(force)
  apply(rename_tac xa xs w)(*strict*)
  apply(rule_tac
      t="[last (xs @ [xa])]"
      and s="[xa]"
      in ssubst)
   apply(rename_tac xa xs w)(*strict*)
   apply (metis last_snoc)
  apply(rename_tac xa xs w)(*strict*)
  apply(case_tac w)
   apply(rename_tac xa xs w)(*strict*)
   apply(force)
  apply(rename_tac xa xs w a list)(*strict*)
  apply(rule_tac
      t="case w of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last w]"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) w"
      in ssubst)
   apply(rename_tac xa xs w a list)(*strict*)
   apply(case_tac w)
    apply(rename_tac xa xs w a list)(*strict*)
    apply(force)
   apply(rename_tac xa xs w a list aa lista)(*strict*)
   apply(rule_tac
      t="(case w of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last w])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last w]"
      in ssubst)
    apply(rename_tac xa xs w a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac xa xs w a list aa lista)(*strict*)
   apply(rule_tac
      t="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last w]"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) ((butlast w) @ [last w])"
      in ssubst)
    apply(rename_tac xa xs w a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac xa xs w a list aa lista)(*strict*)
   apply(rule_tac
      t="butlast w @ [last w]"
      and s="w"
      in ssubst)
    apply(rename_tac xa xs w a list aa lista)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa xs w a list aa lista)(*strict*)
   apply(force)
  apply(rename_tac xa xs w a list)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_last_prime_prime: "
  F_PARSER_RTR__rules_annotate_word (w @ (v @ [l])) a = (F_PARSER_RTR__rules_annotate_word w []) @ (F_PARSER_RTR__rules_annotate_word (v @ [l]) a)"
  apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (v @ [l]) a"
      and s="(F_PARSER_RTR__rules_annotate_word v []) @ (F_PARSER_RTR__rules_annotate_word [l] a)"
      in ssubst)
   apply(rule F_PARSER_RTR__rules_annotate_word_last_prime)
  apply(rule_tac
      t="w@v@[l]"
      and s="(w@v)@[l]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word ((w @ v) @ [l]) a"
      and s="(F_PARSER_RTR__rules_annotate_word (w@v) []) @ (F_PARSER_RTR__rules_annotate_word [l] a)"
      in ssubst)
   apply(rule F_PARSER_RTR__rules_annotate_word_last_prime)
  apply(clarsimp)
  apply(rule F_PARSER_RTR__rules_annotate_word_append)
  done

lemma F_PARSER_RTR__rules_annotate_word_length: "
  length (F_PARSER_RTR__rules_annotate_word w v) = length w"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_inj1: "
  F_PARSER_RTR__rules_annotate_word w a = F_PARSER_RTR__rules_annotate_word v b
  \<Longrightarrow> w = v"
  apply(induct w arbitrary: v a b rule: rev_induct)
   apply(rename_tac v a b)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(rename_tac v b)(*strict*)
   apply(case_tac v)
    apply(rename_tac v b)(*strict*)
    apply(clarsimp)
   apply(rename_tac v b a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs v a b)(*strict*)
  apply(case_tac v)
   apply(rename_tac x xs v a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs a b)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(rename_tac x xs a)(*strict*)
   apply(case_tac "xs@[x]")
    apply(rename_tac x xs a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xs a aa list)(*strict*)
   apply(force)
  apply(rename_tac x xs v a b aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. v = w' @ [x']")
   apply(rename_tac x xs v a b aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xs v a b aa list)(*strict*)
  apply(thin_tac "v=aa#list")
  apply(clarsimp)
  apply(rename_tac x xs a b w' x')(*strict*)
  apply(subgoal_tac "(F_PARSER_RTR__rules_annotate_word xs []) @ (F_PARSER_RTR__rules_annotate_word [x] a) =(F_PARSER_RTR__rules_annotate_word w' []) @ (F_PARSER_RTR__rules_annotate_word [x'] a)")
   apply(rename_tac x xs a b w' x')(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR__rules_annotate_word_last_prime)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac x xs a b w' x')(*strict*)
  apply(erule_tac
      x="w'"
      in meta_allE)
  apply(erule_tac
      x="[]"
      in meta_allE)
  apply(erule_tac
      x="[]"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs a b w' x')(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
  apply(rename_tac x xs a b w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac x a b w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_inj2: "
  length w > 0
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word w a = F_PARSER_RTR__rules_annotate_word v b
  \<Longrightarrow> a = b"
  apply(subgoal_tac "w=v")
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac v)
   apply(force)
  apply(rename_tac aa list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_pair_prefix_hlp: "
  xa @ F_PARSER_RTR__rules_annotate_word ra X = xb @ F_PARSER_RTR__rules_annotate_word rb Y
  \<Longrightarrow> prefix xa xb
  \<Longrightarrow> \<exists>a b. a @ rb = b @ ra"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "length ra = length c + length rb")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule_tac
      t="length ra"
      and s="length (F_PARSER_RTR__rules_annotate_word ra X)"
      in subst)
    apply(rename_tac c)(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_length)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      t="length rb"
      and s="length (F_PARSER_RTR__rules_annotate_word rb Y)"
      in subst)
    apply(rename_tac c)(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_length)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word ra X"
      and s="c @ F_PARSER_RTR__rules_annotate_word rb Y"
      in ssubst)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "\<exists>ra1 ra2. ra=ra1@ra2 \<and> length ra1=length c \<and> length ra2=length rb")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule_tac
      x="take (length c) ra"
      in exI)
   apply(rule_tac
      x="drop (length c) ra"
      in exI)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ra1 ra2)(*strict*)
  apply(case_tac ra2)
   apply(rename_tac c ra1 ra2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ra1)(*strict*)
   apply(force)
  apply(rename_tac c ra1 ra2 a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ra2 = w' @ [x']")
   apply(rename_tac c ra1 ra2 a list)(*strict*)
   prefer 2
   apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac c ra1 ra2 a list)(*strict*)
  apply(thin_tac "ra2=a#list")
  apply(clarsimp)
  apply(rename_tac c ra1 w' x')(*strict*)
  apply(subgoal_tac "(F_PARSER_RTR__rules_annotate_word ra1) [] @ (F_PARSER_RTR__rules_annotate_word (w'@[x']) X) = c @ F_PARSER_RTR__rules_annotate_word rb Y")
   apply(rename_tac c ra1 w' x')(*strict*)
   prefer 2
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word ra1 [] @ F_PARSER_RTR__rules_annotate_word (w' @ [x']) X"
      and s="F_PARSER_RTR__rules_annotate_word (ra1 @ (w'@[x'])) X"
      in subst)
    apply(rename_tac c ra1 w' x')(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_last_prime_prime)
   apply(rename_tac c ra1 w' x')(*strict*)
   apply(force)
  apply(rename_tac c ra1 w' x')(*strict*)
  apply(thin_tac "F_PARSER_RTR__rules_annotate_word (ra1 @ w' @ [x']) X = c @ F_PARSER_RTR__rules_annotate_word rb Y")
  apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word ra1 [] = c")
   apply(rename_tac c ra1 w' x')(*strict*)
   prefer 2
   apply(rule length_append_equal)
    apply(rename_tac c ra1 w' x')(*strict*)
    apply(rule_tac
      t="length (F_PARSER_RTR__rules_annotate_word ra1 [])"
      and s="length ra1"
      in ssubst)
     apply(rename_tac c ra1 w' x')(*strict*)
     apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
    apply(rename_tac c ra1 w' x')(*strict*)
    apply(force)
   apply(rename_tac c ra1 w' x')(*strict*)
   apply(force)
  apply(rename_tac c ra1 w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac ra1 w' x')(*strict*)
  apply(subgoal_tac "w'@[x']=rb")
   apply(rename_tac ra1 w' x')(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(rename_tac ra1 w' x')(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_pair_prefix: "
  xa @ F_PARSER_RTR__rules_annotate_word ra X = xb @ F_PARSER_RTR__rules_annotate_word rb X
  \<Longrightarrow> \<exists>a b. a @ rb = b @ ra"
  apply(subgoal_tac "prefix xa xb \<or> prefix xb xa")
   apply(erule disjE)
    apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix_hlp)
     apply(force)
    apply(force)
   apply(subgoal_tac "\<exists>a b. a @ ra = b @ rb")
    apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(rule_tac
      x="b"
      in exI)
    apply(rule_tac
      x="a"
      in exI)
    apply(force)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix_hlp)
    apply(rule sym)
    apply(force)
   apply(force)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma last_F_PARSER_RTR__rules_annotate_word: "
  w \<noteq> []
  \<Longrightarrow> last (x @ F_PARSER_RTR__rules_annotate_word w v) = F_PARSER_RTR__rules_annotate_element (last w) v"
  apply(subgoal_tac "length (F_PARSER_RTR__rules_annotate_word w v) = length w")
   prefer 2
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
  apply(rule_tac
      t="last (x @ F_PARSER_RTR__rules_annotate_word w v)"
      and s="last (F_PARSER_RTR__rules_annotate_word w v)"
      in ssubst)
   apply(rule last_appendR)
   apply(force)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__rules_annotate_word_triv: "
  F_PARSER_RTR__rules_annotate_word w [] = map (\<lambda>x. (x, [])) w"
  apply(induct w)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a w aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a aa list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_length_prime: "
  F_PARSER_RTR__rules_annotate_word [] [] = []"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_preserves_set: "
  (a, b) \<in> set (F_PARSER_RTR__rules_annotate_word w v)
  \<Longrightarrow> a \<in> set w"
  apply(induct w)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac aa w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(erule disjE)
   apply(rename_tac aa w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(clarsimp)
  apply(rename_tac aa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa w aaa)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(clarsimp)
  apply(rename_tac aa w)(*strict*)
  apply(case_tac w)
   apply(rename_tac aa w)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa w aaa list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__rules_annotate_word_F_PARSER_RTR__rules_annotate_word_rev_annotation_empty: "
  (a, bb) \<in> set (F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w) [])
  \<Longrightarrow> [] = bb"
  apply(induct w rule: rev_induct)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa b xs)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
  apply(rename_tac aa xs)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_pullout: "
  w2 \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (w1 @ w2) X = F_PARSER_RTR__rules_annotate_word w1 [] @ F_PARSER_RTR__rules_annotate_word w2 X"
  apply(induct w2 rule: rev_induct)
   apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply (metis F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_last_prime_prime F_PARSER_RTR__rules_annotate_word_to_F_PARSER_RTR__rules_annotate_element F_PARSER_RTR__rules_annotate_word_triv butlast_snoc butlast_snoc_2 last_snoc map_append)
  done

lemma F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty: "
  x \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word x y) = y"
  apply(case_tac x)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. x = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "x=a#list")
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__word_get_annotation_def)
  apply(rule_tac
      t="(case x of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast x) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a y) [last x])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast x) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a y) [last x]"
      in ssubst)
   apply(case_tac x)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__word_get_annotation_not_empty: "
  x \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation x = F_PARSER_RTR__word_get_annotation (y @ x)"
  apply (metis List.last_append F_PARSER_RTR__word_get_annotation_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_pullout_prime: "
  F_PARSER_RTR__rules_annotate_word (w @ [f]) x = F_PARSER_RTR__rules_annotate_word w [] @ [F_PARSER_RTR__rules_annotate_element f x]"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rule_tac
      t="(case w @ [f] of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [f])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (w @ [f])])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w @ [f])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a x) [last (w @ [f])]"
      in ssubst)
   apply(case_tac "w@[f]")
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(fold F_PARSER_RTR__rules_annotate_word_def)
  apply(clarsimp)
  apply (metis F_PARSER_RTR__rules_annotate_word_to_F_PARSER_RTR__rules_annotate_element)
  done

lemma in_set_of_F_PARSER_RTR__rules_annotate_word: "
  f \<in> set w
  \<Longrightarrow> (f, []) \<in> set (F_PARSER_RTR__rules_annotate_word w [])"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(simp (no_asm) add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac w)
   apply(rename_tac a w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a w aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a w aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a w aa list)(*strict*)
  apply(thin_tac "w=aa#list")
  apply(clarsimp)
  apply(rename_tac a w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(clarsimp)
  done

lemma Annot_at_most_one: "
  w \<noteq> []
  \<Longrightarrow> length (snd (last (F_PARSER_RTR__rules_annotate_word w []))) \<le> Suc 0"
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac "w'@[x']")
   apply(rename_tac w' x')(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(subgoal_tac "length(snd(last(map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last (w' @ [x'])])))\<le> Suc 0")
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(rule_tac
      t="(case w' @ [x'] of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last (w' @ [x'])])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last (w' @ [x'])]"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "\<not> length (snd (last (case w' @ [x'] of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) [last (w' @ [x'])]))) \<le> Suc 0")
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "w' @ [x'] = a # list")
  apply(rule_tac
      t="butlast (w' @ [x'])"
      and s="w'"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(rule_tac
      t="last (w' @ [x'])"
      and s="x'"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma Annot_persists: "
  w \<noteq> []
  \<Longrightarrow> snd (last (F_PARSER_RTR__rules_annotate_word w v)) = v"
  apply(case_tac w)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(case_tac "w'@[x']")
   apply(rename_tac w' x')(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(subgoal_tac "snd (last (case w' @ [x'] of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last (w' @ [x'])])) = v")
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "snd (last (case w' @ [x'] of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last (w' @ [x'])])) \<noteq> v")
  apply(rename_tac w' x' a list)(*strict*)
  apply(rule_tac
      t="(case w' @ [x'] of [] \<Rightarrow> [] | a' # w'stack \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last (w' @ [x'])])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (w' @ [x'])) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v) [last (w' @ [x'])]"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "w' @ [x'] = a # list")
  apply(rule_tac
      t="butlast (w' @ [x'])"
      and s="w'"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(rule_tac
      t="last (w' @ [x'])"
      and s="x'"
      in ssubst)
   apply(rename_tac w' x' a list)(*strict*)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__rules_annotate_word_inj3: "
  w1 \<noteq> []
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word w1 v1 = F_PARSER_RTR__rules_annotate_word w2 v2
  \<Longrightarrow> v1 = v2"
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(subgoal_tac "map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w1) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v1) [last w1] =map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w2) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v2) [last w2] ")
   prefer 2
   apply(case_tac w1)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(case_tac w2)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list aa lista)(*strict*)
   apply(force)
  apply(thin_tac "(case w1 of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w1) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v1) [last w1]) = (case w2 of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w2) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v2) [last w2])")
  apply(subgoal_tac "map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v1) [last w1] =map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v2) [last w2]")
   prefer 2
   apply(force)
  apply(thin_tac " map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w1) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v1) [last w1] = map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast w2) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a v2) [last w2]")
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR__conf_annotate__rev_F_PARSER_RTR__conf_annotate_rev: "
  parserFS_conf_stack c \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__conf_annotate__rev (F_PARSER_RTR__conf_annotate c) = c"
  apply(simp add: F_PARSER_RTR__conf_annotate_def F_PARSER_RTR__conf_annotate__rev_def)
  apply(case_tac c)
  apply(rename_tac parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserFS_conf_fixed parserFS_conf_stack)(*strict*)
  apply(rule conjI)
   apply(rename_tac parserFS_conf_fixed parserFS_conf_stack)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  apply(rename_tac parserFS_conf_fixed parserFS_conf_stack)(*strict*)
  apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S1S1: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule_tac
      x="parserS_conf_scheduler c1"
      in exI)
  apply(rule_tac
      x="parserS_conf_scheduler c2"
      in exI)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S1S2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=[]")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra) = F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []")
    apply(rename_tac r ra)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra)"
      and s="last (xb@(F_PARSER_RTR__rules_annotate_word (rule_lpop ra) (rule_rpop ra)))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []"
      and s="last (x@(F_PARSER_RTR__rules_annotate_word (rule_lpop r) []))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S1R1: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac r ra w1 w2)(*strict*)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra w1 w2)(*strict*)
   apply(force)
  apply(rename_tac r ra w1 w2)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra w1 w2)(*strict*)
      apply(force)
     apply(rename_tac r ra w1 w2)(*strict*)
     apply(force)
    apply(rename_tac r ra w1 w2)(*strict*)
    apply(force)
   apply(rename_tac r ra w1 w2)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra w1 w2)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule_tac
      x="w2"
      in exI)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S1R2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=[]")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra) = F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []")
    apply(rename_tac r ra)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra)"
      and s="last (xb@(F_PARSER_RTR__rules_annotate_word (rule_lpop ra) (rule_rpop ra)))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []"
      and s="last (x@(F_PARSER_RTR__rules_annotate_word (rule_lpop r) []))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S2S2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=rule_rpop r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(case_tac "rule_lpop ra")
    apply(rename_tac r ra)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop ra= w' @ [x']")
    apply(rename_tac r ra a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra a list)(*strict*)
   apply(thin_tac "rule_lpop ra=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x')(*strict*)
   apply(case_tac "rule_lpop r")
    apply(rename_tac r ra w' x')(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop r= w' @ [x']")
    apply(rename_tac r ra w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(thin_tac "rule_lpop r=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(case_tac "w'@[x']")
    apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
   apply(clarsimp)
   apply(case_tac "w'stack@[x'stack]")
    apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list aa lista)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(case_tac c)
   apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
   apply(case_tac c1)
   apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
   apply(case_tac c2)
   apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
   apply(clarsimp)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S2R1: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop r=[]")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) (rule_rpop r) = F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) []")
    apply(rename_tac r ra)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) (rule_rpop r)"
      and s="last (x@(F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) []"
      and s="last (xb@(F_PARSER_RTR__rules_annotate_word (rule_lpop ra) []))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_S2R2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=rule_rpop r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(case_tac "rule_lpop ra")
    apply(rename_tac r ra)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop ra= w' @ [x']")
    apply(rename_tac r ra a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra a list)(*strict*)
   apply(thin_tac "rule_lpop ra=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x')(*strict*)
   apply(case_tac "rule_lpop r")
    apply(rename_tac r ra w' x')(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop r= w' @ [x']")
    apply(rename_tac r ra w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(thin_tac "rule_lpop r=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(case_tac "w'@[x']")
    apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
   apply(clarsimp)
   apply(case_tac "w'stack@[x'stack]")
    apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list aa lista)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_R1R1: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
    apply(force)
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   apply(force)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
    apply(force)
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   apply(force)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   apply(force)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
      apply(force)
     apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
     apply(force)
    apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
    apply(force)
   apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra parserS_conf_schedulera parserS_conf_schedulerb)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac r ra w1 w2)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule_tac
      x="w2"
      in exI)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_R1R2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=[]")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra) = F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []")
    apply(rename_tac r ra)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop ra)) (rule_rpop ra)"
      and s="last (xb@(F_PARSER_RTR__rules_annotate_word (rule_lpop ra) (rule_rpop ra)))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_element (last (rule_lpop r)) []"
      and s="last (x@(F_PARSER_RTR__rules_annotate_word (rule_lpop r) []))"
      in subst)
     apply(rename_tac r ra)(*strict*)
     apply(rule last_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser_R2R2: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic P
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> xb @ rule_lpop e2 = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c1 = x @ rule_lpush e1
  \<Longrightarrow> rule_rpop e2 @ xc = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c1 = rule_rpush e1 @ xa
  \<Longrightarrow> parserS_conf_stack c = x @ rule_lpop e1
  \<Longrightarrow> parserS_conf_stack c2 = xb @ rule_lpush e2
  \<Longrightarrow> parserS_conf_scheduler c = rule_rpop e1 @ xa
  \<Longrightarrow> parserS_conf_scheduler c2 = rule_rpush e2 @ xc
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more)(*strict*)
  apply(case_tac c1)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea)(*strict*)
  apply(case_tac c2)
  apply(rename_tac r ra parserS_conf_stacka parserS_conf_schedulera more parserS_conf_stackaa parserS_conf_scheduleraa morea parserS_conf_stackb parserS_conf_schedulerb moreb)(*strict*)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P ra")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "rule_rpop ra=rule_rpop r")
   apply(rename_tac r ra)(*strict*)
   prefer 2
   apply(case_tac "rule_lpop ra")
    apply(rename_tac r ra)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop ra= w' @ [x']")
    apply(rename_tac r ra a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra a list)(*strict*)
   apply(thin_tac "rule_lpop ra=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x')(*strict*)
   apply(case_tac "rule_lpop r")
    apply(rename_tac r ra w' x')(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop r= w' @ [x']")
    apply(rename_tac r ra w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r ra w' x' a list)(*strict*)
   apply(thin_tac "rule_lpop r=a#list")
   apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(case_tac "w'@[x']")
    apply(rename_tac r ra w' x' w'stack x'stack)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
   apply(clarsimp)
   apply(case_tac "w'stack@[x'stack]")
    apply(rename_tac r ra w' x' w'stack x'stack a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac r ra w' x' w'stack x'stack a list aa lista)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac r ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "r=ra")
   apply(rename_tac r ra)(*strict*)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(rule PARSER_use_FEdeterm)
      apply(rename_tac r ra)(*strict*)
      apply(force)
     apply(rename_tac r ra)(*strict*)
     apply(force)
    apply(rename_tac r ra)(*strict*)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pair_prefix)
   apply(force)
  apply(rename_tac r ra)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_makesTopFreeParser: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_deterministic P
  \<Longrightarrow> P' = F_PARSER_RTR P
  \<Longrightarrow> parserS.is_forward_deterministic P'"
  apply(simp (no_asm) add: parserS.is_forward_deterministic_def)
  apply(rule conjI)
   apply(simp add: parserS.is_forward_target_deterministic_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e)(*strict*)
   apply(simp add: parserS_step_relation_def F_PARSER_RTR_def)
   apply(clarsimp)
  apply(simp add: parserS.is_forward_edge_deterministic_def)
  apply(subgoal_tac "parserS.is_forward_edge_deterministic P")
   prefer 2
   apply(simp add: parserS.is_forward_deterministic_def)
  apply(thin_tac "parserS.is_forward_deterministic P")
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: parserS_step_relation_def F_PARSER_RTR_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(simp add: Let_def)
  apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_shift_new_observed P"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S1S1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S1S2)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S1R1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule F_PARSER_RTR_makesTopFreeParser_S1R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_new_observed P"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule sym)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S1S2)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
           apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
           apply(rule sym)
           apply(force)+
         apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
         apply(rule sym)
         apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule sym)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S1R1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
           apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
           apply(rule sym)
           apply(force)+
         apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
         apply(rule sym)
         apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule sym)
   apply(rule F_PARSER_RTR_makesTopFreeParser_S1R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
          apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
          apply(rule sym)
          apply(force)+
        apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
        apply(rule sym)
        apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_shift_old_observed P"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S2S2)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S2R1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule F_PARSER_RTR_makesTopFreeParser_S2R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_old_observed P"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule sym)
    apply(rule F_PARSER_RTR_makesTopFreeParser_S2R1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
           apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
           apply(rule sym)
           apply(force)+
         apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
         apply(rule sym)
         apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule sym)
   apply(rule F_PARSER_RTR_makesTopFreeParser_S2R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
          apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
          apply(rule sym)
          apply(force)+
        apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
        apply(rule sym)
        apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_reduce_old_observe P"
      in disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
    apply(rule F_PARSER_RTR_makesTopFreeParser_R1R1)
               apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
               apply(force)+
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule F_PARSER_RTR_makesTopFreeParser_R1R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(erule disjE)
   apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
   apply(rule sym)
   apply(rule F_PARSER_RTR_makesTopFreeParser_R1R2)
              apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
              apply(force)+
          apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
          apply(rule sym)
          apply(force)+
        apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
        apply(rule sym)
        apply(force)+
  apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
  apply(rule F_PARSER_RTR_makesTopFreeParser_R2R2)
             apply(rename_tac c c1 c2 e1 e2 x xa xb xc)(*strict*)
             apply(force)+
  done

theorem F_PARSER_RTR_makes_parser_no_top_rules: "
  P' = F_PARSER_RTR P
  \<Longrightarrow> parser_no_top_rules P'"
  apply(simp add: parser_no_top_rules_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  done

lemma F_PARSER_RTR__rules_shift_new_observed_finite: "
  valid_parser P
  \<Longrightarrow> finite (F_PARSER_RTR__rules_shift_new_observed P)"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(rule_tac
      B="{\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) ([]), rule_rpush = []\<rparr> | r. r \<in> parser_rules P}"
      in finite_subset)
   apply(force)
  apply(rule finite_image_set)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_RTR__rules_shift_old_observed_finite: "
  valid_parser P
  \<Longrightarrow> finite (F_PARSER_RTR__rules_shift_old_observed P)"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(rule_tac
      B=" {\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) [], rule_rpush = []\<rparr> | r. r \<in> parser_rules P}"
      in finite_subset)
   apply(force)
  apply(rule finite_image_set)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_RTR__rules_reduce_old_observe_finite: "
  valid_parser P
  \<Longrightarrow> finite (F_PARSER_RTR__rules_reduce_old_observe P)"
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(rule_tac
      B="{\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr> | r. r \<in> parser_rules P}"
      in finite_subset)
   apply(force)
  apply(rule finite_image_set)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_RTR__rules_reduce_new_observe_finite: "
  valid_parser P
  \<Longrightarrow> finite (F_PARSER_RTR__rules_reduce_new_observe P)"
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(rule_tac
      B="{\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr> | r. r \<in> parser_rules P}"
      in finite_subset)
   apply(force)
  apply(rule finite_image_set)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_RTR_valid_parser_step_label_S1: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_shift_new_observed P
  \<Longrightarrow> valid_parser_step_label (F_PARSER_RTR P) e"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(subgoal_tac "ra=r")
    apply(rename_tac r k w ra)(*strict*)
    prefer 2
    apply(case_tac r)
    apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(case_tac ra)
    apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
    apply(rule conjI)
     apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
     apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
     apply(rule sym)
     apply(force)
    apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(rule sym)
    apply(force)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(rule_tac
      x="k"
      in exI)
    apply(rule inMap)
    apply(rule_tac
      x="(w @ [parser_bottom P])"
      in bexI)
     apply(rename_tac r k w)(*strict*)
     apply(force)
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
    apply(rename_tac r k w a b)(*strict*)
    apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) ([]), rule_rpush = []\<rparr>"
      in bexI)
     apply(rename_tac r k w a b)(*strict*)
     apply(force)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
    apply(rename_tac r k w a b)(*strict*)
    apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) ([]), rule_rpush = []\<rparr>"
      in bexI)
     apply(rename_tac r k w a b)(*strict*)
     apply(force)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(case_tac "rule_lpop r")
     apply(rename_tac r k w)(*strict*)
     apply(clarsimp)
    apply(rename_tac r k w a list)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(rename_tac r k w)(*strict*)
   apply(case_tac "rule_lpush r")
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
   apply(rename_tac r k w a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(case_tac "rule_lpop r")
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_lpop r = w' @ [x']")
   apply(rename_tac r k w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac r k w a list)(*strict*)
  apply(thin_tac "rule_lpop r=a#list")
  apply(clarsimp)
  apply(rename_tac r k w w' x')(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w w' x')(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w w' x')(*strict*)
    apply(force)
   apply(rename_tac r k w w' x')(*strict*)
   apply(force)
  apply(rename_tac r k w w' x')(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(subgoal_tac "False")
   apply(rename_tac r k w w' x')(*strict*)
   apply(force)
  apply(rename_tac r k w w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac r k w w' x' ra)(*strict*)
  apply(case_tac r)
  apply(rename_tac r k w w' x' ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac ra)
  apply(rename_tac r k w w' x' ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w' x' rule_lpush rule_lpopa rule_lpusha)(*strict*)
  apply(rename_tac w1 w2 w3)
  apply(rename_tac k w w' x' w1 w2 w3)(*strict*)
  apply(subgoal_tac "w1=w3")
   apply(rename_tac k w w' x' w1 w2 w3)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(rename_tac k w w' x' w1 w2 w3)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w' x' w2 w3)(*strict*)
  apply(subgoal_tac "w2=w'@[x']")
   apply(rename_tac k w w' x' w2 w3)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(rename_tac k w w' x' w2 w3)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w' x' w3)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = w' @ [x'], rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w3, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      and A="parser_rules P"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
   apply(rename_tac k w w' x' w3)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w w' x' w3)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>rule_lpop = w' @ [x'], rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w3, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      and A="parser_rules P"
      and P="\<lambda>x. rule_rpop x \<noteq> []"
      in ballE)
   apply(rename_tac k w w' x' w3)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w w' x' w3)(*strict*)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac k w w' x' w3)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "[]=take k w")
    apply(rename_tac k w w' x' w3)(*strict*)
    apply(case_tac w)
     apply(rename_tac k w w' x' w3)(*strict*)
     apply(force)
    apply(rename_tac k w w' x' w3 a list)(*strict*)
    apply(case_tac k)
     apply(rename_tac k w w' x' w3 a list)(*strict*)
     apply(force)
    apply(rename_tac k w w' x' w3 a list nat)(*strict*)
    apply(force)
   apply(rename_tac k w w' x' w3)(*strict*)
   apply (metis F_PARSER_RTR__rules_annotate_word_inj3)
  apply(rename_tac k w w' x' w3 nat)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_valid_parser_step_label_S2: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_shift_old_observed P
  \<Longrightarrow> valid_parser_step_label (F_PARSER_RTR P) e"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = []")
    apply(rename_tac r k w ra)(*strict*)
    prefer 2
    apply(rule_tac
      w="rule_lpush r"
      in F_PARSER_RTR__rules_annotate_word_inj2)
     apply(rename_tac r k w ra)(*strict*)
     apply(force)
    apply(rename_tac r k w ra)(*strict*)
    apply(force)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(subgoal_tac "ra=r")
    apply(rename_tac r k w ra)(*strict*)
    prefer 2
    apply(case_tac r)
    apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(case_tac ra)
    apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_rpopa rule_lpusha)(*strict*)
    apply(rename_tac w1 w2 w3 w4 w5)
    apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
    apply(subgoal_tac "w3=w1")
     apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
     apply(force)
    apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w w1 w2 w4 w5)(*strict*)
    apply(subgoal_tac "w2=w5")
     apply(rename_tac k w w1 w2 w4 w5)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
     apply(force)
    apply(rename_tac k w w1 w2 w4 w5)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w w1 w4 w5)(*strict*)
    apply(subgoal_tac "w4=kPrefix k (w @ [parser_bottom P])")
     apply(rename_tac k w w1 w4 w5)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule_tac
      w="w1"
      in F_PARSER_RTR__rules_annotate_word_inj2)
      apply(rename_tac k w w1 w4 w5)(*strict*)
      apply(force)
     apply(rename_tac k w w1 w4 w5)(*strict*)
     apply(force)
    apply(rename_tac k w w1 w4 w5)(*strict*)
    apply(force)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule inMap)
    apply(rule_tac
      x="(w @ [parser_bottom P])"
      in bexI)
     apply(rename_tac r k w)(*strict*)
     apply(simp add: kPrefix_def)
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
    apply(rename_tac r k w a b)(*strict*)
    apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) ([]), rule_rpush = []\<rparr>"
      in bexI)
     apply(rename_tac r k w a b)(*strict*)
     apply(force)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
    apply(rename_tac r k w a b)(*strict*)
    apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) ([]), rule_rpush = []\<rparr>"
      in bexI)
     apply(rename_tac r k w a b)(*strict*)
     apply(force)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac r k w)(*strict*)
    apply(case_tac "rule_lpop r")
     apply(rename_tac r k w)(*strict*)
     apply(clarsimp)
    apply(rename_tac r k w a list)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(rename_tac r k w)(*strict*)
   apply(case_tac "rule_lpush r")
    apply(rename_tac r k w)(*strict*)
    apply(clarsimp)
   apply(rename_tac r k w a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(subgoal_tac "w1=w3")
    apply(rename_tac k w w1 w2 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w2 w3 w4)(*strict*)
   apply(subgoal_tac "w2=w4")
    apply(rename_tac k w w2 w3 w4)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = []")
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(rule_tac
      w="rule_lpush r"
      in F_PARSER_RTR__rules_annotate_word_inj2)
     apply(rename_tac k w w3 w4)(*strict*)
     apply(force)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = [], rule_lpush = w4, rule_rpush = []\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(subgoal_tac "False")
   apply(rename_tac r k w)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(clarsimp)
  apply(rename_tac r k w ra)(*strict*)
  apply(case_tac r)
  apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac ra)
  apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_rpopa rule_lpusha)(*strict*)
  apply(rename_tac w1 w2 w3 w4 w5)
  apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
  apply(subgoal_tac "w1=w3")
   apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w2 w3 w4 w5)(*strict*)
  apply(subgoal_tac "w2=w5")
   apply(rename_tac k w w2 w3 w4 w5)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
   apply(force)
  apply(rename_tac k w w2 w3 w4 w5)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w3 w4 w5)(*strict*)
  apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = w4")
   apply(rename_tac k w w3 w4 w5)(*strict*)
   prefer 2
   apply(rule_tac
      w="w3"
      in F_PARSER_RTR__rules_annotate_word_inj2)
    apply(rename_tac k w w3 w4 w5)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4 w5)(*strict*)
   apply(force)
  apply(rename_tac k w w3 w4 w5)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w w3 w5)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
   apply(rename_tac k w w3 w5)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w w3 w5)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      and P="\<lambda>x. rule_rpop x \<noteq> []"
      in ballE)
   apply(rename_tac k w w3 w5)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w w3 w5)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      in ballE)
   apply(rename_tac k w w3 w5)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w w3 w5)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "kPrefix k (w @ [parser_bottom P])=[]")
   apply(rename_tac k w w3 w5)(*strict*)
   prefer 2
   apply (metis F_PARSER_RTR__rules_annotate_word_inj3)
  apply(rename_tac k w w3 w5)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_valid_parser_step_label_R1: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> parser_not_observes_input_terminator P
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_reduce_old_observe P
  \<Longrightarrow> valid_parser_step_label (F_PARSER_RTR P) e"
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(subgoal_tac "w2=w4")
    apply(rename_tac k w w1 w2 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(subgoal_tac "w1=w3")
    apply(rename_tac k w w1 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = []\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = []\<rparr>"
      and P="\<lambda>x. rule_rpop x \<noteq> []"
      in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = []\<rparr>"
      and P="\<lambda>x. length (rule_rpop x) \<le> Suc 0"
      in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P])=[]")
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply (metis F_PARSER_RTR__rules_annotate_word_inj3)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(clarsimp)
  apply(rename_tac r k w ra)(*strict*)
  apply(subgoal_tac "ra=r")
   apply(rename_tac r k w ra)(*strict*)
   prefer 2
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(subgoal_tac "w3=w1")
    apply(rename_tac k w w1 w2 w3 w4)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w2 w4)(*strict*)
   apply(subgoal_tac "w2=w4")
    apply(rename_tac k w w1 w2 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w4)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w ra)(*strict*)
  apply(clarify)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(rule_tac
      x="k"
      in exI)
   apply(rule inMap)
   apply(rule_tac
      x="(w @ [parser_bottom P])"
      in bexI)
    apply(rename_tac r k w ra)(*strict*)
    apply(force)
   apply(rename_tac r k w ra)(*strict*)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w a b)(*strict*)
   apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr>"
      in bexI)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w a b)(*strict*)
   apply(clarify)
   apply(rule_tac
      x="r"
      in exI)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w a b)(*strict*)
   apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) [], rule_rpop = rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr>"
      in bexI)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w a b)(*strict*)
   apply(clarify)
   apply(rule_tac
      x="r"
      in exI)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac "rule_lpop r")
    apply(rename_tac r k w ra)(*strict*)
    apply(clarsimp)
   apply(rename_tac r k w ra a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
   apply(rename_tac r k w a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac r k w ra)(*strict*)
  apply(case_tac "rule_lpush r")
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w ra a list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
  apply(rename_tac r k w a list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(simp add: parser_not_observes_input_terminator_def)
  apply(clarsimp)
  apply(rename_tac r k w a list x)(*strict*)
  apply(erule_tac
      x="r"
      and P="\<lambda>r. parser_bottom P \<notin> set (rule_rpush r)"
      in ballE)
   apply(rename_tac r k w a list x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r k w a list x)(*strict*)
  apply(erule_tac
      x="r"
      and P="\<lambda>r. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r"
      in ballE)
   apply(rename_tac r k w a list x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r k w a list x)(*strict*)
  apply(erule_tac
      x="r"
      and P="\<lambda>r. rule_rpop r \<noteq> []"
      in ballE)
   apply(rename_tac r k w a list x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r k w a list x)(*strict*)
  apply(erule_tac
      x="r"
      in ballE)
   apply(rename_tac r k w a list x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r k w a list x)(*strict*)
  apply(clarsimp)
  apply (metis List.last_in_set snoc_eq_iff_butlast)
  done

lemma F_PARSER_RTR_valid_parser_step_label_R2: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_reduce_new_observe P
  \<Longrightarrow> valid_parser_step_label (F_PARSER_RTR P) e"
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P r")
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac r)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(subgoal_tac "w2=w4")
    apply(rename_tac k w w1 w2 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(subgoal_tac "w1=w3")
    apply(rename_tac k w w1 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = []")
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(subgoal_tac "\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = []\<rparr> = \<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>")
     apply(rename_tac k w w3 w4)(*strict*)
     apply(force)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(rule PARSER_use_FEdeterm)
        apply(rename_tac k w w3 w4)(*strict*)
        apply(force)
       apply(rename_tac k w w3 w4)(*strict*)
       apply(force)
      apply(rename_tac k w w3 w4)(*strict*)
      apply(force)
     apply(rename_tac k w w3 w4)(*strict*)
     apply(force)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w4, rule_rpush = kPrefix k (w @ [parser_bottom P])\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_rpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4 w5)
   apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
   apply(subgoal_tac "w2=w5")
    apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w3 w4 w5)(*strict*)
   apply(subgoal_tac "w1=w3")
    apply(rename_tac k w w1 w3 w4 w5)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w3 w4 w5)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w4 w5)(*strict*)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = w4")
    apply(rename_tac k w w3 w4 w5)(*strict*)
    prefer 2
    apply(rule_tac
      w="w3"
      in F_PARSER_RTR__rules_annotate_word_inj2)
     apply(rename_tac k w w3 w4 w5)(*strict*)
     apply(force)
    apply(rename_tac k w w3 w4 w5)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4 w5)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w5)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = []\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac k w w3 w5)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w5)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = []\<rparr>"
      and P="\<lambda>x. rule_rpop x \<noteq> []"
      in ballE)
    apply(rename_tac k w w3 w5)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w5)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = w3, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = w5, rule_rpush = []\<rparr>"
      in ballE)
    apply(rename_tac k w w3 w5)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k w w3 w5)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P])=[]")
    apply(rename_tac k w w3 w5)(*strict*)
    prefer 2
    apply (metis F_PARSER_RTR__rules_annotate_word_inj3)
   apply(rename_tac k w w3 w5)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(subgoal_tac "False")
    apply(rename_tac r k w)(*strict*)
    apply(force)
   apply(rename_tac r k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(subgoal_tac "w2=w4")
    apply(rename_tac k w w1 w2 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(subgoal_tac "w1=w3")
    apply(rename_tac k w w1 w3 w4)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w3 w4)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom P]) = []")
    apply(rename_tac k w w3 w4)(*strict*)
    prefer 2
    apply(rule_tac
      w="w3"
      in F_PARSER_RTR__rules_annotate_word_inj2)
     apply(rename_tac k w w3 w4)(*strict*)
     apply(force)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(clarsimp)
   apply(erule_tac x="\<lparr>rule_lpop = w3, rule_rpop = [], rule_lpush = w4, rule_rpush = []\<rparr>" and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"in ballE)
    apply(rename_tac k w w3 w4)(*strict*)
    apply(force)
   apply(rename_tac k w w3 w4)(*strict*)
   apply(force)
  apply(rename_tac r k w)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r k w ra)(*strict*)
  apply(subgoal_tac "ra=r")
   apply(rename_tac r k w ra)(*strict*)
   prefer 2
   apply(case_tac r)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac ra)
   apply(rename_tac r k w ra rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w rule_lpop rule_lpush rule_lpopa rule_rpopa rule_lpusha)(*strict*)
   apply(rename_tac w1 w2 w3 w4 w5)
   apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
   apply(subgoal_tac "w3=w1")
    apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w3 w4 w5)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w2 w4 w5)(*strict*)
   apply(subgoal_tac "w2=w5")
    apply(rename_tac k w w1 w2 w4 w5)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_inj1)
    apply(force)
   apply(rename_tac k w w1 w2 w4 w5)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w w1 w4 w5)(*strict*)
   apply(rule_tac
      w="w1"
      in F_PARSER_RTR__rules_annotate_word_inj2)
    apply(rename_tac k w w1 w4 w5)(*strict*)
    apply(force)
   apply(rename_tac k w w1 w4 w5)(*strict*)
   apply(rule sym)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(clarify)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule inMap)
   apply(rule_tac
      x="(w @ [parser_bottom P])"
      in bexI)
    apply(rename_tac r k w ra)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac r k w ra)(*strict*)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w a b)(*strict*)
   apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr>"
      in bexI)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w a b)(*strict*)
   apply(clarify)
   apply(rule_tac
      x="r"
      in exI)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac r k w a b)(*strict*)
   apply(rule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r), rule_rpop = [], rule_lpush = F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r), rule_rpush = []\<rparr>"
      in bexI)
    apply(rename_tac r k w a b)(*strict*)
    apply(force)
   apply(rename_tac r k w a b)(*strict*)
   apply(clarify)
   apply(rule_tac
      x="r"
      in exI)
   apply(force)
  apply(rename_tac r k w ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac r k w ra)(*strict*)
   apply(case_tac "rule_lpop r")
    apply(rename_tac r k w ra)(*strict*)
    apply(clarsimp)
   apply(rename_tac r k w ra a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
   apply(rename_tac r k w a list)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rename_tac r k w ra)(*strict*)
  apply(case_tac "rule_lpush r")
   apply(rename_tac r k w ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac r k w ra a list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_length)
  apply(rename_tac r k w a list)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  done

definition F_PARSER_RTR_input :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_RTR_input P \<equiv>
  valid_bounded_parser P (Suc 0)
  \<and> (\<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r)
  \<and> (\<forall>r \<in> parser_rules P. rule_rpop r \<noteq> [])
  \<and> parser_not_observes_input_terminator P
  \<and> parserS.is_forward_edge_deterministic_accessible P"

lemma F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_configurations: "
  F_PARSER_RTR_input G1
  \<Longrightarrow> parserFS_conf_fixed c = []
  \<Longrightarrow> parserFS_conf_stack c \<noteq> []
  \<Longrightarrow> (parser_bottom G1 \<in> set (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c)) \<longrightarrow> parserFS_conf_scheduler c = [])
  \<Longrightarrow> c \<in> parserFS_configurations (F_PARSER_RTR G1)
  \<Longrightarrow> F_PARSER_RTR__conf_annotate__rev c \<in> parserFS_configurations G1"
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
  apply(rule conjI)
   apply(rename_tac l r)(*strict*)
   apply(thin_tac "parser_bottom G1 \<in> set (F_PARSER_RTR__word_get_annotation l) \<longrightarrow> r = []")
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(clarsimp)
   apply(rename_tac l r a b)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(subgoal_tac "(a,b) \<in> parser_nonterms (let R = F_PARSER_RTR__rules_shift_new_observed G1 \<union> F_PARSER_RTR__rules_shift_old_observed G1 \<union> F_PARSER_RTR__rules_reduce_old_observe G1 \<union> F_PARSER_RTR__rules_reduce_new_observe G1; N = insert (F_PARSER_RTR__rules_annotate_element (parser_initial G1) []) {n. \<exists>r \<in> R. n \<in> set (rule_lpop r) \<or> n \<in> set (rule_lpush r)} in \<lparr>parser_nonterms = N, parser_events = parser_events G1, parser_initial = F_PARSER_RTR__rules_annotate_element (parser_initial G1) [], parser_marking = N \<inter> (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) ` parser_marking G1, parser_rules = R, parser_marker = Map.empty, parser_bottom = parser_bottom G1\<rparr>)")
    apply(rename_tac l r a b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac l r a b)(*strict*)
   apply(thin_tac "set l \<subseteq> parser_nonterms (let R = F_PARSER_RTR__rules_shift_new_observed G1 \<union> F_PARSER_RTR__rules_shift_old_observed G1 \<union> F_PARSER_RTR__rules_reduce_old_observe G1 \<union> F_PARSER_RTR__rules_reduce_new_observe G1; N = insert (F_PARSER_RTR__rules_annotate_element (parser_initial G1) []) {n. \<exists>r \<in> R. n \<in> set (rule_lpop r) \<or> n \<in> set (rule_lpush r)} in \<lparr>parser_nonterms = N, parser_events = parser_events G1, parser_initial = F_PARSER_RTR__rules_annotate_element (parser_initial G1) [], parser_marking = N \<inter> (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) ` parser_marking G1, parser_rules = R, parser_marker = Map.empty, parser_bottom = parser_bottom G1\<rparr>)")
   apply(rename_tac l r a b)(*strict*)
   apply(thin_tac "(a, b) \<in> set l")
   apply(simp add: Let_def)
   apply(erule disjE)
    apply(rename_tac l r a b)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(rename_tac l r a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac l r a b ra)(*strict*)
   apply(erule_tac
      P="ra \<in> F_PARSER_RTR__rules_shift_new_observed G1"
      in disjE)
    apply(rename_tac l r a b ra)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb)(*strict*)
    apply(erule disjE)
     apply(rename_tac l r a b rb)(*strict*)
     apply(rule_tac
      A="set (rule_lpop rb)"
      in set_mp)
      apply(rename_tac l r a b rb)(*strict*)
      prefer 2
      apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
      apply(force)
     apply(rename_tac l r a b rb)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
      apply(rename_tac l r a b rb x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x k w)(*strict*)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(rule_tac
      A="set (rule_lpush rb)"
      in set_mp)
     apply(rename_tac l r a b rb)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
     apply(rename_tac l r a b rb x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x k w)(*strict*)
    apply(force)
   apply(rename_tac l r a b ra)(*strict*)
   apply(erule_tac
      P="ra \<in> F_PARSER_RTR__rules_shift_old_observed G1"
      in disjE)
    apply(rename_tac l r a b ra)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb)(*strict*)
    apply(erule disjE)
     apply(rename_tac l r a b rb)(*strict*)
     apply(rule_tac
      A="set (rule_lpop rb)"
      in set_mp)
      apply(rename_tac l r a b rb)(*strict*)
      prefer 2
      apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
      apply(force)
     apply(rename_tac l r a b rb)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
      apply(rename_tac l r a b rb x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x k w)(*strict*)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(rule_tac
      A="set (rule_lpush rb)"
      in set_mp)
     apply(rename_tac l r a b rb)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
     apply(rename_tac l r a b rb x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x k w)(*strict*)
    apply(force)
   apply(rename_tac l r a b ra)(*strict*)
   apply(erule_tac
      P="ra \<in> F_PARSER_RTR__rules_reduce_old_observe G1"
      in disjE)
    apply(rename_tac l r a b ra)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb)(*strict*)
    apply(erule disjE)
     apply(rename_tac l r a b rb)(*strict*)
     apply(rule_tac
      A="set (rule_lpop rb)"
      in set_mp)
      apply(rename_tac l r a b rb)(*strict*)
      prefer 2
      apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
      apply(force)
     apply(rename_tac l r a b rb)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
      apply(rename_tac l r a b rb x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac l r a b rb x)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac l r a b rb x k w)(*strict*)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(rule_tac
      A="set (rule_lpush rb)"
      in set_mp)
     apply(rename_tac l r a b rb)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
     apply(rename_tac l r a b rb x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x k w)(*strict*)
    apply(force)
   apply(rename_tac l r a b ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
   apply(rename_tac l r a b rb)(*strict*)
   apply(erule disjE)
    apply(rename_tac l r a b rb)(*strict*)
    apply(rule_tac
      A="set (rule_lpop rb)"
      in set_mp)
     apply(rename_tac l r a b rb)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
     apply(force)
    apply(rename_tac l r a b rb)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
     apply(rename_tac l r a b rb x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac l r a b rb x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac l r a b rb x k w)(*strict*)
    apply(force)
   apply(rename_tac l r a b rb)(*strict*)
   apply(rule_tac
      A="set (rule_lpush rb)"
      in set_mp)
    apply(rename_tac l r a b rb)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_preserves_set)
    apply(force)
   apply(rename_tac l r a b rb)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(clarsimp)
   apply(rename_tac l r a b rb x)(*strict*)
   apply(erule_tac
      x="rb"
      and P="\<lambda>rb. valid_parser_step_label G1 rb"
      in ballE)
    apply(rename_tac l r a b rb x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac l r a b rb x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac l r a b rb x k w)(*strict*)
   apply(force)
  apply(rename_tac l r)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac l r)(*strict*)
   prefer 2
   apply(rule context_conjI)
    apply(rename_tac l r)(*strict*)
    apply(simp add: dom_abbreviation)
    apply(clarsimp)
    apply(rename_tac l v vb c ve ca)(*strict*)
    apply(rule_tac
      x="vb @ [parser_bottom (F_PARSER_RTR G1)]"
      in exI)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac l r)(*strict*)
   apply(thin_tac "r \<in> parser_unfixed_schedulers (F_PARSER_RTR G1)")
   apply(thin_tac "[] \<in> parser_fixed_schedulers (F_PARSER_RTR G1)")
   apply(thin_tac "set l \<subseteq> parser_nonterms (F_PARSER_RTR G1)")
   apply(thin_tac "r \<in> parser_unfixed_schedulers G1")
   apply(simp add: dom_abbreviation)
   apply(erule exE)+
   apply(rename_tac l r v va)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac l r v va vb c)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="F_PARSER_RTR__word_get_annotation l @ v"
      in exI)
   apply(clarsimp)
   apply(rename_tac l v vb c)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(rule_tac
      B="set(vb @ [parser_bottom G1])"
      in subset_trans)
    apply(rename_tac l v vb c)(*strict*)
    apply (metis set_append1)
   apply(rename_tac l v vb c)(*strict*)
   apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(thin_tac "parser_bottom G1 \<in> set (F_PARSER_RTR__word_get_annotation l) \<longrightarrow> r = []")
  apply(thin_tac "[] \<in> parser_fixed_schedulers (F_PARSER_RTR G1)")
  apply(thin_tac "r \<in> parser_unfixed_schedulers (F_PARSER_RTR G1)")
  apply(thin_tac "r \<in> parser_schedulers (F_PARSER_RTR G1)")
  apply(simp add: F_PARSER_RTR_def Let_def valid_parser_def F_PARSER_RTR__word_get_annotation_def)
  apply(rename_tac l)(*strict*)
  apply(case_tac l)
   apply(rename_tac l)(*strict*)
   apply(clarsimp)
  apply(rename_tac l a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. l = w' @ [x']")
   apply(rename_tac l a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac l a list)(*strict*)
  apply(thin_tac "l=a#list")
  apply(clarsimp)
  apply(rename_tac w' a b)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' a b)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(simp add: parser_fixed_schedulers_def)
   apply(simp add: parser_schedulers_def)
   apply(simp add: prefix_closure_def prefix_def)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac w' a b)(*strict*)
  apply(thin_tac "set w' \<subseteq> insert (F_PARSER_RTR__rules_annotate_element (parser_initial G1) []) {n. \<exists>r \<in> F_PARSER_RTR__rules_shift_new_observed G1 \<union> F_PARSER_RTR__rules_shift_old_observed G1 \<union> F_PARSER_RTR__rules_reduce_old_observe G1 \<union> F_PARSER_RTR__rules_reduce_new_observe G1. n \<in> set (rule_lpop r) \<or> n \<in> set (rule_lpush r)}")
  apply(rename_tac w' a b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b r)(*strict*)
  apply(erule_tac
      P="r \<in> F_PARSER_RTR__rules_shift_new_observed G1"
      in disjE)
   apply(rename_tac a b r)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac a b ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 ra")
    apply(rename_tac a b ra)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(rename_tac a b ra)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
    apply(clarsimp)
    apply(rename_tac a b ra uu_ uua_)(*strict*)
    apply(erule disjE)
     apply(rename_tac a b ra uu_ uua_)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
     apply(simp add: dom_abbreviation)
     apply(erule_tac
      x="[]"
      in allE)
     apply(force)
    apply(rename_tac a b ra uu_ uua_)(*strict*)
    apply(clarsimp)
    apply(rename_tac a b ra uu_ uua_ aa)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      in allE)
    apply(force)
   apply(rename_tac a b ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra uu_ uua_)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      in allE)
    apply(force)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_ aa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_ aa k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac a b ra uu_ uua_ aa k w)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      and P="\<lambda>x. x @ [parser_bottom G1] \<noteq> take k w"
      in allE)
    apply(force)
   apply(rename_tac a b ra uu_ uua_ aa k w nat)(*strict*)
   apply(force)
  apply(rename_tac a b r)(*strict*)
  apply(erule_tac
      P="r \<in> F_PARSER_RTR__rules_shift_old_observed G1"
      in disjE)
   apply(rename_tac a b r)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac a b ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 ra")
    apply(rename_tac a b ra)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(rename_tac a b ra)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac a b ra k w)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(case_tac "k-length w")
     apply(rename_tac a b ra k w uu_ uua_)(*strict*)
     prefer 2
     apply(rename_tac a b ra k w uu_ uua_ nat)(*strict*)
     apply(force)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(erule disjE)
     apply(rename_tac a b ra k w uu_ uua_)(*strict*)
     apply(clarsimp)
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply(simp add: dom_abbreviation)
     apply(erule_tac
      x="take k w@[parser_bottom G1]"
      and P="\<lambda>v. (\<forall>va. set va \<subseteq> parser_events G1 \<longrightarrow> parser_bottom G1 \<in> set va \<or> v \<noteq> va @ [parser_bottom G1]) \<or> (\<forall>c. take k w @ c \<noteq> v)"
      in allE)
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply(clarsimp)
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply(erule_tac
      x="take k w"
      and P="\<lambda>x. x @ [parser_bottom G1] \<noteq> take k w"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x="take k w"
      in allE)
     apply(clarsimp)
     apply(erule impE)
      apply(rename_tac ra k w uu_ uua_)(*strict*)
      apply (metis Diff_subset kPrefix_def set_kPrefix_subset subset_trans)
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply (metis in_set_takeD not_in_diff)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(clarsimp)
    apply(rename_tac ra k w uu_ uua_ aa)(*strict*)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      and P="\<lambda>x. x @ [parser_bottom G1] \<noteq> take k w"
      in allE)
    apply(force)
   apply(rename_tac a b ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra uu_ uua_)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
     prefer 2
     apply(rename_tac a b ra uu_ uua_ k w nat)(*strict*)
     apply(force)
    apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      and P="\<lambda>x. x @ [parser_bottom G1] \<noteq> take k w"
      in allE)
    apply(force)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_ aa)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: dom_abbreviation)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac a b r)(*strict*)
  apply(erule_tac
      P="r \<in> F_PARSER_RTR__rules_reduce_old_observe G1"
      in disjE)
   apply(rename_tac a b r)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac a b ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 ra")
    apply(rename_tac a b ra)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(rename_tac a b ra)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac a b ra k w)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(erule disjE)
     apply(rename_tac a b ra k w uu_ uua_)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
     apply(simp add: dom_abbreviation)
     apply(erule_tac
      x="[]"
      in allE)
     apply(force)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(clarsimp)
    apply(rename_tac a b ra k w uu_ uua_ aa)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="[]"
      in allE)
    apply(force)
   apply(rename_tac a b ra)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(erule disjE)
    apply(rename_tac a b ra uu_ uua_)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
    apply(simp add: kPrefix_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(clarsimp)
    apply(rename_tac ra uu_ uua_ k w)(*strict*)
    apply(case_tac "k-length w")
     apply(rename_tac ra uu_ uua_ k w)(*strict*)
     apply(simp add: dom_abbreviation)
     apply(erule_tac
      x="take k w@[parser_bottom G1]"
      in allE)
     apply(clarsimp)
     apply(rename_tac ra uu_ uua_ k w)(*strict*)
     apply(erule_tac
      x="take k w"
      in allE)
     apply(clarsimp)
     apply (metis in_set_takeD not_in_diff)
    apply(rename_tac ra uu_ uua_ k w nat)(*strict*)
    apply(clarsimp)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="w@[parser_bottom G1]"
      in allE)
    apply(clarsimp)
    apply(rename_tac ra uu_ uua_ k w nat)(*strict*)
    apply(erule_tac
      x="w"
      in allE)
    apply(clarsimp)
    apply (metis not_in_diff)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_ aa)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: dom_abbreviation)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac a b r)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac a b ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G1 ra")
   apply(rename_tac a b ra)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac a b ra)(*strict*)
  apply(erule disjE)
   apply(rename_tac a b ra)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac a b ra k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rename_tac a b ra k w uu_ uua_)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(erule disjE)
    apply(rename_tac a b ra k w uu_ uua_)(*strict*)
    apply(clarsimp)
    apply(rename_tac ra k w uu_ uua_)(*strict*)
    apply(case_tac "k-length w")
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply(simp add: dom_abbreviation)
     apply(erule_tac
      x="take k w@[parser_bottom G1]"
      in allE)
     apply(clarsimp)
     apply(rename_tac ra k w uu_ uua_)(*strict*)
     apply(erule_tac
      x="take k w"
      in allE)
     apply(clarsimp)
     apply (metis in_set_takeD not_in_diff)
    apply(rename_tac ra k w uu_ uua_ nat)(*strict*)
    apply(clarsimp)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="w@[parser_bottom G1]"
      in allE)
    apply(clarsimp)
    apply(rename_tac ra k w uu_ uua_ nat)(*strict*)
    apply(erule_tac
      x="w"
      in allE)
    apply(clarsimp)
    apply (metis not_in_diff)
   apply(rename_tac a b ra k w uu_ uua_)(*strict*)
   apply(clarsimp)
   apply(rename_tac ra k w uu_ uua_ aa)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac a b ra)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(clarsimp)
  apply(rename_tac a b ra uu_ uua_)(*strict*)
  apply(erule disjE)
   apply(rename_tac a b ra uu_ uua_)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(case_tac "k-length w")
    apply(rename_tac a b ra uu_ uua_ k w)(*strict*)
    apply(simp add: dom_abbreviation)
    apply(erule_tac
      x="take k w@[parser_bottom G1]"
      in allE)
    apply(clarsimp)
    apply(rename_tac ra uu_ uua_ k w)(*strict*)
    apply(rename_tac ra uu_ uua_ k w)(*strict*)
    apply(erule_tac
      x="take k w"
      in allE)
    apply(clarsimp)
    apply (metis in_set_takeD not_in_diff)
   apply(rename_tac a b ra uu_ uua_ k w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac ra uu_ uua_ k w nat)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(erule_tac
      x="w@[parser_bottom G1]"
      in allE)
   apply(clarsimp)
   apply(rename_tac ra uu_ uua_ k w nat)(*strict*)
   apply(erule_tac
      x="w"
      in allE)
   apply(clarsimp)
   apply (metis not_in_diff)
  apply(rename_tac a b ra uu_ uua_)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b ra uu_ uua_ aa)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(simp add: dom_abbreviation)
  apply(erule_tac
      x="[]"
      in allE)
  apply(force)
  done

theorem F_PARSER_RTR_preserves_valid_parser: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parser_not_observes_input_terminator P
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible P
  \<Longrightarrow> P' = F_PARSER_RTR P
  \<Longrightarrow> valid_parser P'"
  apply(simp (no_asm) add: valid_parser_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: valid_bounded_parser_def)
   apply(simp add: valid_parser_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(rule_tac
      t="{n. \<exists>r \<in> F_PARSER_RTR__rules_shift_new_observed P \<union> F_PARSER_RTR__rules_shift_old_observed P \<union> F_PARSER_RTR__rules_reduce_old_observe P \<union> F_PARSER_RTR__rules_reduce_new_observe P. n \<in> set (rule_lpop r) \<or> n \<in> set (rule_lpush r)}"
      and s="(\<Union>{set (rule_lpop y) \<union> (set (rule_lpush y)) |(y::('a \<times> 'b list, 'b) parser_step_label). y \<in> (F_PARSER_RTR__rules_shift_new_observed P \<union> F_PARSER_RTR__rules_shift_old_observed P \<union> F_PARSER_RTR__rules_reduce_old_observe P \<union> F_PARSER_RTR__rules_reduce_new_observe P)})"
      in ssubst)
    apply(rule order_antisym)
     apply(clarsimp)
     apply(rename_tac a b r)(*strict*)
     apply(rule_tac
      x="set (rule_lpop r) \<union> set (rule_lpush r)"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="r"
      in exI)
     apply(clarsimp)
    apply(clarsimp)
    apply(rename_tac a b y)(*strict*)
    apply(rule_tac
      x="y"
      in bexI)
     apply(rename_tac a b y)(*strict*)
     apply(force)
    apply(rename_tac a b y)(*strict*)
    apply(force)
   apply(rule finite_big_union)
    apply(rule finite_UnI)+
       apply(rule F_PARSER_RTR__rules_shift_new_observed_finite)
       apply(simp add: valid_bounded_parser_def)
      apply(rule F_PARSER_RTR__rules_shift_old_observed_finite)
      apply(simp add: valid_bounded_parser_def)
     apply(rule F_PARSER_RTR__rules_reduce_old_observe_finite)
     apply(simp add: valid_bounded_parser_def)
    apply(rule F_PARSER_RTR__rules_reduce_new_observe_finite)
    apply(simp add: valid_bounded_parser_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_PARSER_RTR_def)
   apply(clarsimp)
   apply(simp add: Let_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_finite F_PARSER_RTR__rules_shift_old_observed_finite F_PARSER_RTR__rules_reduce_old_observe_finite F_PARSER_RTR__rules_reduce_new_observe_finite valid_bounded_parser_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(subgoal_tac "e \<in> (F_PARSER_RTR__rules_shift_new_observed P) \<union> (F_PARSER_RTR__rules_shift_old_observed P) \<union> (F_PARSER_RTR__rules_reduce_old_observe P) \<union> (F_PARSER_RTR__rules_reduce_new_observe P)")
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac e)(*strict*)
    apply(rule F_PARSER_RTR_valid_parser_step_label_S1)
        apply(rename_tac e)(*strict*)
        apply(force)+
   apply(rename_tac e)(*strict*)
   apply(erule disjE)
    apply(rename_tac e)(*strict*)
    apply(rule F_PARSER_RTR_valid_parser_step_label_S2)
        apply(rename_tac e)(*strict*)
        apply(force)+
   apply(rename_tac e)(*strict*)
   apply(erule disjE)
    apply(rename_tac e)(*strict*)
    apply(rule F_PARSER_RTR_valid_parser_step_label_R1)
         apply(rename_tac e)(*strict*)
         apply(force)+
   apply(rename_tac e)(*strict*)
   apply(rule F_PARSER_RTR_valid_parser_step_label_R2)
       apply(rename_tac e)(*strict*)
       apply(force)+
  apply(simp add: F_PARSER_RTR_def valid_parser_def valid_bounded_parser_def Let_def)
  done

theorem F_PARSER_RTR_preserves_PARSERl: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parser_not_observes_input_terminator P
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible P
  \<Longrightarrow> P' = F_PARSER_RTR P
  \<Longrightarrow> valid_bounded_parser P' (Suc 0)"
  apply(simp (no_asm) add: valid_bounded_parser_def)
  apply(rule context_conjI)
   apply(rule F_PARSER_RTR_preserves_valid_parser)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def valid_bounded_parser_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def valid_bounded_parser_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def valid_bounded_parser_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def valid_bounded_parser_def)
  apply(clarsimp)
  done

definition der_map :: "
  ('conf1 \<Rightarrow> nat \<Rightarrow> 'conf2)
  \<Rightarrow> ('label, 'conf1) derivation
  \<Rightarrow> ('label, 'conf2) derivation"
  where
    "der_map f d \<equiv>
  \<lambda>n.
    case d n of None \<Rightarrow> None
    | Some (pair e c) \<Rightarrow> Some (pair e (f c n))"

definition F_PARSER_RTR_get_fixed_scheduler_DB :: "
  ('stack \<times> 'event list, 'event, 'marker option) parser
  \<Rightarrow> (('stack \<times> 'event list, 'event) parser_step_label, ('stack \<times> 'event list, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "F_PARSER_RTR_get_fixed_scheduler_DB G d n \<equiv>
  F_PARSER_RTR__word_get_annotation (parserS_conf_stack (the (get_configuration (d n))))"

definition F_PARSER_RTR_get_unfixed_scheduler_DB :: "
  ('stack \<times> 'event list, 'event, 'marker option) parser
  \<Rightarrow> (('stack \<times> 'event list, 'event) parser_step_label, ('stack \<times> 'event list, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "F_PARSER_RTR_get_unfixed_scheduler_DB G d n \<equiv>
  parserS_get_scheduler (the (get_configuration (d n)))"

definition F_PARSER_RTR_set_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserS_conf"
  where
    "F_PARSER_RTR_set_unfixed_scheduler_DB G d n sUF \<equiv>
  the (get_configuration (d n)) \<lparr>parserS_conf_scheduler := sUF\<rparr>"

lemma F_PARSER_RTR__rule_annotate__rev_preserves_rules: "
  F_PARSER_RTR_input G1
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G1)
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev e \<in> parser_rules G1"
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 r")
    apply(rename_tac r)(*strict*)
    apply(case_tac r)
    apply(rename_tac r rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="rule_lpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="rule_lpush"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 r")
    apply(rename_tac r)(*strict*)
    apply(case_tac r)
    apply(rename_tac r rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_lpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_rpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="rule_lpush"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 r")
    apply(rename_tac r)(*strict*)
    apply(case_tac r)
    apply(rename_tac r rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_lpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_rpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="rule_lpush"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (smt F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="[]"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="rule_lpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush rule_rpop)"
      and s="rule_lpush"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush rule_rpop)"
      and s="rule_rpop"
      in ssubst)
     apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G1 r")
   apply(rename_tac r)(*strict*)
   apply(case_tac r)
   apply(rename_tac r rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="[]"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_lpop"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpop rule_rpop)"
      and s="rule_rpop"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="rule_lpush"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply (smt F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush [])"
      and s="[]"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpop [])"
      and s="rule_lpop"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply (smt F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word rule_lpush rule_rpop)"
      and s="rule_lpush"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word rule_lpush rule_rpop)"
      and s="rule_rpop"
      in ssubst)
    apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR_no_rpush: "
  F_PARSER_RTR_input G1
  \<Longrightarrow> e2 \<in> parser_rules (F_PARSER_RTR G1)
  \<Longrightarrow> rule_rpush e2 = []"
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(erule disjE)
   apply(force)
  apply(erule disjE)
   apply(force)
  apply(erule disjE)
   apply(force)
  apply(force)
  done

lemma F_PARSER_RTR_all_rules_only_tail_marked: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpush e)) (F_PARSER_RTR__word_get_annotation (rule_lpush e)) = rule_lpush e"
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  done

lemma F_PARSER_RTR_all_rules_only_tail_marked_lpop: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpop e)) (F_PARSER_RTR__word_get_annotation (rule_lpop e)) = rule_lpop e"
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length  F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil append_Nil2 butn_empty_prime_prime butn_prefix_closureise nat_neq_iff not_Cons_self take_Nil take_Suc_conv_app_nth)
  done

lemma F_PARSER_RTR_all_reachable_configurations_only_tail_marked: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserS_conf_stack c)) (F_PARSER_RTR__word_get_annotation (parserS_conf_stack c)) = parserS_conf_stack c"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserS.derivation_initial_def)
   apply(simp add: parserS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac n e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e2")
   apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ rule_lpush e2) = F_PARSER_RTR__word_get_annotation (rule_lpush e2)")
    apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(case_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2)")
    apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc a list)(*strict*)
   apply(rule_tac
      t="(case map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2) of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (rule_lpush e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (rule_lpush e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))]"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x xa k w xc a list)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2) = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x xa k w xc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc a list)(*strict*)
   apply(thin_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2)=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc w' x')(*strict*)
   apply(case_tac "rule_lpush e2")
    apply(rename_tac n c e1 e2 c1 x xa k w xc w' x')(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpush e2 = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x xa k w xc w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc w' x' a list)(*strict*)
   apply(thin_tac "rule_lpush e2=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(case_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2)")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
   apply(subgoal_tac "map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (x @ rule_lpop e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))] = x @ rule_lpop e2")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
   apply(thin_tac "(case map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2) of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (x @ rule_lpop e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))]) = x @ rule_lpop e2")
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2) = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b a list)(*strict*)
   apply(thin_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2)=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b w' x'stack)(*strict*)
   apply(case_tac "rule_lpop e2")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b w' x'stack)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b w' x'stack a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop e2 = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b w' x'stack a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b w' x'stack a list)(*strict*)
   apply(thin_tac "rule_lpop e2=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev(rule_lpush e2)) (F_PARSER_RTR__word_get_annotation(rule_lpush e2)) = rule_lpush e2")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_all_rules_only_tail_marked)
     apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="w'stack"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) []"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule map_idI_prime)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba a bb)(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_F_PARSER_RTR__rules_annotate_word_rev_annotation_empty)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) [] @ (F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev [(x', b)]) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))) = w'stack @ [(x', b)]")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    apply(subgoal_tac "length (F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) []) = length w'stack")
     apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
     apply (smt F_PARSER_RTR__rules_annotate_word_length length_append_equal)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
    apply(rule_tac f="length" in cong)
     apply(force)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)]) = F_PARSER_RTR__rules_annotate_word_rev w'stack @ (F_PARSER_RTR__rules_annotate_word_rev [(x', b)])")
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule_tac
      P="\<lambda>X. F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) [] @ F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev [(x', b)]) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))=X"
      and t="w'stack @ [(x', b)]"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)])) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule sym)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)])"
      and s="F_PARSER_RTR__rules_annotate_word_rev w'stack @ F_PARSER_RTR__rules_annotate_word_rev [(x', b)]"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x xa k w xc x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pullout)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
  done

lemma F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_at_most_one: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> length (F_PARSER_RTR__word_get_annotation (parserS_conf_stack c)) \<le> Suc 0"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: parserS_initial_configurations_def)
   apply(simp add: F_PARSER_RTR_def)
   apply(clarsimp)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def F_PARSER_RTR__word_get_annotation_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e2")
   apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
    apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_parser_def)
   apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
   apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser )
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpush e2)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpush e2)"
      in ssubst)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply(simp add: F_PARSER_RTR__word_get_annotation_def)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(rule Annot_at_most_one)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply(erule disjE)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(rule Annot_at_most_one)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply(erule disjE)
   apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(rule_tac
      t="snd (last (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (kPrefix k (w @ [parser_bottom G]))))"
      and s="kPrefix k (w @ [parser_bottom G])"
      in ssubst)
    apply(rename_tac n c e1 c1 x k w r)(*strict*)
    apply(rule Annot_persists)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(simp add: valid_bounded_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="r"
      and P="\<lambda>r. length (rule_rpop r) \<le> Suc 0"
      in ballE)
    apply(rename_tac n c e1 c1 x k w r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(force)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 x k w r)(*strict*)
  apply(rule_tac
      t="snd (last (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)))"
      and s="rule_rpop r"
      in ssubst)
   apply(rename_tac n c e1 c1 x k w r)(*strict*)
   apply(rule Annot_persists)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
  apply(rename_tac n c e1 c1 x k w r)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def)
  apply(simp add: valid_bounded_parser_def)
  done

lemma F_PARSER_RTR_preserves_parser_not_observes_input_terminator: "
  valid_parser G
  \<Longrightarrow> parser_not_observes_input_terminator G
  \<Longrightarrow> parser_not_observes_input_terminator (F_PARSER_RTR G)"
  apply(simp add: parser_not_observes_input_terminator_def)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule disjE)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  done

lemma F_PARSER_RTR_no_top_rules: "
  valid_parser P
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_rpush e = []"
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  done

lemma F_PARSER_RTR_parser_fixed_input_length_recN: "
  valid_parser G
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parserS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> parser_fixed_input_length_recN d n = 0"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2)=0")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rule F_PARSER_RTR_no_top_rules)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(force)
  done

lemma F_PARSER_RTR_parserS_get_unfixed_scheduler_DB_parserS_get_fixed_scheduler_DB: "
  valid_parser G
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parserS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> parserS_get_unfixed_scheduler_DB (F_PARSER_RTR G) d n = parserS_get_scheduler (the (get_configuration (d n))) \<and> parserS_get_fixed_scheduler_DB (F_PARSER_RTR G) d n = []"
  apply(induct n)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: parserS_get_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp (no_asm) add: parserS_get_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "length (rule_rpush e2)=0")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_fixed_input_length_recN d n = 0")
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(rule F_PARSER_RTR_parser_fixed_input_length_recN)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)+
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rule F_PARSER_RTR_no_top_rules)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(force)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S1: "
  e1 \<in> F_PARSER_RTR__rules_shift_new_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_new_observed G
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev e1 = F_PARSER_RTR__rule_annotate__rev e2
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(clarsimp)
  apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev same_append_eq)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S2: "
  e1 \<in> F_PARSER_RTR__rules_shift_old_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_old_observed G
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev e1 = F_PARSER_RTR__rule_annotate__rev e2
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(clarsimp)
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev length_0_conv list.size(3))
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_R1: "
  e1 \<in> F_PARSER_RTR__rules_reduce_old_observe G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev e1 = F_PARSER_RTR__rule_annotate__rev e2
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(clarsimp)
  apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev same_append_eq)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_R2: "
  e1 \<in> F_PARSER_RTR__rules_reduce_new_observe G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev e1 = F_PARSER_RTR__rule_annotate__rev e2
  \<Longrightarrow> e1 = e2"
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(clarsimp)
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev length_0_conv)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S1S2: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_shift_old_observed G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(subgoal_tac "rule_rpop ra=[]")
     apply(rename_tac r ra)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj3)
       apply(rename_tac r ra)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S1R1: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(subgoal_tac "rule_rpop ra=[]")
     apply(rename_tac r ra)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj3)
       apply(rename_tac r ra)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S1R2: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_new_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(subgoal_tac "rule_rpop ra=[]")
     apply(rename_tac r ra)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj3)
       apply(rename_tac r ra)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S2R1: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_old_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
    apply(force)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_S2R2: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_shift_old_observed G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(subgoal_tac "rule_rpop ra=[]")
     apply(rename_tac r ra)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj3)
       apply(rename_tac r ra)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rule_annotate__rev_inj_R1R2: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e1 \<in> F_PARSER_RTR__rules_reduce_old_observe G
  \<Longrightarrow> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G
  \<Longrightarrow> e1 \<noteq> e2"
  apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r ra)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G ra")
   apply(rename_tac r ra)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r ra)(*strict*)
    apply(subgoal_tac "rule_rpop ra=[]")
     apply(rename_tac r ra)(*strict*)
     prefer 2
     apply(rule F_PARSER_RTR__rules_annotate_word_inj3)
       apply(rename_tac r ra)(*strict*)
       prefer 3
       apply(rule sym)
       apply(force)
      apply(rename_tac r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac r ra)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac r ra)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac r ra)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  done

lemma F_PARSER_RTR__rules_shift_old_observed_elementship: "
  valid_parser G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_rpop e = []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (rule_lpush e) = []
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_shift_old_observed G"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(case_tac "e \<in> F_PARSER_RTR__rules_shift_old_observed G")
   apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(clarsimp)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_shift_old_observed_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "rule_rpop r=[]")
   apply(rename_tac r)(*strict*)
   apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))=rule_rpop r")
   apply(rename_tac r)(*strict*)
   apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="r"
      in ballE)
   apply(rename_tac r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac r)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_reduce_new_observe_elementship: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_rpop e = []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (rule_lpush e) \<noteq> []
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_reduce_new_observe G"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(case_tac "e \<in> F_PARSER_RTR__rules_reduce_new_observe G")
   apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e")
   apply(erule disjE)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
    apply(rename_tac r)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
   apply(erule disjE)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
    apply(rename_tac r)(*strict*)
    apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
     apply(rename_tac r)(*strict*)
     apply(force)
    apply(rename_tac r)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac r k w)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
    apply(rename_tac r)(*strict*)
    apply(force)
   apply(rename_tac r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac r k w)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(subgoal_tac "e \<in> parser_rules (F_PARSER_RTR G)")
    apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_RTR_def Let_def)
  apply(simp add: F_PARSER_RTR_input_def)
  apply(rule F_PARSER_RTR_preserves_valid_parser)
       apply(simp add: valid_bounded_parser_def)
       apply(force)+
  done

lemma F_PARSER_RTR__rules_shift_new_observed_elementship: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_rpop e \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__word_get_annotation (rule_lpush e) = []
  \<Longrightarrow> e \<in> F_PARSER_RTR__rules_shift_new_observed G"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(case_tac "e \<in> F_PARSER_RTR__rules_shift_new_observed G")
   apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e")
   apply(erule disjE)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def)
    apply(clarsimp)
   apply(erule disjE)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
    apply(rename_tac r)(*strict*)
    apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)) = rule_rpop r")
     apply(rename_tac r)(*strict*)
     apply(force)
    apply(rename_tac r)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac r k w)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_reduce_old_observe_def F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(subgoal_tac "e \<in> parser_rules (F_PARSER_RTR G)")
    apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_RTR_def Let_def)
  apply(simp add: F_PARSER_RTR_input_def)
  apply(rule F_PARSER_RTR_preserves_valid_parser)
       apply(simp add: valid_bounded_parser_def)
       apply(force)+
  done

lemma F_PARSER_RTR_input_rpop_single: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules G
  \<Longrightarrow> \<exists>x. rule_rpop e = [x]"
  apply(simp add: F_PARSER_RTR_input_def)
  apply(clarsimp)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)+
     apply(case_tac "rule_rpop e")
      apply(clarsimp)
     apply(rename_tac a list)(*strict*)
     apply(case_tac list)
      apply(rename_tac a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac a list aa lista)(*strict*)
     apply(clarsimp)
    apply(force)
   apply(force)
  apply(force)
  done

interpretation "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain" : ATS_Simulation_Configuration_Weak_Plain
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserFS_configurations"
  (* initial_configurations1 *)
  "parserFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserFS_marking_condition"
  (* marked_effect1 *)
  "parserFS_marked_effect"
  (* unmarked_effect1 *)
  "parserFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserFS_configurations"
  (* initial_configurations2 *)
  "parserFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserFS_marking_condition"
  (* marked_effect2 *)
  "parserFS_marked_effect"
  (* unmarked_effect2 *)
  "parserFS_unmarked_effect"
  apply(simp add: LOCALE_DEFS parserFS_interpretations)
  done

definition F_PARSER_RTR_bisimSR :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> (('stack, 'event) parserFS_conf \<times> ('stack \<times> 'event list, 'event) parserFS_conf) set"
  where
    "F_PARSER_RTR_bisimSR P \<equiv>
  {(c, c') |
      c c'. c \<in> parserFS_configurations P
      \<and> c' \<in> parserFS_configurations (F_PARSER_RTR P)
      \<and> length (parserFS_conf_fixed c) \<le> Suc 0
      \<and> parser_bottom P \<notin> set (parserFS_conf_fixed c)
      \<and> F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack c) (parserFS_conf_fixed c) = parserFS_conf_stack c'
      \<and> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c')) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c')) = parserFS_conf_stack c'
      \<and> parserFS_conf_scheduler c = parserFS_conf_scheduler c'
      \<and> parserFS_conf_fixed c' = []}"

definition F_PARSER_RTR_bisimISR :: "
  ('stack, 'event, 'marker option) parser
  \<Rightarrow> (('stack, 'event) parserFS_conf \<times> ('stack \<times> 'event list, 'event) parserFS_conf) set"
  where
    "F_PARSER_RTR_bisimISR P \<equiv>
  {(c, c') |
    c c'. c \<in> parserFS_initial_configurations P
    \<and> c' \<in> parserFS_initial_configurations (F_PARSER_RTR P)
    \<and> parserFS_conf_scheduler c = parserFS_conf_scheduler c'}"

lemma F_PARSER_RTR_initial_simulation1: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> SR = F_PARSER_RTR_bisimSR P
  \<Longrightarrow> ISR = F_PARSER_RTR_bisimISR P
  \<Longrightarrow> parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True P (F_PARSER_RTR P) SR ORX ISR"
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation_def F_PARSER_RTR_bisimSR_def)
  apply(clarsimp)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed=parserFS_conf_fixed c0L,parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack c0L) (parserFS_conf_fixed c0L), parserFS_conf_scheduler=parserFS_conf_scheduler c0L\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(rule conjI)
    apply(rename_tac r)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac r)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(clarsimp)
   apply(rename_tac v vb c)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(rule conjI)
    apply(rename_tac v vb c)(*strict*)
    apply(force)
   apply(rename_tac v vb c)(*strict*)
   apply(rule_tac
      x="vb @ [parser_bottom P]"
      in exI)
   apply(force)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__rules_annotate_word_length F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev length_0_conv list.size(3))
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule_tac
      x="der1 \<lparr>parserFS_conf_fixed=parserFS_conf_fixed c0L,parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack c0L) (parserFS_conf_fixed c0L), parserFS_conf_scheduler=parserFS_conf_scheduler c0L\<rparr>"
      in exI)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = parserFS_conf_fixed c0L, parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack c0L) (parserFS_conf_fixed c0L), parserFS_conf_scheduler = parserFS_conf_scheduler c0L\<rparr>"
      in bexI)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: F_PARSER_RTR_bisimISR_def)
    apply(simp add: parserFS_initial_configurations_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(rule parserFS.der1_is_derivation)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.preserve_effect_initial_def)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: LT_ON_def)
    apply(clarsimp)
    apply(rename_tac c0L x)(*strict*)
    apply(simp add: parserFS_unmarked_effect_def)
    apply(clarsimp)
    apply(rename_tac c0L c c' i v e)(*strict*)
    apply(simp add: der1_def)
    apply(case_tac i)
     apply(rename_tac c0L c c' i v e)(*strict*)
     prefer 2
     apply(rename_tac c0L c c' i v e nat)(*strict*)
     apply(force)
    apply(rename_tac c0L c c' i v e)(*strict*)
    apply(clarsimp)
    apply(rename_tac c')(*strict*)
    apply (metis butlast_if_match_direct2_prime in_set_conv_nth less_zeroE list.size(3))
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: LT_ON_def)
    apply(clarsimp)
    apply(rename_tac c0L x)(*strict*)
    apply(simp add: parserFS_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac c0L c)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac c0L c i e ca)(*strict*)
   apply(simp add: der1_def)
   apply(clarsimp)
   apply(rename_tac c i e ca)(*strict*)
   apply(case_tac i)
    apply(rename_tac c i e ca)(*strict*)
    prefer 2
    apply(rename_tac c i e ca nat)(*strict*)
    apply(force)
   apply(rename_tac c i e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserFS_marking_configurations_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac ca)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac ca)(*strict*)
   apply(rule_tac
      x="(parser_initial P,[])"
      in bexI)
    apply(rename_tac ca)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac ca)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac c0L)(*strict*)
  apply(simp add: parserFS_initial_configurations_def)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  done

lemma no_see_bottom_in_F_PARSER_RTR_input: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d i = Some (pair e' c')
  \<Longrightarrow> v @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c' = parserFS_conf_scheduler c
  \<Longrightarrow> parser_bottom G \<notin> set (v @ parserFS_conf_fixed c')"
  apply(induct i arbitrary: e' c' v)
   apply(rename_tac e' c' v)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e' c' v)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac i e' c' v)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac i e' c' v)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e' c' v)(*strict*)
    apply(force)
   apply(rename_tac i e' c' v)(*strict*)
   apply(force)
  apply(rename_tac i e' c' v)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c' v e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c1 @ parserFS_conf_scheduler c1 = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
   apply(rename_tac i c' v e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in parserFS_input_with_fixed_decreases)
        apply(rename_tac i c' v e1 e2 c1)(*strict*)
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
       apply(rename_tac i c' v e1 e2 c1)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac i c' v e1 e2 c1)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac i c' v e1 e2 c1)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(rename_tac i c' v e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac i c' v e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac i c' v e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac i c' v e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac i c' v e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed c1 @ parserFS_conf_scheduler c1")
   apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in parserFS_input_with_fixed_decreases)
        apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
       apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
     apply(force)
    apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
    apply(force)
   apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
   apply(force)
  apply(rename_tac i c' v e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c' v e1 e2 c1 w wa)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed c=[]")
   apply(rename_tac i c' v e1 e2 c1 w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c' e1 e2 c1 w wa)(*strict*)
   apply(erule_tac
      x="wa"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac i c' e1 e2 c1 w wa x v)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac i c' e1 e2 c1 w wa x v)(*strict*)
    apply(erule disjE)
     apply(rename_tac i c' e1 e2 c1 w wa x v)(*strict*)
     apply(clarsimp)
     apply(rename_tac i c' e1 e2 c1 w wa x popnew)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def)
     apply(clarsimp)
     apply(simp add: parser_not_observes_input_terminator_def)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac i c' e1 e2 c1 w wa x popnew k wb)(*strict*)
     apply(simp add: kPrefix_def)
     apply(case_tac "k-length wb")
      apply(rename_tac i c' e1 e2 c1 w wa x popnew k wb)(*strict*)
      apply(clarsimp)
      apply (metis in_set_takeD nset_diff set_append_contra1)
     apply(rename_tac i c' e1 e2 c1 w wa x popnew k wb nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac i c' e1 e2 c1 w wa x popnew k wb nat xa)(*strict*)
     apply (metis List.set_simps(1) Nil_is_append_conv ex_in_conv not_Cons_self2 self_append_conv2)
    apply(rename_tac i c' e1 e2 c1 w wa x v)(*strict*)
    apply(clarsimp)
   apply(rename_tac i c' e1 e2 c1 w wa x v)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(rename_tac i c' v e1 e2 c1 w wa)(*strict*)
  apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  done

lemma F_PARSER_RTR_step_simulation1: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> SR = F_PARSER_RTR_bisimSR P
  \<Longrightarrow> ISR = F_PARSER_RTR_bisimISR P
  \<Longrightarrow> parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True P (F_PARSER_RTR P) SR ORX ISR"
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation_def F_PARSER_RTR_bisimSR_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule_tac
      x="Some (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L))"
      in exI)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed=[],parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler=parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
  apply(rule_tac
      x="der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L)) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(subgoal_tac "\<exists>x. rule_rpop eL = [x]")
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def)
   apply(clarsimp)
   apply(erule_tac
      x="eL"
      and P="\<lambda>eL. rule_rpush eL = [] \<or> rule_rpush eL = rule_rpop eL"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(erule_tac
      x="eL"
      in ballE)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply(simp add: valid_bounded_parser_def)
     apply(clarsimp)
     apply(erule_tac
      x="eL"
      in ballE)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(case_tac "rule_rpop eL")
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL a list)(*strict*)
      apply(case_tac list)
       apply(rename_tac cnL cnR cn'L eL a list)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL a list aa lista)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply(simp add: parserFS_step_relation_def)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(simp add: parserFS_step_relation_def)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(subgoal_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<in> parser_rules (F_PARSER_RTR P)")
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(clarsimp)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(case_tac v)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x xa)(*strict*)
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_shift_new_observed P")
    apply(rename_tac cnL cnR cn'L eL x xa)(*strict*)
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_shift_old_observed P")
    apply(rename_tac cnL cnR cn'L eL x xa)(*strict*)
    apply(case_tac "parserFS_conf_fixed cnL")
     apply(rename_tac cnL cnR cn'L eL x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL x xa)(*strict*)
     apply(thin_tac "F_PARSER_RTR__rule_annotate eL [] (rule_rpush eL) \<notin> F_PARSER_RTR__rules_reduce_new_observe P")
     apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
     apply(rule_tac
      x="eL"
      in exI)
     apply(clarsimp)
     apply(simp only: F_PARSER_RTR__rule_annotate_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
    apply(subgoal_tac "a#list=[x]")
     apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
     apply(subgoal_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<in> F_PARSER_RTR__rules_reduce_new_observe P")
      apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
     apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_reduce_new_observe P")
     apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
     apply(rule_tac
      x="eL"
      in exI)
     apply(clarsimp)
     apply(simp only: F_PARSER_RTR__rule_annotate_def)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parserFS_conf_fixed cn'L = rule_rpush eL")
      apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
     apply(case_tac cnL)
     apply(rename_tac cnL cnR cn'L eL x xa a list parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
     apply(case_tac cnR)
     apply(rename_tac cnL cnR cn'L eL x xa a list parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa)(*strict*)
     apply(case_tac cn'L)
     apply(rename_tac cnL cnR cn'L eL x xa a list parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa parserFS_conf_fixedb parserFS_conf_stackb parserFS_conf_schedulerb)(*strict*)
     apply(clarsimp)
     apply(rename_tac eL x xa a list parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb)(*strict*)
     apply(erule disjE)
      apply(rename_tac eL x xa a list parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb)(*strict*)
      apply(force)
     apply(rename_tac eL x xa a list parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb)(*strict*)
     apply(clarsimp)
     apply(rename_tac eL x xa a list parserFS_conf_schedulerb remainder)(*strict*)
     apply(case_tac "rule_rpush eL")
      apply(rename_tac eL x xa a list parserFS_conf_schedulerb remainder)(*strict*)
      apply(force)
     apply(rename_tac eL x xa a list parserFS_conf_schedulerb remainder aa lista)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
    apply(case_tac "rule_rpush eL")
     apply(rename_tac cnL cnR cn'L eL x xa a list)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x xa a list aa lista)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
   apply(subgoal_tac "list=[]")
    apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
   apply(subgoal_tac "rule_rpush eL=[]")
    apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
   apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_reduce_new_observe P")
   apply(case_tac "parserFS_conf_fixed cnL")
    apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
    apply(subgoal_tac "F_PARSER_RTR__rule_annotate eL [] [] \<in> F_PARSER_RTR__rules_shift_new_observed P")
     apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL [] [] \<notin> F_PARSER_RTR__rules_shift_new_observed P")
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL [] [] \<notin> F_PARSER_RTR__rules_shift_old_observed P")
    apply(simp add: F_PARSER_RTR__rule_annotate_def)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
    apply(rule_tac
      x="eL"
      in exI)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL xa a aa list)(*strict*)
   apply(subgoal_tac "aa#list=[a]")
    apply(rename_tac cnL cnR cn'L eL xa a aa list)(*strict*)
    apply(subgoal_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<in> F_PARSER_RTR__rules_shift_old_observed P")
     apply(rename_tac cnL cnR cn'L eL xa a aa list)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL xa a aa list)(*strict*)
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_shift_old_observed P")
    apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<notin> F_PARSER_RTR__rules_shift_new_observed P")
    apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
    apply(rule_tac
      x="eL"
      in exI)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
    apply(simp only: F_PARSER_RTR__rule_annotate_def)
    apply(clarsimp)
    apply(subgoal_tac "parserFS_conf_fixed cn'L=[]")
     apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL xa a)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL xa a aa list)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(subgoal_tac "rule_lpop eL \<noteq> []")
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def)
   apply(simp add: valid_parser_def valid_bounded_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="eL"
      and P="\<lambda>eL. valid_parser_step_label P eL"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(subgoal_tac "rule_lpush eL \<noteq> []")
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def)
   apply(simp add: valid_parser_def valid_bounded_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="eL"
      and P="\<lambda>eL. valid_parser_step_label P eL"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(rule parserFS.der2_is_derivation)
   apply(simp add: parserFS_step_relation_def)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word xa []"
      in exI)
    apply(simp add: F_PARSER_RTR__rule_annotate_def)
    apply (metis F_PARSER_RTR__rules_annotate_word_pullout)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(simp add: F_PARSER_RTR__rule_annotate_def)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(erule exE)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew)(*strict*)
    apply(rule disjI1)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rule_annotate_def)
    apply(case_tac cnR)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
    apply(case_tac cnL)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa)(*strict*)
    apply(case_tac cn'L)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa parserFS_conf_fixedb parserFS_conf_stackb parserFS_conf_schedulerb)(*strict*)
    apply(clarsimp)
    apply(rename_tac eL x xa v popnew parserFS_conf_fixeda parserFS_conf_schedulerb)(*strict*)
    apply(rule conjI)
     apply(rename_tac eL x xa v popnew parserFS_conf_fixeda parserFS_conf_schedulerb)(*strict*)
     apply(force)
    apply(rename_tac eL x xa v popnew parserFS_conf_fixeda parserFS_conf_schedulerb)(*strict*)
    apply(clarsimp)
    apply(case_tac parserFS_conf_fixeda)
     apply(rename_tac eL x xa v popnew parserFS_conf_fixeda parserFS_conf_schedulerb)(*strict*)
     apply(force)
    apply(rename_tac eL x xa v popnew parserFS_conf_fixeda parserFS_conf_schedulerb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac eL x xa v popnew parserFS_conf_schedulerb a)(*strict*)
    apply(case_tac v)
     apply(rename_tac eL x xa v popnew parserFS_conf_schedulerb a)(*strict*)
     apply(clarsimp)
     apply(rename_tac eL x xa popnew parserFS_conf_schedulerb a)(*strict*)
     apply(case_tac popnew)
      apply(rename_tac eL x xa popnew parserFS_conf_schedulerb a)(*strict*)
      apply(force)
     apply(rename_tac eL x xa popnew parserFS_conf_schedulerb a aa list)(*strict*)
     apply(clarsimp)
     apply(rename_tac eL x xa parserFS_conf_schedulerb a aa list)(*strict*)
     apply (metis list.simps(3) List.list.sel(3))
    apply(rename_tac eL x xa v popnew parserFS_conf_schedulerb a aa list)(*strict*)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate_def)
   apply(case_tac "parserFS_conf_fixed cnL")
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(rule parserFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac cnL cnR cn'L eL x)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac eL x f fb l lb ra rb)(*strict*)
   apply(rule conjI)
    apply(rename_tac eL x f fb l lb ra rb)(*strict*)
    prefer 2
    apply(simp add: dom_abbreviation)
    apply(clarsimp)
    apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd")(*strict*)
    apply(rule conjI)
     apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd")(*strict*)
     apply(case_tac rb)
      apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd")(*strict*)
      apply(clarsimp)
      apply(rename_tac eL x f l lb va vf vh vi c vj ca cb cc vm)(*strict*)
      apply(force)
     apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. rb = w' @ [x']")
      apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
     apply(thin_tac "rb=a#list")
     apply(clarsimp)
     apply(rename_tac eL x f fb l lb va vf vi c vj ca cb cc "cd" w')(*strict*)
     apply(rule_tac
      x="w' @ [parser_bottom P]"
      in exI)
     apply(clarsimp)
     apply(rename_tac eL x f fb l lb va vf vi c vj ca cb cc "cd" w' xa)(*strict*)
     apply(simp add: F_PARSER_RTR_def)
     apply(simp add: Let_def)
     apply(force)
    apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd")(*strict*)
    apply(case_tac rb)
     apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd")(*strict*)
     apply(clarsimp)
     apply(rename_tac eL x f l lb va vf vh vi c vj ca cb cc vm)(*strict*)
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def)
     apply(clarsimp)
     apply(simp add: parser_not_observes_input_terminator_def)
     apply(erule_tac
      x="eL"
      and P="\<lambda>eL. rule_rpush eL = [] \<or> rule_rpush eL = rule_rpop eL"
      and A="parser_rules P"
      in ballE)
      apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
     apply(subgoal_tac "parser_bottom (F_PARSER_RTR P) \<in> set (rule_rpush eL)")
      apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
      apply(force)
     apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
     apply(rule_tac
      t="rule_rpush eL"
      and s="[parser_bottom (F_PARSER_RTR P)]"
      in ssubst)
      apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
      apply(force)
     apply(rename_tac eL va vi vj ca cb cc vm xa)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. rb = w' @ [x']")
     apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac eL x f fb l lb rb va vf vh vi c vj ca cb cc vm "cd" a list)(*strict*)
    apply(thin_tac "rb=a#list")
    apply(clarsimp)
    apply(rename_tac eL x f fb l lb va vf vi c vj ca cb cc "cd" w' xa)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(force)
   apply(rename_tac eL x f fb l lb ra rb)(*strict*)
   apply(clarsimp)
   apply(rename_tac eL x f fb l lb ra rb a b)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac eL x f fb ra rb a b xa v)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1@[(a,b)]@w2 = F_PARSER_RTR__rules_annotate_word (xa @ rule_lpush eL) fb")
    apply(rename_tac eL x f fb ra rb a b xa v)(*strict*)
    prefer 2
    apply (metis ConsApp in_set_conv_decomp)
   apply(rename_tac eL x f fb ra rb a b xa v)(*strict*)
   apply(clarsimp)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
   apply(thin_tac "(a, b) \<in> set (F_PARSER_RTR__rules_annotate_word (xa @ rule_lpush eL) fb)")
   apply(subgoal_tac "w1 @ (a, b) # w2 = F_PARSER_RTR__rules_annotate_word xa [] @ F_PARSER_RTR__rules_annotate_word (rule_lpush eL) fb")
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
    prefer 2
    apply (metis F_PARSER_RTR__rules_annotate_word_pullout)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
   apply(thin_tac "w1 @ (a, b) # w2 = F_PARSER_RTR__rules_annotate_word (xa @ rule_lpush eL) fb")
   apply(subgoal_tac "prefix (w1 @ [(a, b)]) (F_PARSER_RTR__rules_annotate_word xa []) \<or> strict_prefix (F_PARSER_RTR__rules_annotate_word xa []) (w1 @ [(a, b)])")
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
    prefer 2
    apply (metis ConsApp append_eq_appendI mutual_prefix_strict_prefix)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
   apply(erule_tac
      P="(w1 @ [(a, b)]) \<sqsubseteq> F_PARSER_RTR__rules_annotate_word xa []"
      in disjE)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
    apply(rule_tac
      A="set (F_PARSER_RTR__rules_annotate_word (xa @ rule_lpop eL) f)"
      in set_mp)
     apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
     apply(force)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (xa @ rule_lpop eL) f"
      and s="F_PARSER_RTR__rules_annotate_word xa [] @ F_PARSER_RTR__rules_annotate_word (rule_lpop eL) f"
      in ssubst)
     apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_pullout)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
    apply(rule_tac
      A="set (F_PARSER_RTR__rules_annotate_word xa [])"
      in set_mp)
     apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
     apply(force)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
    apply (metis head_in_set nset_mp set_append2)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
   apply(case_tac c)
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c)(*strict*)
    apply(force)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c aa list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c aa list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac eL x f fb ra rb a b xa v w1 w2 c aa list)(*strict*)
   apply(thin_tac "c=aa#list")
   apply(clarsimp)
   apply(rename_tac eL x f fb ra rb a b xa v w2 w')(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(clarsimp)
   apply(erule_tac
      x="F_PARSER_RTR__rule_annotate eL f fb"
      in ballE)
    apply(rename_tac eL x f fb ra rb a b xa v w2 w')(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rule_annotate_def)
    apply (metis List.set_simps(2) insert_subset set_append2)
   apply(rename_tac eL x f fb ra rb a b xa v w2 w')(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew)(*strict*)
    apply (metis F_PARSER_RTR_input_def valid_parser_rules_rhs_gets_shorter valid_bounded_parser_def add_Suc add_Suc_shift list.size(3) list.size(4) add.commute plus_nat.add_0)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v remainder)(*strict*)
   apply (metis add.commute append_Nil length_shorter_1 length_shorter_append2 list.size(3) list.size(4) monoid_add_class.add.left_neutral nat_le_linear)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x xa v popnew)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
   apply(rename_tac cnL cnR cn'L eL x xa v)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x xa v remainder)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
   apply(clarsimp)
   apply(erule_tac
      x="eL"
      and A="parser_rules P"
      and P="\<lambda>eL. rule_rpush eL = [] \<or> rule_rpush eL = rule_rpop eL"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL x xa v remainder)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x xa v remainder)(*strict*)
   apply (metis set_subset_Cons subsetD)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply (metis Nil_is_append_conv F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL x)(*strict*)
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.preserve_effect_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R)(*strict*)
   apply(simp add: LT_ON_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
   apply(case_tac "xa \<in> parserFS_unmarked_effect P d1L")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    apply(erule_tac
      x="xa"
      in ballE)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    apply(rule_tac
      A="parserFS_unmarked_effect (F_PARSER_RTR P) d1R"
      in set_mp)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    apply(rule_tac
      P="\<lambda>X. parserFS_unmarked_effect (F_PARSER_RTR P) X \<subseteq> parserFS_unmarked_effect (F_PARSER_RTR P) (derivation_append d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L)) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>) n1R)"
      and s="derivation_take (derivation_append d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L)) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>) n1R) n1R"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
     apply (metis parserFS.derivation_append_derivation_take)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    apply(rule parserFS.AX_unmarked_effect_persists)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
     apply(rule F_PARSER_RTR_preserves_valid_parser)
          apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
          apply(simp add: valid_bounded_parser_def)
          apply(force)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
   apply(subgoal_tac "\<exists>c. d1L 0 = Some (pair None c)")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    prefer 2
    apply(rule parserFS.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
   apply(subgoal_tac "\<exists>c. d1R 0 = Some (pair None c)")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
    prefer 2
    apply(rule parserFS.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c ca)(*strict*)
   apply(rename_tac c0L c0R)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
   apply(simp add: F_PARSER_RTR_bisimISR_def get_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d1L n1L = Some (pair e c)")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
    prefer 2
    apply(rule parserFS.some_position_has_details_before_max_dom)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
   apply(subgoal_tac "c=cnL")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_fit_def der2_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
   apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c0L @ parserFS_conf_scheduler c0L = w @ parserFS_conf_fixed cnL @ parserFS_conf_scheduler cnL")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
    prefer 2
    apply(rule_tac
      G="P"
      and d="d1L"
      in parserFS_input_with_fixed_decreases)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
         apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
      apply (metis parserFS.derivation_append_derivation_take parserFS.derivation_take_preserves_derivation_initial)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
   apply(subgoal_tac "parserFS_conf_fixed c0L=[]")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
    prefer 2
    apply(simp add: parserFS.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
    apply(simp add: parserFS_initial_configurations_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
   apply(subgoal_tac "\<exists>w. parserFS_conf_fixed cnL @ parserFS_conf_scheduler cnL = w @ parserFS_conf_fixed cn'L @ parserFS_conf_scheduler cn'L")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
    prefer 2
    apply(rule_tac
      G="P"
      and i="n1L"
      and j="Suc n1L"
      and d="derivation_append d1L (der2 cnL eL cn'L) n1L"
      in parserFS_input_with_fixed_decreases)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
         apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
        apply(rule parserFS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
       apply(rule parserFS.derivation_initial_belongs)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
     apply(simp add: der2_def derivation_append_def)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
   apply(subgoal_tac "xa=w@wa@ parserFS_conf_fixed cn'L")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(subgoal_tac "parserFS_conf_fixed cnL = []")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "wa @ parserFS_conf_fixed cn'L = [x]")
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(clarsimp)
      apply(erule_tac
      x="w"
      in ballE)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply(simp add: parserFS_unmarked_effect_def)
       apply(clarsimp)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(rule_tac
      x="c0R"
      in exI)
       apply(rule conjI)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
        apply(simp add: derivation_append_def)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(rule conjI)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
        apply(rule_tac
      x="Suc n1R"
      in exI)
        apply(rule_tac
      x="Some(F_PARSER_RTR__rule_annotate eL [] (parserFS_conf_fixed cn'L))"
      in exI)
        apply(simp add: der2_def derivation_append_def)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      t="parser_bottom (F_PARSER_RTR P)"
      and s="parser_bottom P"
      in ssubst)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
        apply(simp add: F_PARSER_RTR_def)
        apply(simp add: Let_def)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(rule butlast_if_match_idemp_if_ignore)
       apply(subgoal_tac "parser_bottom P \<notin> set (va @ parserFS_conf_fixed c'stack)")
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
        apply (metis butlast_if_match_direct2_prime)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(rule_tac
      d="derivation_append d1L (der2 cnL eL cn'L) n1L"
      in no_see_bottom_in_F_PARSER_RTR_input)
           apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
           apply(force)
          apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
          apply(force)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e wa c c' c'stack i v ea ia va eb)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(subgoal_tac "w \<in> parserFS_unmarked_effect P d1L")
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(thin_tac "w \<notin> parserFS_unmarked_effect P d1L")
      apply(subgoal_tac "\<exists>e c. d1L n1L = Some (pair e c)")
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       prefer 2
       apply(rule parserFS.some_position_has_details_before_max_dom)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(clarsimp)
      apply(simp (no_asm) add: parserFS_unmarked_effect_def)
      apply(rule_tac
      x="c0L"
      in exI)
      apply(clarsimp)
      apply(rule_tac
      x="cnL"
      in exI)
      apply(rule conjI)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply(rule_tac
      x="n1L"
      in exI)
       apply(rule_tac
      x="e"
      in exI)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(rule_tac
      x="w"
      in exI)
      apply(clarsimp)
      apply(subgoal_tac "parser_bottom P \<notin> set w")
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       prefer 2
       apply(subgoal_tac "parser_bottom P \<notin> set (w@parserFS_conf_fixed cnL)")
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
        prefer 2
        apply(rule_tac
      d="d1L"
      in no_see_bottom_in_F_PARSER_RTR_input)
            apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
            apply(force)
           apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
           prefer 3
           apply(simp add: derivation_append_fit_def der2_def)
          apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
          apply (metis parserFS.derivation_append_derivation_take parserFS.derivation_take_preserves_derivation_initial)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply (metis butlast_if_match_direct2_prime)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(case_tac "parserFS_conf_fixed cnL")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
    apply(subgoal_tac "list=[]")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
     prefer 2
     apply(rule_tac
      w="parserFS_conf_fixed cnL"
      in length_shorter_1)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a)(*strict*)
    apply(subgoal_tac "a=x")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a)(*strict*)
     prefer 2
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a xa v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(case_tac "wa @ parserFS_conf_fixed cn'L")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
     apply(subgoal_tac "w \<in> parserFS_unmarked_effect P d1L")
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
     apply(thin_tac "w \<notin> parserFS_unmarked_effect P d1L")
     apply(subgoal_tac "w@[x] \<in> parserFS_unmarked_effect P d1L")
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      apply(rule_tac
      t="parserFS_unmarked_effect P d1L"
      and s="prefix_closure (parserFS_unmarked_effect P d1L)"
      in subst)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
       apply(rule parserFS_unmarked_effect_prefix_closed)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
        apply(simp add: F_PARSER_RTR_input_def)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
       apply (metis parserFS.derivation_append_derivation_take parserFS.derivation_take_preserves_derivation_initial)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      apply(simp add: prefix_closure_def prefix_def)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
     apply(simp (no_asm) add: parserFS_unmarked_effect_def)
     apply(rule_tac
      x="c0L"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="cnL"
      in exI)
     apply(rule conjI)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      apply(rule_tac
      x="n1L"
      in exI)
      apply(rule_tac
      x="e"
      in exI)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom P \<notin> set (w@parserFS_conf_fixed cnL)")
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      prefer 2
      apply(rule_tac
      d="d1L"
      in no_see_bottom_in_F_PARSER_RTR_input)
          apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
          apply(force)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
         prefer 3
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
        apply (metis parserFS.derivation_append_derivation_take parserFS.derivation_take_preserves_derivation_initial)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w)(*strict*)
     apply (metis butlast_if_match_direct2_prime)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "a=x")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
     prefer 2
     apply (metis ConsApp append_Cons append_assoc list.inject parserFS_string_state_def)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa list)(*strict*)
    apply(subgoal_tac "list=[]")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa list)(*strict*)
     prefer 2
     apply(simp add: parserFS_step_relation_def)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(subgoal_tac "parserFS_conf_scheduler cnR = parserFS_conf_scheduler cn'L")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     prefer 2
     apply (metis ConsApp append_assoc list.inject parserFS_string_state_def)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(thin_tac "x # parserFS_conf_scheduler cnR = wa @ parserFS_conf_fixed cn'L @ parserFS_conf_scheduler cn'L")
    apply(clarsimp)
    apply(subgoal_tac "w@[x] \<in> parserFS_unmarked_effect P d1L")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(thin_tac "w@[x] \<notin> parserFS_unmarked_effect P d1L")
    apply(simp (no_asm) add: parserFS_unmarked_effect_def)
    apply(rule_tac
      x="c0L"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="cnL"
      in exI)
    apply(rule conjI)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(rule_tac
      x="n1L"
      in exI)
     apply(rule_tac
      x="e"
      in exI)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom P \<notin> set (w@parserFS_conf_fixed cnL)")
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     prefer 2
     apply(rule_tac
      d="d1L"
      in no_see_bottom_in_F_PARSER_RTR_input)
         apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
       apply (metis parserFS.derivation_append_derivation_take parserFS.derivation_take_preserves_derivation_initial)
      apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c0L c0R e w wa)(*strict*)
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
   apply(thin_tac "derivation_append_fit d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L)) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>) n1R")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
   apply(thin_tac "\<forall>x \<in> parserFS_unmarked_effect P d1L. x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1R")
   apply(thin_tac "c0R \<in> parserFS_initial_configurations (F_PARSER_RTR P)")
   apply(thin_tac "parserFS.derivation_initial (F_PARSER_RTR P) (derivation_append d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L)) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cn'L) (parserFS_conf_fixed cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>) n1R)")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
   apply(thin_tac "maximum_of_domain d1R n1R")
   apply(thin_tac "cnR \<in> parserFS_configurations (F_PARSER_RTR P)")
   apply(thin_tac "F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnL) (parserFS_conf_fixed cnL) = parserFS_conf_stack cnR")
   apply(thin_tac "F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) (parserFS_conf_fixed cn'L) \<in> parser_rules (F_PARSER_RTR P)")
   apply(thin_tac "parserFS.derivation (F_PARSER_RTR P) d1R")
   apply(thin_tac "d1R 0 = Some (pair None c0R)")
   apply(thin_tac "parserFS_conf_scheduler c0R = w @ wa @ parserFS_conf_fixed cn'L @ parserFS_conf_scheduler cn'L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa c0L c0R e w wa)(*strict*)
   apply(simp add: parserFS_unmarked_effect_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L xa c0L e w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
   apply(case_tac "i\<le>n1L")
    apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
    apply(erule_tac
      x="c'"
      in allE)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
     apply(erule_tac
      x="i"
      in allE)
     apply(erule_tac
      x="ea"
      in allE)
   apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(erule_tac
    x="v"
    in allE)
  apply(erule impE)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(subgoal_tac "c=c0L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(subgoal_tac "i=Suc n1L")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  prefer 2
  apply(case_tac "i=Suc n1L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L e w wa c c' i v ea)(*strict*)
  apply(case_tac "i-n1L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L e w wa c c' i v ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L e w wa c c' i v ea nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L e w wa c c' i v ea nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L e w wa c c' i v ea nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' i v ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' v ea)(*strict*)
  apply(subgoal_tac "c=c0L")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' v ea)(*strict*)
  prefer 2
  apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c c' v ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c' v ea)(*strict*)
  apply(subgoal_tac "c' = cn'L")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c' v ea)(*strict*)
  prefer 2
  apply(simp add: der2_def derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa c' v ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(subgoal_tac "parser_bottom P \<notin> set(w @ wa @ parserFS_conf_fixed cn'L)")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply (metis butlast_if_match_direct2_prime)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(rule_tac
    t="w @ wa @ parserFS_conf_fixed cn'L"
    and s="(w @ wa) @ parserFS_conf_fixed cn'L"
    in ssubst)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(rule_tac
    d="derivation_append d1L (der2 cnL eL cn'L) n1L"
    in no_see_bottom_in_F_PARSER_RTR_input)
     apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L c0L e w wa ea)(*strict*)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R)(*strict*)
  apply(clarsimp)
  apply(simp add: parserFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(case_tac "i\<le>n1L")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(erule impE)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
    apply(rule_tac
    x="c"
    in exI)
    apply(simp add: derivation_append_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
   apply(rule_tac
    x="i"
    in exI)
   apply(rule_tac
    x="e"
    in exI)
   apply(rule_tac
    x="ca"
    in exI)
   apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
   apply(rule_tac
    x="cb"
    in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
  apply(rule_tac
    x="ia"
    in exI)
  apply(rule_tac
    x="ea"
    in exI)
  apply(rule_tac
    x="cc"
    in exI)
  apply(simp add: derivation_append_def)
  apply(subgoal_tac "ia \<le> n1R")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
  apply (rule parserFS.allPreMaxDomSome_prime)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca cb ia ea cc)(*strict*)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(subgoal_tac "i=Suc n1L")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  prefer 2
  apply(case_tac "i=Suc n1L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-n1L")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i ca)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca)(*strict*)
  apply(thin_tac "(\<exists>c. d1L 0 = Some (pair None c) \<and> c \<in> parserFS_configurations P) \<and> (\<exists>i e c. d1L i = Some (pair e c) \<and> c \<in> parserFS_marking_configurations P) \<longrightarrow> (\<exists>c. d1R 0 = Some (pair None c) \<and> c \<in> parserFS_configurations (F_PARSER_RTR P)) \<and> (\<exists>i e c. d1R i = Some (pair e c) \<and> c \<in> parserFS_marking_configurations (F_PARSER_RTR P))")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d1R 0 = Some (pair None c)")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   apply(rule_tac
    x="cb"
    in exI)
   apply(simp add: derivation_append_def der2_def)
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
  apply(rule_tac
    x="Suc n1R"
    in exI)
  apply(simp (no_asm) add: derivation_append_def der2_def)
  apply(simp add: parserFS_marking_configurations_def)
  apply(subgoal_tac "e=Some eL \<and> cn'L = ca")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed ca = []")
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(rule_tac
    x="F_PARSER_RTR__rules_annotate_element f (parserFS_conf_fixed ca)"
    in bexI)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
     apply(rule_tac
    x="F_PARSER_RTR__rules_annotate_word w []"
    in exI)
     apply(clarsimp)
     apply (rule F_PARSER_RTR__rules_annotate_word_pullout_prime)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(simp (no_asm) add: F_PARSER_RTR_def)
    apply(simp (no_asm) add: Let_def)
    apply(rule conjI)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
     prefer 2
     apply(rule inMap)
     apply(rule_tac
    x="f"
    in bexI)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(rule disjI2)
    apply(rule_tac
    x="(F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) [])"
    in bexI)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
     apply(rule disjI2)
     apply(simp add: F_PARSER_RTR__rule_annotate_def)
     apply(rule in_set_of_F_PARSER_RTR__rules_annotate_word)
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa v)(*strict*)
     apply(erule disjE)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa v)(*strict*)
      apply(clarsimp)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa popnew)(*strict*)
      apply(case_tac "rule_lpush eL")
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa popnew)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa popnew a list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. rule_lpush eL = w' @ [x']")
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa popnew a list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa popnew a list)(*strict*)
      apply(thin_tac "rule_lpush eL=a#list")
      apply(clarsimp)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa v)(*strict*)
     apply(clarsimp)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa)(*strict*)
     apply(case_tac "rule_lpush eL")
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. rule_lpush eL = w' @ [x']")
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w xa a list)(*strict*)
     apply(thin_tac "rule_lpush eL=a#list")
     apply(clarsimp)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
   prefer 2
   apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
   apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed ca @ parserFS_conf_scheduler ca")
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    prefer 2
    apply(rule_tac
    G="P"
    in parserFS_input_with_fixed_decreases)
         apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
         apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
        apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
        apply(rule parserFS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
       apply(rule parserFS.derivation_initial_belongs)
        apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
   apply(subgoal_tac "parserFS_conf_fixed c=[]")
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
    apply(subgoal_tac "parser_bottom P \<notin> set (wa @ parserFS_conf_fixed ca)")
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
     prefer 2
     apply(rule_tac
    d="derivation_append d1L (der2 cnL eL ca) n1L"
    in no_see_bottom_in_F_PARSER_RTR_input)
         apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
    apply(case_tac "parserFS_conf_fixed ca")
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa a list)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w wa)(*strict*)
   apply(simp add: derivation_append_def parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
  prefer 2
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c e ca)(*strict*)
  apply(rule parserFS.some_position_has_details_at_0)
  apply(force)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1R n1R = Some (pair e c)")
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
  prefer 2
  apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(case_tac "d1R n1R")
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(rule parserFS.AX_step_relation_preserves_belongsC)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(rule F_PARSER_RTR_preserves_valid_parser)
        apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
        apply(simp add: valid_bounded_parser_def)
        apply(force)
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(rule_tac
    d="derivation_append d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) []) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (w @ [f]) [], parserFS_conf_scheduler = [parser_bottom P]\<rparr>) n1R"
    and n="n1R"
    in parserFS.position_change_due_to_step_relation)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
    apply(rule parserFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
   apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(rule_tac
    i="n1R"
    and d="derivation_append d1R (der2 cnR (F_PARSER_RTR__rule_annotate eL (parserFS_conf_fixed cnL) []) \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word (w @ [f]) [], parserFS_conf_scheduler = [parser_bottom P]\<rparr>) n1R"
    in parserFS.belongs_configurations)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(rule F_PARSER_RTR_preserves_valid_parser)
        apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
        apply(simp add: valid_bounded_parser_def)
        apply(force)
       apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(force)
  apply(rename_tac cnL cnR eL x d1L n1L d1R n1R c ca cb f w e cc)(*strict*)
  apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R)(*strict*)
  apply(simp add: LT_ON_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R xa)(*strict*)
  apply(simp add: parserFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c)(*strict*)
  apply(subgoal_tac "\<exists>c. d1L 0 = Some (pair None c)")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c)(*strict*)
  prefer 2
  apply(rule parserFS.some_position_has_details_at_0)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c)(*strict*)
  apply(subgoal_tac "\<exists>c. d1R 0 = Some (pair None c)")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c)(*strict*)
  prefer 2
  apply(rule parserFS.some_position_has_details_at_0)
  apply(force)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c ca cb)(*strict*)
  apply(rule_tac
    x="cb"
    in exI)
  apply(rule conjI)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c ca cb)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c ca cb)(*strict*)
  apply(subgoal_tac "ca=c")
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c ca cb)(*strict*)
  prefer 2
  apply(simp add: derivation_append_def)
  apply(rename_tac cnL cnR cn'L eL x d1L n1L d1R n1R c ca cb)(*strict*)
  apply(clarsimp)
  done

theorem F_PARSER_RTR_lang_sound1: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> w \<in> parserFS.marked_language P
  \<Longrightarrow> \<exists>v. (w, v) \<in> ORX \<and> v \<in> parserFS.marked_language (F_PARSER_RTR P)"
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True P (F_PARSER_RTR P) (F_PARSER_RTR_bisimSR P) ORX (F_PARSER_RTR_bisimISR P)")
   prefer 2
   apply(rule F_PARSER_RTR_step_simulation1)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True P (F_PARSER_RTR P) (F_PARSER_RTR_bisimSR P) ORX (F_PARSER_RTR_bisimISR P)")
   prefer 2
   apply(rule F_PARSER_RTR_initial_simulation1)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.simulation_implies_marked_effect_subset)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(force)
     apply(simp add: F_PARSER_RTR_input_def)
     apply(rule F_PARSER_RTR_preserves_valid_parser)
          apply(simp add: valid_bounded_parser_def)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(force)
  done

theorem F_PARSER_RTR_unmarked_language_sound1: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> w \<in> parserFS.unmarked_language P
  \<Longrightarrow> \<exists>v. (w, v) \<in> ORX \<and> v \<in> parserFS.unmarked_language (F_PARSER_RTR P)"
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True P (F_PARSER_RTR P) (F_PARSER_RTR_bisimSR P) ORX (F_PARSER_RTR_bisimISR P)")
   prefer 2
   apply(rule F_PARSER_RTR_step_simulation1)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True P (F_PARSER_RTR P) (F_PARSER_RTR_bisimSR P) ORX (F_PARSER_RTR_bisimISR P)")
   prefer 2
   apply(rule F_PARSER_RTR_initial_simulation1)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.simulation_implies_unmarked_effect_subset)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(force)
     apply(simp add: F_PARSER_RTR_input_def)
     apply(rule F_PARSER_RTR_preserves_valid_parser)
          apply(simp add: valid_bounded_parser_def)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: der2_def derivation_append_fit_def derivation_append_def)
  apply(force)
  done

lemma F_PARSER_RTR_initial_simulation2: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}\<inverse>
  \<Longrightarrow> SR = (F_PARSER_RTR_bisimSR P) \<inverse>
  \<Longrightarrow> ISR = (F_PARSER_RTR_bisimISR P) \<inverse>
  \<Longrightarrow> parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True (F_PARSER_RTR P) P SR ORX ISR"
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation_def F_PARSER_RTR_bisimSR_def)
  apply(clarsimp)
  apply(rename_tac c0L)(*strict*)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed=F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c0L),parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c0L), parserFS_conf_scheduler=parserFS_conf_scheduler c0L\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(rule conjI)
    apply(rename_tac r)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: F_PARSER_RTR_input_def)
    apply(simp add: valid_bounded_parser_def)
    apply(simp add: valid_parser_def)
   apply(rename_tac r)(*strict*)
   apply(rule conjI)
    apply(rename_tac r)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: dom_abbreviation)
   apply(rename_tac r)(*strict*)
   apply(rule conjI)
    apply(rename_tac r)(*strict*)
    apply(simp add: dom_abbreviation)
    apply(clarsimp)
    apply(rename_tac v vb c)(*strict*)
    apply(rule_tac
      x="vb @ [parser_bottom (F_PARSER_RTR P)]"
      in exI)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac r)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(clarsimp)
   apply(rename_tac v vb c)(*strict*)
   apply(rule conjI)
    apply(rename_tac v vb c)(*strict*)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac v vb c)(*strict*)
   apply(rule conjI)
    apply(rename_tac v vb c)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac v vb c)(*strict*)
   apply(rule conjI)
    apply(rename_tac v vb c)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac v vb c)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule conjI)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac c0L)(*strict*)
  apply(rule_tac
      x="der1 \<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c0L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c0L), parserFS_conf_scheduler = parserFS_conf_scheduler c0L\<rparr>"
      in exI)
  apply(rename_tac c0L)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c0L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c0L), parserFS_conf_scheduler = parserFS_conf_scheduler c0L\<rparr>"
      in bexI)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: F_PARSER_RTR_bisimISR_def)
    apply(simp add: parserFS_initial_configurations_def)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(rule parserFS.der1_is_derivation)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.preserve_effect_initial_def)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: LT_ON_def)
    apply(clarsimp)
    apply(rename_tac c0L x)(*strict*)
    apply(simp add: parserFS_unmarked_effect_def)
    apply(clarsimp)
    apply(rename_tac c0L c c' i v e)(*strict*)
    apply(simp add: der1_def)
    apply(case_tac i)
     apply(rename_tac c0L c c' i v e)(*strict*)
     prefer 2
     apply(rename_tac c0L c c' i v e nat)(*strict*)
     apply(force)
    apply(rename_tac c0L c c' i v e)(*strict*)
    apply(clarsimp)
    apply(rename_tac c')(*strict*)
    apply(rule context_conjI)
     apply(rename_tac c')(*strict*)
     prefer 2
     apply(clarsimp)
     apply(simp add: F_PARSER_RTR_def)
     apply(simp add: Let_def)
    apply(rename_tac c')(*strict*)
    apply(simp add: parserFS_initial_configurations_def)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac c0L)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(rule conjI)
    apply(rename_tac c0L)(*strict*)
    apply(simp add: LT_ON_def)
    apply(clarsimp)
    apply(rename_tac c0L x)(*strict*)
    apply(simp add: parserFS_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac c0L c)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c0L)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac c0L c i e ca)(*strict*)
   apply(simp add: der1_def)
   apply(clarsimp)
   apply(rename_tac c i e ca)(*strict*)
   apply(case_tac i)
    apply(rename_tac c i e ca)(*strict*)
    prefer 2
    apply(rename_tac c i e ca nat)(*strict*)
    apply(force)
   apply(rename_tac c i e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(simp add: parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserFS_marking_configurations_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac ca)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac ca)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
   apply(clarsimp)
  apply(rename_tac c0L)(*strict*)
  apply(simp add: parserFS_initial_configurations_def)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  apply(simp add: F_PARSER_RTR_def)
  apply(simp add: Let_def)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_element_def)
  done

lemma F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_short: "
  F_PARSER_RTR_input P
  \<Longrightarrow> eL \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> rule_lpush eL \<noteq> []
  \<Longrightarrow> length (F_PARSER_RTR__word_get_annotation (rule_lpush eL)) \<le> Suc 0"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime less_zeroE list.size(3) trivNat)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime less_zeroE list.size(3) trivNat)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR_input_rpop_single Nat.add_0_right F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__rules_annotate_word_length add_Suc_right eq_imp_le length_0_conv list.size(3) list.size(4))
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply (metis F_PARSER_RTR_input_rpop_single Nat.add_0_right F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__rules_annotate_word_length add_Suc_right eq_imp_le length_0_conv list.size(3) list.size(4))
  done

lemma F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_no_parser_bottom: "
  F_PARSER_RTR_input P
  \<Longrightarrow> eL \<in> parser_rules (F_PARSER_RTR P)
  \<Longrightarrow> rule_lpush eL \<noteq> []
  \<Longrightarrow> parser_bottom P \<notin> set (F_PARSER_RTR__word_get_annotation (rule_lpush eL))"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__rules_annotate_word_length_prime empty_iff list.set(1))
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__rules_annotate_word_length_prime empty_iff list.set(1))
  apply(erule disjE)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
   apply(clarsimp)
   apply(erule_tac
      x="r"
      and A="parser_rules P"
      and P="\<lambda>r. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r"
      in ballE)
    apply(rename_tac r)(*strict*)
    apply(clarsimp)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length length_0_conv list.size(3))
   apply(rename_tac r)(*strict*)
   apply(force)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
  apply(clarsimp)
  apply(erule_tac
      x="r"
      and A="parser_rules P"
      and P="\<lambda>r. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r"
      in ballE)
   apply(rename_tac r)(*strict*)
   apply(clarsimp)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length length_0_conv list.size(3))
  apply(rename_tac r)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_marking_configurations: "
  F_PARSER_RTR_input P
  \<Longrightarrow> c \<in> parserFS_marking_configurations (F_PARSER_RTR P)
  \<Longrightarrow> parserFS_conf_fixed c = []
  \<Longrightarrow> parserFS_conf_stack c \<noteq> []
  \<Longrightarrow> (parser_bottom P \<in> set (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c)) \<longrightarrow> parserFS_conf_scheduler c = [])
  \<Longrightarrow> F_PARSER_RTR__conf_annotate__rev c \<in> parserFS_marking_configurations P"
  apply(subgoal_tac "F_PARSER_RTR__conf_annotate__rev c \<in> parserFS_configurations P")
   prefer 2
   apply(rule F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_configurations)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: parserFS_marking_configurations_def)
  apply(simp add: parserFS_marking_configurations_def)
  apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
  apply(clarsimp)
  apply(rename_tac a b w)(*strict*)
  apply(rule conjI)
   apply(rename_tac a b w)(*strict*)
   apply(rule_tac
      x="a"
      in bexI)
    apply(rename_tac a b w)(*strict*)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev w"
      in exI)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (w @ [(a, b)])"
      and s="F_PARSER_RTR__rules_annotate_word_rev w @ F_PARSER_RTR__rules_annotate_word_rev [(a, b)]"
      in ssubst)
     apply(rename_tac a b w)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_distrib_append rotate_simps)
    apply(rename_tac a b w)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac a b w)(*strict*)
   apply(simp add: F_PARSER_RTR_def Let_def)
   apply(clarsimp)
   apply(rename_tac a b w aa)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a b w)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (w @ [(a, b)])"
      and s="[]"
      in ssubst)
   apply(rename_tac a b w)(*strict*)
   apply(simp add: F_PARSER_RTR_def Let_def)
   apply(clarsimp)
   apply(rename_tac a b w aa)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
  apply(rename_tac a b w)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR_def Let_def)
  done

lemma F_PARSER_RTR_preserves_empty_fixed: "
  F_PARSER_RTR_input P
  \<Longrightarrow> parserFS_conf_fixed c1 = []
  \<Longrightarrow> parserFS_step_relation (F_PARSER_RTR P) c1 e c2
  \<Longrightarrow> parserFS_conf_fixed c2 = []"
  apply(simp add: parserFS_step_relation_def)
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(erule_tac
      P="e \<in> F_PARSER_RTR__rules_shift_new_observed P"
      in disjE)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac x r)(*strict*)
   apply(force)
  apply(rename_tac x v)(*strict*)
  apply(erule_tac
      P="e \<in> F_PARSER_RTR__rules_shift_old_observed P"
      in disjE)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(erule_tac
      P="e \<in> F_PARSER_RTR__rules_reduce_old_observe P"
      in disjE)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac x r)(*strict*)
   apply(force)
  apply(rename_tac x v)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  done

lemma F_PARSER_RTR_preserves_nonempty_lhs: "
  F_PARSER_RTR_input P
  \<Longrightarrow> parserFS_step_relation (F_PARSER_RTR P) c1 e c2
  \<Longrightarrow> parserFS_conf_stack c2 \<noteq> []"
  apply(simp add: parserFS_step_relation_def)
  apply(subgoal_tac "rule_lpush e \<noteq> []")
   prefer 2
   apply(subgoal_tac "valid_parser (F_PARSER_RTR P)")
    apply(simp add: valid_parser_def)
    apply(clarsimp)
    apply(rename_tac v)(*strict*)
    apply(erule_tac
      x="e"
      in ballE)
     apply(rename_tac v)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac v)(*strict*)
    apply(force)
   apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(clarsimp)
  done

lemma F_PARSER_RTR_rule_lpop_not_empty: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_lpop e \<noteq> []"
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e")
   apply(simp add: valid_parser_step_label_def)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(simp add: valid_parser_def)
  apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
  done

lemma F_PARSER_RTR_rule_lpush_not_empty: "
  F_PARSER_RTR_input G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_RTR G)
  \<Longrightarrow> rule_lpush e \<noteq> []"
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e")
   apply(simp add: valid_parser_step_label_def)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(simp add: valid_parser_def)
  apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
  done

lemma F_PARSER_RTR_never_fixed: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> parserFS_conf_fixed cn = []"
  apply(induct n arbitrary: en cn)
   apply(rename_tac en cn)(*strict*)
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac n en cn)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n en cn)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n en cn)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n en cn)(*strict*)
    apply(force)
   apply(rename_tac n en cn)(*strict*)
   apply(force)
  apply(rename_tac n en cn)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rule F_PARSER_RTR_preserves_empty_fixed)
    apply(rename_tac n cn e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac n cn e1 e2 c1)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_fixed_suffix_of_removed: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> v @ parserFS_conf_scheduler cn = parserFS_conf_scheduler c0
  \<Longrightarrow> v \<sqsupseteq> F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn)"
  apply(induct n arbitrary: en cn v)
   apply(rename_tac en cn v)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(simp add: F_PARSER_RTR_def Let_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac n en cn v)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n en cn v)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n en cn v)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n en cn v)(*strict*)
    apply(force)
   apply(rename_tac n en cn v)(*strict*)
   apply(force)
  apply(rename_tac n en cn v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn v e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c0 = w@parserFS_conf_scheduler c1")
   apply(rename_tac n cn v e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      i="0"
      and j="n"
      and d="d"
      and G="F_PARSER_RTR G"
      in parserFS_input_decreases)
        apply(rename_tac n cn v e1 e2 c1)(*strict*)
        apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
       apply(rename_tac n cn v e1 e2 c1)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac n cn v e1 e2 c1)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac n cn v e1 e2 c1)(*strict*)
       apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
      apply(rename_tac n cn v e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac n cn v e1 e2 c1)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
    apply(rename_tac n cn v e1 e2 c1)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
   apply(rename_tac n cn v e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac n cn v e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
  apply(erule_tac
      x="w"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c1 = w@parserFS_conf_scheduler cn")
   apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
   prefer 2
   apply(rule_tac
      i="n"
      and j="Suc n"
      and d="d"
      and G="F_PARSER_RTR G"
      in parserFS_input_decreases)
        apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
        apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
       apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
       apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
      apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
      apply(force)
     apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
    apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
   apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
   apply(force)
  apply(rename_tac n cn v e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 w wa)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   prefer 2
   apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(subgoal_tac "rule_lpop e2 \<noteq> []")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_rule_lpop_not_empty)
    apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(subgoal_tac "rule_lpush e2 \<noteq> []")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_rule_lpush_not_empty)
    apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(case_tac "e2 \<in> F_PARSER_RTR__rules_shift_new_observed G")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(rule_tac
      x="c@wa"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])"
      and s="[]"
      in ssubst)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(clarsimp)
   apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(case_tac "e2 \<in> F_PARSER_RTR__rules_shift_old_observed G")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(rule_tac
      x="c@rule_rpop r@wa"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length append_Nil2 append_self_conv list.size(3) takePrecise take_0)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(force)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed c1 = []")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_never_fixed)
     apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
     apply(force)
    apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(force)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(case_tac "e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(thin_tac "e2 \<notin> F_PARSER_RTR__rules_shift_new_observed G")
   apply(thin_tac "e2 \<notin> F_PARSER_RTR__rules_shift_old_observed G")
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpop r) ([]))"
      and s="[]"
      in ssubst)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length append_Nil2 append_self_conv list.size(3) takePrecise take_0)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])=[]")
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
     apply(clarsimp)
    apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r x)(*strict*)
   apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(case_tac "e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G")
   apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
   apply(thin_tac "e2 \<notin> F_PARSER_RTR__rules_shift_new_observed G")
   apply(thin_tac "e2 \<notin> F_PARSER_RTR__rules_shift_old_observed G")
   apply(thin_tac "e2 \<notin> F_PARSER_RTR__rules_reduce_old_observe G")
   apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 wa c r)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n cn e1 c1 c r x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
    apply(rename_tac n cn e1 c1 c r x)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length append_Nil2 append_self_conv list.size(3) takePrecise take_0)
   apply(rename_tac n cn e1 c1 c r x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
    apply(rename_tac n cn e1 c1 c r x)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length append_Nil2 append_self_conv list.size(3) takePrecise take_0)
   apply(rename_tac n cn e1 c1 c r x)(*strict*)
   apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 wa c)(*strict*)
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(simp add: parserFS_step_relation_def)
  done

lemma F_PARSER_RTR_relects_steps1: "
  F_PARSER_RTR_input P
  \<Longrightarrow> cnR \<in> parserFS_configurations P
  \<Longrightarrow> cnL \<in> parserFS_configurations (F_PARSER_RTR P)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR) = parserFS_conf_stack cnL
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cnL)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cnL)) = parserFS_conf_stack cnL
  \<Longrightarrow> parserFS_conf_scheduler cnR = parserFS_conf_scheduler cnL
  \<Longrightarrow> parserFS_conf_fixed cnL = []
  \<Longrightarrow> parserFS_step_relation (F_PARSER_RTR P) cnL eL cn'L
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev eL \<in> parser_rules P
  \<Longrightarrow> rule_lpop eL \<noteq> []
  \<Longrightarrow> rule_lpush eL \<noteq> []
  \<Longrightarrow> parserFS_step_relation P cnR (F_PARSER_RTR__rule_annotate__rev eL) \<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>"
  apply(simp add: parserFS_step_relation_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(erule disjE)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
   apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(erule disjE)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
    apply(case_tac "eL \<in> F_PARSER_RTR__rules_shift_new_observed P")
     apply(rename_tac x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
     apply(clarsimp)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])"
      and s="[]"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
     apply(rename_tac x r)(*strict*)
     apply(clarsimp)
    apply(rename_tac x v)(*strict*)
    apply(case_tac "eL \<in> F_PARSER_RTR__rules_shift_old_observed P")
     apply(rename_tac x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
     apply(clarsimp)
     apply(rename_tac x r)(*strict*)
     apply(subgoal_tac "rule_lpop r \<noteq> []")
      apply(rename_tac x r)(*strict*)
      prefer 2
      apply(subgoal_tac "valid_parser_step_label P r")
       apply(rename_tac x r)(*strict*)
       apply(simp add: valid_parser_step_label_def)
      apply(rename_tac x r)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
      apply(force)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
     apply(rename_tac x r)(*strict*)
     apply(clarsimp)
    apply(rename_tac x v)(*strict*)
    apply(case_tac "eL \<in> F_PARSER_RTR__rules_reduce_old_observe P")
     apply(rename_tac x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
     apply(clarsimp)
     apply(rename_tac x r)(*strict*)
     apply(subgoal_tac "rule_lpush r \<noteq> []")
      apply(rename_tac x r)(*strict*)
      prefer 2
      apply(subgoal_tac "valid_parser_step_label P r")
       apply(rename_tac x r)(*strict*)
       apply(simp add: valid_parser_step_label_def)
      apply(rename_tac x r)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
      apply(force)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])"
      and s="[]"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
     apply(rename_tac x r)(*strict*)
     apply(clarsimp)
    apply(rename_tac x v)(*strict*)
    apply(case_tac "eL \<in> F_PARSER_RTR__rules_reduce_new_observe P")
     apply(rename_tac x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
     apply(clarsimp)
     apply(rename_tac x r)(*strict*)
     apply(subgoal_tac "rule_lpush r \<noteq> []")
      apply(rename_tac x r)(*strict*)
      prefer 2
      apply(subgoal_tac "valid_parser_step_label P r")
       apply(rename_tac x r)(*strict*)
       apply(simp add: valid_parser_step_label_def)
      apply(rename_tac x r)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac x r)(*strict*)
     apply(subgoal_tac "rule_lpop r \<noteq> []")
      apply(rename_tac x r)(*strict*)
      prefer 2
      apply(subgoal_tac "valid_parser_step_label P r")
       apply(rename_tac x r)(*strict*)
       apply(simp add: valid_parser_step_label_def)
      apply(rename_tac x r)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
      apply(force)
     apply(rename_tac x r)(*strict*)
     apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
      apply(rename_tac x r)(*strict*)
      apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
      apply(force)
     apply(rename_tac x r)(*strict*)
     apply(clarsimp)
    apply(rename_tac x v)(*strict*)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(case_tac "eL \<in> F_PARSER_RTR__rules_shift_new_observed P")
    apply(rename_tac x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
    apply(clarsimp)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])"
      and s="[]"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
    apply(rename_tac x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "eL \<in> F_PARSER_RTR__rules_shift_old_observed P")
    apply(rename_tac x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
    apply(clarsimp)
    apply(rename_tac x r)(*strict*)
    apply(subgoal_tac "rule_lpop r \<noteq> []")
     apply(rename_tac x r)(*strict*)
     prefer 2
     apply(subgoal_tac "valid_parser_step_label P r")
      apply(rename_tac x r)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac x r)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
     apply(force)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
    apply(rename_tac x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "eL \<in> F_PARSER_RTR__rules_reduce_old_observe P")
    apply(rename_tac x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
    apply(clarsimp)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])"
      and s="[]"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])"
      and s="[]"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_length_prime)
    apply(rename_tac x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "eL \<in> F_PARSER_RTR__rules_reduce_new_observe P")
    apply(rename_tac x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
    apply(rename_tac x r)(*strict*)
    apply(subgoal_tac "rule_lpush r \<noteq> []")
     apply(rename_tac x r)(*strict*)
     prefer 2
     apply(subgoal_tac "valid_parser_step_label P r")
      apply(rename_tac x r)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac x r)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(subgoal_tac "rule_lpop r \<noteq> []")
     apply(rename_tac x r)(*strict*)
     prefer 2
     apply(subgoal_tac "valid_parser_step_label P r")
      apply(rename_tac x r)(*strict*)
      apply(simp add: valid_parser_step_label_def)
     apply(rename_tac x r)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
     apply(force)
    apply(rename_tac x r)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r))"
      and s="rule_rpop r"
      in ssubst)
     apply(rename_tac x r)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
     apply(force)
    apply(rename_tac x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
  apply(erule conjE)+
  apply(erule disjE)
   apply(rule disjI1)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(rule conjI)
    apply(rename_tac x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (rule_lpop eL)"
      and s="F_PARSER_RTR__word_get_annotation (x@rule_lpop eL)"
      in ssubst)
     apply(rename_tac x v)(*strict*)
     apply(rule F_PARSER_RTR__word_get_annotation_not_empty)
     apply(force)
    apply(rename_tac x v)(*strict*)
    apply(rule_tac
      t="x @ rule_lpop eL"
      and s="F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR)"
      in ssubst)
     apply(rename_tac x v)(*strict*)
     apply(force)
    apply(rename_tac x v)(*strict*)
    apply(subgoal_tac "parserFS_conf_stack cnR\<noteq>[]")
     apply(rename_tac x v)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(rename_tac x v)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
    apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_not_empty)
  apply(rule disjI2)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (rule_lpop eL)"
      and s="F_PARSER_RTR__word_get_annotation (x@rule_lpop eL)"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_not_empty)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="x @ rule_lpop eL"
      and s="F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR)"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "parserFS_conf_stack cnR\<noteq>[]")
    apply(rename_tac x)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply (metis F_PARSER_RTR__word_get_annotation_not_empty)
  done

lemma F_PARSER_RTR_relects_steps2: "
  F_PARSER_RTR_input P
  \<Longrightarrow> cnR \<in> parserFS_configurations P
  \<Longrightarrow> cnL \<in> parserFS_configurations (F_PARSER_RTR P)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR) = parserFS_conf_stack cnL
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cnL)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cnL)) = parserFS_conf_stack cnL
  \<Longrightarrow> parserFS_conf_scheduler cnR = parserFS_conf_scheduler cnL
  \<Longrightarrow> parserFS_conf_fixed cnL = []
  \<Longrightarrow> parserFS_step_relation (F_PARSER_RTR P) cnL eL cn'L
  \<Longrightarrow> F_PARSER_RTR__rule_annotate__rev eL \<in> parser_rules P
  \<Longrightarrow> rule_lpop eL \<noteq> []
  \<Longrightarrow> rule_lpush eL \<noteq> []
  \<Longrightarrow> cX1 = cnR
  \<Longrightarrow> cX2 = \<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>
  \<Longrightarrow> eX = (F_PARSER_RTR__rule_annotate__rev eL)
  \<Longrightarrow> parserFS_step_relation P cX1 eX cX2"
  apply(clarsimp)
  apply(rule F_PARSER_RTR_relects_steps1)
            apply(force)+
  done

lemma F_PARSER_RTR_step_simulation2: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}\<inverse>
  \<Longrightarrow> SR = (F_PARSER_RTR_bisimSR P) \<inverse>
  \<Longrightarrow> ISR = (F_PARSER_RTR_bisimISR P) \<inverse>
  \<Longrightarrow> parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True (F_PARSER_RTR P) P SR ORX ISR"
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation_def F_PARSER_RTR_bisimSR_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule_tac
      x="Some (F_PARSER_RTR__rule_annotate__rev eL)"
      in exI)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed=F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L),parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler=parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
  apply(rule_tac
      x="der2 cnR (F_PARSER_RTR__rule_annotate__rev eL) \<lparr>parserFS_conf_fixed=F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L),parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler=parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
  apply(subgoal_tac "F_PARSER_RTR__rule_annotate__rev eL \<in> parser_rules P")
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rule_annotate__rev_preserves_rules)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(subgoal_tac "rule_lpop eL \<noteq> []")
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   prefer 2
   apply(thin_tac "parserFS_step_relation (F_PARSER_RTR P) cnL eL cn'L")
   apply(thin_tac "cnR \<in> parserFS_configurations P")
   apply(thin_tac "cnL \<in> parserFS_configurations (F_PARSER_RTR P)")
   apply(thin_tac "length (parserFS_conf_fixed cnR) \<le> Suc 0")
   apply(thin_tac "parser_bottom P \<notin> set (parserFS_conf_fixed cnR)")
   apply(thin_tac "F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR) = parserFS_conf_stack cnL")
   apply(thin_tac "parserFS_conf_scheduler cnR = parserFS_conf_scheduler cnL")
   apply(thin_tac "parserFS_conf_fixed cnL = []")
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(rename_tac cnL eL)(*strict*)
   apply(subgoal_tac "valid_parser_step_label P \<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL), rule_rpop = F_PARSER_RTR__word_get_annotation (rule_lpop eL) @ rule_rpop eL, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL), rule_rpush = F_PARSER_RTR__word_get_annotation (rule_lpush eL)\<rparr>")
    apply(rename_tac cnL eL)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac cnL eL k w xa)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(rename_tac cnL eL)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(subgoal_tac "rule_lpush eL \<noteq> []")
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   prefer 2
   apply(thin_tac "parserFS_step_relation (F_PARSER_RTR P) cnL eL cn'L")
   apply(thin_tac "cnR \<in> parserFS_configurations P")
   apply(thin_tac "cnL \<in> parserFS_configurations (F_PARSER_RTR P)")
   apply(thin_tac "length (parserFS_conf_fixed cnR) \<le> Suc 0")
   apply(thin_tac "parser_bottom P \<notin> set (parserFS_conf_fixed cnR)")
   apply(thin_tac "F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR) = parserFS_conf_stack cnL")
   apply(thin_tac "parserFS_conf_scheduler cnR = parserFS_conf_scheduler cnL")
   apply(thin_tac "parserFS_conf_fixed cnL = []")
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(rename_tac cnL eL)(*strict*)
   apply(subgoal_tac "valid_parser_step_label P \<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL), rule_rpop = F_PARSER_RTR__word_get_annotation (rule_lpop eL) @ rule_rpop eL, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL), rule_rpush = F_PARSER_RTR__word_get_annotation (rule_lpush eL)\<rparr>")
    apply(rename_tac cnL eL)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac cnL eL k w xa)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(rename_tac cnL eL)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(rule parserFS.der2_is_derivation)
   apply(rule F_PARSER_RTR_relects_steps1)
             apply(rename_tac cnL cnR cn'L eL)(*strict*)
             apply(force)
            apply(rename_tac cnL cnR cn'L eL)(*strict*)
            apply(force)
           apply(rename_tac cnL cnR cn'L eL)(*strict*)
           apply(force)
          apply(rename_tac cnL cnR cn'L eL)(*strict*)
          apply(force)
         apply(rename_tac cnL cnR cn'L eL)(*strict*)
         apply(force)
        apply(rename_tac cnL cnR cn'L eL)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(rule_tac
      t="\<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>"
      and s="F_PARSER_RTR__conf_annotate__rev cn'L"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(rule F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_configurations)
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(subgoal_tac "parserFS_conf_fixed cn'L = rule_rpush eL")
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       prefer 2
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
       apply(erule disjE)
        apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
        apply(clarsimp)
       apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(subgoal_tac "eL \<in> parser_rules (F_PARSER_RTR P)")
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       prefer 2
       apply(simp add: parserFS_step_relation_def)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(clarsimp)
      apply(simp add: F_PARSER_RTR_def)
      apply(simp add: Let_def)
      apply(erule disjE)
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(erule disjE)
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(erule disjE)
       apply(rename_tac cnL cnR cn'L eL)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    prefer 2
    apply(rule parserFS.AX_step_relation_preserves_belongsC)
      apply(rename_tac cnL cnR cn'L eL)(*strict*)
      apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "False")
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime all_not_in_conv empty_def set_empty2)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime all_not_in_conv empty_def set_empty2)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply(subgoal_tac "parser_bottom P \<in> set (rule_rpop r)")
      apply(rename_tac cnL cnR cn'L x r)(*strict*)
      prefer 2
      apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length length_0_conv list.size(3))
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply(subgoal_tac "parser_bottom P \<notin> set (rule_rpop r)")
      apply(rename_tac cnL cnR cn'L x r)(*strict*)
      prefer 2
      apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
      apply(clarsimp)
      apply(erule_tac
      x="r"
      and P="\<lambda>r. parser_bottom P \<notin> set (rule_rpush r)"
      in ballE)
       apply(rename_tac cnL cnR cn'L x r)(*strict*)
       apply(clarsimp)
      apply(rename_tac cnL cnR cn'L x r)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(subgoal_tac "parser_bottom P \<in> set (rule_rpop r)")
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     prefer 2
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length length_0_conv)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(subgoal_tac "parser_bottom P \<notin> set (rule_rpop r)")
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     prefer 2
     apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
     apply(clarsimp)
     apply(erule_tac
      x="r"
      and P="\<lambda>r. parser_bottom P \<notin> set (rule_rpush r)"
      in ballE)
      apply(rename_tac cnL cnR cn'L x r)(*strict*)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime all_not_in_conv empty_def set_empty2)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length_prime all_not_in_conv empty_def set_empty2)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(subgoal_tac "parser_bottom P \<in> set (rule_rpop r)")
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     prefer 2
     apply (metis F_PARSER_RTR__conf_get_annotation_def  F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length length_0_conv)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(subgoal_tac "parser_bottom P \<notin> set (rule_rpop r)")
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     prefer 2
     apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L x r)(*strict*)
   apply(subgoal_tac "parser_bottom P \<in> set (rule_rpop r)")
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    prefer 2
    apply (metis F_PARSER_RTR__conf_get_annotation_def  F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_length length_0_conv)
   apply(rename_tac cnL cnR cn'L x r)(*strict*)
   apply(subgoal_tac "parser_bottom P \<notin> set (rule_rpop r)")
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR_input_def parser_not_observes_input_terminator_def)
    apply(clarsimp)
    apply(erule_tac
      x="r"
      and P="\<lambda>r. parser_bottom P \<notin> set (rule_rpush r)"
      in ballE)
     apply(rename_tac cnL cnR cn'L x r)(*strict*)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L x r)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L x r)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(rule parserFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac cnL cnR cn'L eL)(*strict*)
     apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser)
    apply(rename_tac cnL cnR cn'L eL)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpush eL)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpush eL)"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_short)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(subgoal_tac "parser_bottom P \<notin> set (F_PARSER_RTR__word_get_annotation (x @ rule_lpush eL))")
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpush eL)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpush eL)"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_no_parser_bottom)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpush eL)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpush eL)"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (x @ rule_lpush eL)"
      and s="F_PARSER_RTR__rules_annotate_word_rev x @ F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL)"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev x @ F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL)) (F_PARSER_RTR__word_get_annotation (rule_lpush eL))"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev x) [] @ F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL)) (F_PARSER_RTR__word_get_annotation (rule_lpush eL))"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR_all_rules_only_tail_marked F_PARSER_RTR__rules_annotate_word_append_prime F_PARSER_RTR__rules_annotate_word_length F_PARSER_RTR__rules_annotate_word_rev_distrib_append butn_prefix_closureise butn_zero list.size(3) self_append_conv)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev x) []"
      and s="x"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(rule_tac
      v="rule_lpop eL"
      in append_injr)
    apply(rule_tac
      t="x @ rule_lpop eL"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (x @ rule_lpop eL)) (F_PARSER_RTR__word_get_annotation (x @ rule_lpop eL))"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (x @ rule_lpop eL)"
      and s="F_PARSER_RTR__rules_annotate_word_rev x @ (F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL))"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply (metis F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpop eL)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpop eL)"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev x @ F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL)) (F_PARSER_RTR__word_get_annotation (rule_lpop eL))"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev x) ([]) @ F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL)) (F_PARSER_RTR__word_get_annotation (rule_lpop eL))"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(rule F_PARSER_RTR__rules_annotate_word_pullout)
     apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpop eL)) (F_PARSER_RTR__word_get_annotation (rule_lpop eL))"
      and s="rule_lpop eL"
      in ssubst)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply (metis F_PARSER_RTR_all_rules_only_tail_marked_lpop)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (rule_lpush eL)) (F_PARSER_RTR__word_get_annotation (rule_lpush eL))"
      and s="rule_lpush eL"
      in ssubst)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply (metis F_PARSER_RTR_all_rules_only_tail_marked)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(erule disjE)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR_def)
    apply(simp add: Let_def)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(erule disjE)
     apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL x v)(*strict*)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL)(*strict*)
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.preserve_effect_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R)(*strict*)
  apply(subgoal_tac "\<exists>c. d1R 0 = Some (pair None c)")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R)(*strict*)
  apply(subgoal_tac "\<exists>c. d1L 0 = Some (pair None c)")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
    apply(clarsimp)
    apply(simp add: parserFS_marking_condition_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
    apply(rule conjI)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     apply(rule_tac
      x="the (get_configuration (d1R 0))"
      in exI)
     apply(rule conjI)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
      apply(simp add: derivation_append_def)
      apply(simp add: get_configuration_def)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     apply(case_tac "d1R 0")
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc a)(*strict*)
     apply(simp add: get_configuration_def)
     apply(rule_tac
      d="d1R"
      in parserFS.belongs_configurations)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc a)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc a)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc a)(*strict*)
      apply(thin_tac "cnR \<in> parserFS_configurations P")
      apply(thin_tac "cnL \<in> parserFS_configurations (F_PARSER_RTR P)")
      apply(thin_tac "length (parserFS_conf_fixed cnR) \<le> Suc 0")
      apply(thin_tac "parser_bottom P \<notin> set (parserFS_conf_fixed cnR)")
      apply(thin_tac "F_PARSER_RTR__rules_annotate_word (parserFS_conf_stack cnR) (parserFS_conf_fixed cnR) = parserFS_conf_stack cnL")
      apply(thin_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cnL)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cnL)) = parserFS_conf_stack cnL")
      apply(thin_tac "parserFS_conf_scheduler cnR = parserFS_conf_scheduler cnL")
      apply(thin_tac "parserFS_conf_fixed cnL = []")
      apply(thin_tac "parserFS_step_relation (F_PARSER_RTR P) cnL eL cn'L")
      apply(thin_tac "F_PARSER_RTR__rule_annotate__rev eL \<in> parser_rules P")
      apply(thin_tac "rule_lpop eL \<noteq> []")
      apply(thin_tac "rule_lpush eL \<noteq> []")
      apply(thin_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L)) = parserFS_conf_stack cn'L")
      apply(thin_tac "(c, ca) \<in> F_PARSER_RTR_bisimISR P")
      apply(thin_tac "parserFS.derivation (F_PARSER_RTR P) d1L")
      apply(thin_tac "maximum_of_domain d1L n1L")
      apply(thin_tac "parserFS.derivation_initial (F_PARSER_RTR P) (derivation_append d1L (der2 cnL eL cn'L) n1L)")
      apply(thin_tac "derivation_append_fit d1L (der2 cnL eL cn'L) n1L")
      apply(thin_tac "a = pair None c")
      apply(thin_tac "d1L 0 = Some (pair None ca)")
      apply(thin_tac "ca \<in> parserFS_configurations (F_PARSER_RTR P) \<and> (\<exists>i e c. d1L i = Some (pair e c) \<and> c \<in> parserFS_marking_configurations (F_PARSER_RTR P)) \<longrightarrow> c \<in> parserFS_configurations P \<and> (\<exists>i e c. d1R i = Some (pair e c) \<and> c \<in> parserFS_marking_configurations P)")
      apply(thin_tac "derivation_append d1L (der2 cnL eL cn'L) n1L 0 = Some (pair None cb)")
      apply(thin_tac "cb \<in> parserFS_configurations (F_PARSER_RTR P)")
      apply(thin_tac "derivation_append d1L (der2 cnL eL cn'L) n1L i = Some (pair e cc)")
      apply(thin_tac "cc \<in> parserFS_marking_configurations (F_PARSER_RTR P)")
      apply(thin_tac "d1R 0 = Some (pair None c)")
      apply(clarsimp)
      apply(rename_tac cnR cn'L eL d1L d1R n1R)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
      apply(case_tac "d1R 0")
       apply(rename_tac cnR cn'L eL d1L d1R n1R)(*strict*)
       apply(clarsimp)
       apply(simp add: derivation_append_def)
      apply(rename_tac cnR cn'L eL d1L d1R n1R a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac cnR cn'L eL d1L d1R n1R a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac cnR cn'L eL d1L d1R n1R option b)(*strict*)
      apply(case_tac option)
       apply(rename_tac cnR cn'L eL d1L d1R n1R option b)(*strict*)
       prefer 2
       apply(rename_tac cnR cn'L eL d1L d1R n1R option b a)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac cnR cn'L eL d1L d1R n1R option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac cnR cn'L eL d1L d1R n1R b)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc a)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
    apply(case_tac "i\<le>n1L")
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     apply(erule impE)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
      apply(rule conjI)
       apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
       apply(simp add: parserFS.derivation_initial_def)
       apply(simp add: derivation_append_def)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
      apply(rule_tac
      x="i"
      in exI)
      apply(rule_tac
      x="e"
      in exI)
      apply(rule_tac
      x="cc"
      in exI)
      apply(simp add: derivation_append_def)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
     apply(rule_tac
      x="ia"
      in exI)
     apply(rule_tac
      x="ea"
      in exI)
     apply(rule_tac
      x="cd"
      in exI)
     apply(simp add: derivation_append_def)
     apply(subgoal_tac "ia\<le>n1R")
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
     apply(rule_tac
      M="P"
      and d="d1R"
      in parserFS.allPreMaxDomSome_prime)
       apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
       apply(force)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc ia ea "cd")(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
    apply(subgoal_tac "i=Suc n1L")
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     prefer 2
     apply(case_tac "i=Suc n1L")
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def der2_def)
     apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i e cc)(*strict*)
     apply(case_tac "i-n1L")
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i e cc)(*strict*)
      apply(clarsimp)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i e cc nat)(*strict*)
     apply(clarsimp)
     apply(case_tac nat)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i e cc nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i cc)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c cb i e cc nat nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb i e cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb e cc)(*strict*)
    apply(subgoal_tac "e=Some eL \<and> cn'L = cc")
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb e cc)(*strict*)
     prefer 2
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb e cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cb cc)(*strict*)
    apply(thin_tac "derivation_append d1L (der2 cnL eL cc) n1L (Suc n1L) = Some (pair (Some eL) cc)")
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cb cc)(*strict*)
    apply(subgoal_tac "cb=ca")
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cb cc)(*strict*)
     prefer 2
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cb cc)(*strict*)
    apply(thin_tac "derivation_append d1L (der2 cnL eL cc) n1L 0 = Some (pair None cb)")
    apply(clarsimp)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
    apply(rule_tac
      x="Suc n1R"
      in exI)
    apply(simp (no_asm) add: derivation_append_def der2_def)
    apply(rule_tac
      t="\<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cc), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cc), parserFS_conf_scheduler = parserFS_conf_scheduler cc\<rparr>"
      and s="F_PARSER_RTR__conf_annotate__rev cc"
      in ssubst)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
     apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
    apply(subgoal_tac "\<exists>e c. d1L n1L = Some (pair e c)")
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
     prefer 2
     apply(rule parserFS.some_position_has_details_before_max_dom)
       apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
    apply(subgoal_tac "parserFS_step_relation (F_PARSER_RTR P) cnL eL cc")
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
     prefer 2
     apply(rule_tac
      n="n1L"
      and d="derivation_append d1L (der2 cnL eL cc) n1L"
      in parserFS.position_change_due_to_step_relation)
       apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
       apply (rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
      apply(simp (no_asm) add: derivation_append_def der2_def)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
      apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
    apply(rule F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_marking_configurations)
        apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
      apply(simp add: parserFS_marking_configurations_def)
      apply(rule F_PARSER_RTR_preserves_empty_fixed)
        apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
        apply(force)
       apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
       apply(force)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
     apply(rule F_PARSER_RTR_preserves_nonempty_lhs)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb)(*strict*)
    apply(clarsimp)
    apply(simp add: parserFS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
    apply(subgoal_tac "parser_bottom P \<notin> set (F_PARSER_RTR__word_get_annotation (x@rule_lpush eL))")
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ rule_lpush eL)"
      and s="F_PARSER_RTR__word_get_annotation (rule_lpush eL)"
      in ssubst)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
    apply(rule F_PARSER_RTR_F_PARSER_RTR__word_get_annotation_no_parser_bottom)
      apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR eL d1L n1L d1R n1R c ca cc e cb x v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
   apply(simp add: LT_ON_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
    apply(thin_tac "x \<in> parserFS_marked_effect (F_PARSER_RTR P) (derivation_append d1L (der2 cnL eL cn'L) n1L)")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
    apply(simp add: parserFS_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule conjI)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(simp add: parserFS_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb)(*strict*)
   apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca)(*strict*)
  apply(simp add: LT_ON_def)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
  apply(case_tac "x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1L")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(thin_tac "x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) (derivation_append d1L (der2 cnL eL cn'L) n1L)")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   apply(thin_tac "x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1L")
   apply(simp add: parserFS_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(subgoal_tac "i\<le>n1R")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    prefer 2
    apply(rule_tac
      M="P"
      and d="d1R"
      in parserFS.allPreMaxDomSome_prime)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="e"
      in exI)
    apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
  apply(subgoal_tac "\<exists>c. derivation_append d1L (der2 cnL eL cn'L) n1L 0 = Some (pair None c) \<and> (\<exists>c'. (\<exists>i e. derivation_append d1L (der2 cnL eL cn'L) n1L i = Some (pair e c')) \<and> (\<exists>v. v @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c' = parserFS_conf_scheduler c \<and> x = butlast_if_match (v @ parserFS_conf_fixed c') (parser_bottom (F_PARSER_RTR P))))")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
   prefer 2
   apply(simp add: parserFS_unmarked_effect_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
  apply(thin_tac "x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) (derivation_append d1L (der2 cnL eL cn'L) n1L)")
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca x)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb c' i v e)(*strict*)
  apply(subgoal_tac "cb=ca")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb c' i v e)(*strict*)
   prefer 2
   apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
  apply(thin_tac "derivation_append d1L (der2 cnL eL cn'L) n1L 0 = Some (pair None ca)")
  apply(case_tac "i\<le>n1L")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(thin_tac "\<forall>x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1L. x \<in> parserFS_unmarked_effect P d1R")
   apply(subgoal_tac "butlast_if_match (v @ parserFS_conf_fixed c') (parser_bottom (F_PARSER_RTR P)) \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1L")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(simp add: parserFS_unmarked_effect_def)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="e"
      in exI)
    apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
  apply(subgoal_tac "i=Suc n1L")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   prefer 2
   apply(case_tac "i=Suc n1L")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-n1L")
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
    apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e nat nata)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' v e)(*strict*)
  apply(thin_tac "butlast_if_match (v @ parserFS_conf_fixed c') (parser_bottom (F_PARSER_RTR P)) \<notin> parserFS_unmarked_effect (F_PARSER_RTR P) d1L")
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' v e)(*strict*)
  apply(thin_tac "\<forall>x \<in> parserFS_unmarked_effect (F_PARSER_RTR P) d1L. x \<in> parserFS_unmarked_effect P d1R")
  apply(subgoal_tac "e=Some eL \<and> c'=cn'L")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' v e)(*strict*)
   prefer 2
   apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca c' v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(thin_tac "derivation_append d1L (der2 cnL eL cn'L) n1L (Suc n1L) = Some (pair (Some eL) cn'L)")
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(simp add: parserFS_unmarked_effect_def)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L), parserFS_conf_stack = F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack cn'L), parserFS_conf_scheduler = parserFS_conf_scheduler cn'L\<rparr>"
      in exI)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(rule conjI)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   apply(rule_tac
      x="Suc n1R"
      in exI)
   apply(rule_tac
      x="Some (F_PARSER_RTR__rule_annotate__rev eL)"
      in exI)
   apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(simp add: F_PARSER_RTR_bisimISR_def)
  apply(clarsimp)
  apply(subgoal_tac "parserFS_conf_fixed cn'L=[]")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_preserves_empty_fixed)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
     apply(force)
    apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
    apply(force)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   apply(force)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="parser_bottom (F_PARSER_RTR P)"
      and s="parser_bottom P"
      in ssubst)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   apply(simp add: F_PARSER_RTR_def Let_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(subgoal_tac "suffix v (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack cn'L))")
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca cb)(*strict*)
   apply(rule_tac
      x="cb"
      in exI)
   apply(clarsimp)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(rule_tac
      n="Suc n1L"
      in F_PARSER_RTR_fixed_suffix_of_removed)
      apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
      apply(force)
     apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
     apply(force)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(simp add: derivation_append_fit_def derivation_append_def der2_def)
  apply(rename_tac cnL cnR cn'L eL d1L n1L d1R n1R c ca v)(*strict*)
  apply(force)
  done

theorem F_PARSER_RTR_lang_sound2: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> w \<in> parserFS.marked_language (F_PARSER_RTR P)
  \<Longrightarrow> \<exists>v. (w, v) \<in> ORX \<and> v \<in> parserFS.marked_language P"
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True (F_PARSER_RTR P) P ((F_PARSER_RTR_bisimSR P)\<inverse>) ORX ((F_PARSER_RTR_bisimISR P)\<inverse>)")
   prefer 2
   apply(rule F_PARSER_RTR_step_simulation2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True (F_PARSER_RTR P) P ((F_PARSER_RTR_bisimSR P)\<inverse>) ORX ((F_PARSER_RTR_bisimISR P)\<inverse>)")
   prefer 2
   apply(rule F_PARSER_RTR_initial_simulation2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.simulation_implies_marked_effect_subset)
      apply(rule F_PARSER_RTR_preserves_valid_parser)
           apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
           apply(force)
          apply(simp add: F_PARSER_RTR_input_def)
         apply(simp add: F_PARSER_RTR_input_def)
        apply(simp add: F_PARSER_RTR_input_def)
       apply(simp add: F_PARSER_RTR_input_def)
      apply(force)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_PARSER_RTR_unmarked_language_sound2: "
  F_PARSER_RTR_input P
  \<Longrightarrow> ORX = { (o1, o2) | o1 o2. o1 = o2}
  \<Longrightarrow> w \<in> parserFS.unmarked_language (F_PARSER_RTR P)
  \<Longrightarrow> \<exists>v. (w, v) \<in> ORX \<and> v \<in> parserFS.unmarked_language P"
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True (F_PARSER_RTR P) P ((F_PARSER_RTR_bisimSR P)\<inverse>) ORX ((F_PARSER_RTR_bisimISR P)\<inverse>)")
   prefer 2
   apply(rule F_PARSER_RTR_step_simulation2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True (F_PARSER_RTR P) P ((F_PARSER_RTR_bisimSR P)\<inverse>) ORX ((F_PARSER_RTR_bisimISR P)\<inverse>)")
   prefer 2
   apply(rule F_PARSER_RTR_initial_simulation2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.simulation_implies_unmarked_effect_subset)
      apply(rule F_PARSER_RTR_preserves_valid_parser)
           apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
           apply(force)
          apply(simp add: F_PARSER_RTR_input_def)
         apply(simp add: F_PARSER_RTR_input_def)
        apply(simp add: F_PARSER_RTR_input_def)
       apply(simp add: F_PARSER_RTR_input_def)
      apply(force)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_PARSER_RTR_marked_unmarked_language_sound: "
  F_PARSER_RTR_input P
  \<Longrightarrow> parserS.unmarked_language P = parserS.unmarked_language (F_PARSER_RTR P)"
  apply(rule_tac
      t="parserS.unmarked_language P"
      and s="parserFS.unmarked_language P"
      in ssubst)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
   apply(metis parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_RTR P)"
      and s="parserFS.unmarked_language (F_PARSER_RTR P)"
      in ssubst)
   apply(subgoal_tac "valid_parser (F_PARSER_RTR P)")
    apply(metis parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(metis F_PARSER_RTR_preserves_valid_parser)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>v. (x,v) \<in> SSOR \<and> v \<in> parserFS.unmarked_language (F_PARSER_RTR P)" for SSOR)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_unmarked_language_sound1)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>v. (x,v) \<in> SSOR \<and> v \<in> parserFS.unmarked_language P" for SSOR)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_unmarked_language_sound2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_marked_lang_sound: "
  F_PARSER_RTR_input P
  \<Longrightarrow> parserS.marked_language P = parserS.marked_language (F_PARSER_RTR P)"
  apply(rule_tac
      t="parserS.marked_language P"
      and s="parserFS.marked_language P"
      in ssubst)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
   apply(metis parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply(rule_tac
      t="parserS.marked_language (F_PARSER_RTR P)"
      and s="parserFS.marked_language (F_PARSER_RTR P)"
      in ssubst)
   apply(subgoal_tac "valid_parser (F_PARSER_RTR P)")
    apply(metis parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(metis F_PARSER_RTR_preserves_valid_parser)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>v. (x,v) \<in> SSOR \<and> v \<in> parserFS.marked_language (F_PARSER_RTR P)" for SSOR)
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_lang_sound1)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>v. (x,v) \<in> SSOR \<and> v \<in> parserFS.marked_language P" for SSOR)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR_lang_sound2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR__rules_annotate_word_equal_annot: "
  w1 \<noteq> []
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word w1 v1 = x @ F_PARSER_RTR__rules_annotate_word w2 v2
  \<Longrightarrow> v1 = v2"
  apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
  done

lemma F_PARSER_RTR_reflects_steps: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS_step_relation (F_PARSER_RTR G) c e1 c1
  \<Longrightarrow> c \<in> parserFS.get_accessible_configurations (F_PARSER_RTR G)
  \<Longrightarrow> cR \<in> parserFS.get_accessible_configurations G
  \<Longrightarrow> (cR, c) \<in> F_PARSER_RTR_bisimSR G
  \<Longrightarrow> parserFS_step_relation G cR (F_PARSER_RTR__rule_annotate__rev e1) (F_PARSER_RTR__conf_annotate__rev c1)"
  apply(simp add: F_PARSER_RTR_bisimSR_def)
  apply(subgoal_tac "parserFS_conf_stack cR \<noteq> []")
   prefer 2
   apply(simp add: parserFS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac d da i ia)(*strict*)
   apply(case_tac "da ia")
    apply(rename_tac d da i ia)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac d da i ia a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d da i ia a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da i ia option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "parserFS_conf_stack cR \<noteq> []")
    apply(rename_tac d da i ia option b)(*strict*)
    apply(force)
   apply(rename_tac d da i ia option b)(*strict*)
   apply(rule_tac
      G="G"
      and d="da"
      in valid_parser_lhs_never_empty)
     apply(rename_tac d da i ia option b)(*strict*)
     apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
    apply(rename_tac d da i ia option b)(*strict*)
    apply(force)
   apply(rename_tac d da i ia option b)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e1")
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def)
   apply(simp add: parserFS_step_relation_def)
   apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
    apply(simp add: valid_bounded_parser_def valid_parser_def parser_step_labels_def)
   apply (metis F_PARSER_RTR_preserves_valid_parser)
  apply(simp (no_asm) add: parserFS_step_relation_def)
  apply(rule context_conjI)
   apply(rule F_PARSER_RTR__rule_annotate__rev_preserves_rules)
    apply(force)
   apply(simp add: parserFS_step_relation_def)
  apply(subgoal_tac "valid_parser_step_label G (F_PARSER_RTR__rule_annotate__rev e1)")
   prefer 2
   apply(subgoal_tac "valid_parser G")
    apply(simp add: valid_parser_def)
   apply(simp add: valid_bounded_parser_def valid_parser_def parser_step_labels_def F_PARSER_RTR_input_def)
  apply(subgoal_tac "e1 \<in> F_PARSER_RTR__rules_shift_new_observed G \<or> e1 \<in> F_PARSER_RTR__rules_shift_old_observed G \<or> e1 \<in> F_PARSER_RTR__rules_reduce_old_observe G \<or> e1 \<in> F_PARSER_RTR__rules_reduce_new_observe G")
   prefer 2
   apply(simp add: parserFS_step_relation_def)
   apply(simp add: F_PARSER_RTR_def Let_def )
  apply(erule disjE)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac x r)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(subgoal_tac "valid_parser G")
     apply(rename_tac x r)(*strict*)
     apply(simp add: valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
   apply(erule_tac
      P="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) = []"
      in impE)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(subgoal_tac "(\<forall>e \<in> parser_rules G. length (rule_rpop e) \<le> Suc 0)")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      in ballE)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)]) = kPrefix ka (wa @ [parser_bottom G])")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) = []")
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(rule_tac
      t="kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])"
      and s="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) [])@kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])"
      in ssubst)
      apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
      apply(force)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(force)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parserFS_conf_fixed cR = []")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_equal_annot)
      apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(force)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_not_empty)
  apply(erule disjE)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac x r)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(subgoal_tac "valid_parser G")
     apply(rename_tac x r)(*strict*)
     apply(simp add: valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
   apply(subgoal_tac "(\<forall>e \<in> parser_rules G. length (rule_rpop e) \<le> Suc 0)")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) []), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) [])\<rparr>"
      in ballE)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parserFS_conf_fixed cR = kPrefix kb (wb @ [parser_bottom G])")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_equal_annot)
      apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(force)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(rule disjI1)
   apply(subgoal_tac "kPrefix ka (wa @ [parser_bottom G])=xd")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(clarsimp)
    apply(rename_tac x r k w ka wa kb wb)(*strict*)
    apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__word_get_annotation_not_empty)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev append_Nil2)
  apply(erule disjE)
   apply(simp add: parserFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac x r)(*strict*)
   apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      in ballE)
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac x r)(*strict*)
    prefer 2
    apply(subgoal_tac "valid_parser G")
     apply(rename_tac x r)(*strict*)
     apply(simp add: valid_parser_def)
    apply(rename_tac x r)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
   apply(subgoal_tac "(\<forall>e \<in> parser_rules G. length (rule_rpop e) \<le> Suc 0)")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) []) @ rule_rpop r, rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      in ballE)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parserFS_conf_fixed cR = []")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_equal_annot)
      apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(force)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
    apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(rule conjI)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])))=kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])")
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])))"
      and s="kPrefix k (w @ [parser_bottom (F_PARSER_RTR G)])"
      in ssubst)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply (metis  F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(subgoal_tac "parser_bottom (F_PARSER_RTR G)=parser_bottom G")
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r k w ka wa kb wb)(*strict*)
     apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_not_empty)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(simp add: F_PARSER_RTR_def Let_def)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(simp add: F_PARSER_RTR_input_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac x r)(*strict*)
  apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
  apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      and P="\<lambda>x. rule_rpush x = [] \<or> rule_rpush x = rule_rpop x"
      in ballE)
   apply(rename_tac x r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x r)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      in ballE)
   apply(rename_tac x r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x r)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G r")
   apply(rename_tac x r)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser G")
    apply(rename_tac x r)(*strict*)
    apply(simp add: valid_parser_def)
   apply(rename_tac x r)(*strict*)
   apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
  apply(subgoal_tac "(\<forall>e \<in> parser_rules G. length (rule_rpop e) \<le> Suc 0)")
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   prefer 2
   apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(erule_tac
      x="\<lparr>rule_lpop = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_rpop = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpop r) (rule_rpop r)), rule_lpush = F_PARSER_RTR__rules_annotate_word_rev (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)), rule_rpush = F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r))\<rparr>"
      in ballE)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parserFS_conf_fixed cR = kPrefix kb (wb @ [parser_bottom G])")
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   prefer 2
   apply(rule F_PARSER_RTR__rules_annotate_word_equal_annot)
     apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
    apply(force)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(force)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(rule_tac
      x="F_PARSER_RTR__rules_annotate_word_rev x"
      in exI)
   apply (metis F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(rule conjI)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply(force)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (kPrefix kb (wb @ [parser_bottom G])))"
      and s="kPrefix kb (wb @ [parser_bottom G])"
      in ssubst)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply (metis F_PARSER_RTR__conf_get_annotation_def  F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(rule_tac
      t="F_PARSER_RTR__word_get_annotation (F_PARSER_RTR__rules_annotate_word (rule_lpush r) (kPrefix kb (wb @ [parser_bottom G])))"
      and s="kPrefix kb (wb @ [parser_bottom G])"
      in ssubst)
   apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
   apply (metis  F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  apply(rename_tac x r k w ka wa kb wb xd)(*strict*)
  apply(clarsimp)
  apply(metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev)
  done

lemma F_PARSER_RTR_parser_bottom_not_read: "
  valid_parser G
  \<Longrightarrow> parser_not_observes_input_terminator G
  \<Longrightarrow> parserFS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parser_bottom G \<notin> set (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c))"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_PARSER_RTR_def Let_def)
   apply(subgoal_tac "parser_bottom G \<notin>set (F_PARSER_RTR__word_get_annotation [F_PARSER_RTR__rules_annotate_element (parser_initial G) []])")
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac n e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(subgoal_tac " (e2 \<in> F_PARSER_RTR__rules_shift_new_observed G \<or> e2 \<in> F_PARSER_RTR__rules_shift_old_observed G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G)")
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_def Let_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_new_observed G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_old_observed G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)) = rule_rpop r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
    apply(simp add: parser_not_observes_input_terminator_def)
    apply(erule_tac
      x="r"
      in ballE)
     apply(rename_tac n c e1 c1 x r)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)) = rule_rpop r")
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(clarsimp)
   apply(simp add: parser_not_observes_input_terminator_def)
   apply(erule_tac
      x="r"
      in ballE)
    apply(rename_tac n c e1 c1 x r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(clarsimp)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
  apply(subgoal_tac "valid_parser_step_label G r")
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_RTR_all_reachable_configurations_only_tail_marked_FS: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c)) = parserFS_conf_stack c"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(simp add: parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_PARSER_RTR_def)
   apply(simp add: Let_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac n e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR G) e2")
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ rule_lpush e2) = F_PARSER_RTR__word_get_annotation (rule_lpush e2)")
    apply(rename_tac n c e1 e2 c1 x v k w)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(rename_tac n c e1 e2 c1 x v k w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
   apply(case_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2)")
    apply(rename_tac n c e1 e2 c1 x v k w)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w a list)(*strict*)
   apply(rule_tac
      t="(case map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2) of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (rule_lpush e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))])"
      and s="map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (rule_lpush e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2))]"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x v k w a list)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2) = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x v k w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w a list)(*strict*)
   apply(thin_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpush e2)=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w w' x')(*strict*)
   apply(case_tac "rule_lpush e2")
    apply(rename_tac n c e1 e2 c1 x v k w w' x')(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpush e2 = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x v k w w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w w' x' a list)(*strict*)
   apply(thin_tac "rule_lpush e2=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def)
   apply(case_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2)")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
   apply(subgoal_tac "map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (x @ rule_lpop e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))] = x @ rule_lpop e2")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
   apply(thin_tac "(case map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2) of [] \<Rightarrow> [] | a' # w' \<Rightarrow> map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a (F_PARSER_RTR__word_get_annotation (x @ rule_lpop e2))) [last (map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2))]) = x @ rule_lpop e2")
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2) = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b a list)(*strict*)
   apply(thin_tac "map (\<lambda>(a, b). a) x @ map (\<lambda>(a, b). a) (rule_lpop e2)=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b w' x'stack)(*strict*)
   apply(case_tac "rule_lpop e2")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b w' x'stack)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b w' x'stack a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop e2 = w' @ [x']")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b w' x'stack a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b w' x'stack a list)(*strict*)
   apply(thin_tac "rule_lpop e2=a#list")
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev(rule_lpush e2)) (F_PARSER_RTR__word_get_annotation(rule_lpush e2)) = rule_lpush e2")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_all_rules_only_tail_marked)
     apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="w'stack"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) []"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule map_idI_prime)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba a bb)(*strict*)
    apply(rule F_PARSER_RTR__rules_annotate_word_F_PARSER_RTR__rules_annotate_word_rev_annotation_empty)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) [] @ (F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev [(x', b)]) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))) = w'stack @ [(x', b)]")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    apply(subgoal_tac "length (F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) []) = length w'stack")
     apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
     apply (simp add: F_PARSER_RTR__rules_annotate_word_length)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_word_def F_PARSER_RTR__rules_annotate_word_rev_def)
    apply(rule_tac f="length" in cong)
     apply(force)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)]) = F_PARSER_RTR__rules_annotate_word_rev w'stack @ (F_PARSER_RTR__rules_annotate_word_rev [(x', b)])")
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__rules_annotate_word_rev_distrib_append)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule_tac
      P="\<lambda>X. F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev w'stack) [] @ F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev [(x', b)]) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))=X"
      and t="w'stack @ [(x', b)]"
      and s="F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)])) (F_PARSER_RTR__word_get_annotation (w'stack @ [(x', b)]))"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule sym)
   apply(rule_tac
      t="F_PARSER_RTR__rules_annotate_word_rev (w'stack @ [(x', b)])"
      and s="F_PARSER_RTR__rules_annotate_word_rev w'stack @ F_PARSER_RTR__rules_annotate_word_rev [(x', b)]"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 x v k w x' w'stack b x'stack w'event ba)(*strict*)
   apply(rule F_PARSER_RTR__rules_annotate_word_pullout)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_rev_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply (metis F_PARSER_RTR_input_def F_PARSER_RTR_preserves_valid_parser )
  done

lemma F_PARSER_RTR_at_most_1_in_lookahead: "
  valid_bounded_parser G (Suc 0)
  \<Longrightarrow> parserFS.derivation_initial (F_PARSER_RTR G) d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> length (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c)) \<le> Suc 0"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: F_PARSER_RTR_def Let_def)
   apply(simp add: F_PARSER_RTR__word_get_annotation_def F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac n e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation (F_PARSER_RTR G) c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(subgoal_tac " (e2 \<in> F_PARSER_RTR__rules_shift_new_observed G \<or> e2 \<in> F_PARSER_RTR__rules_shift_old_observed G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G)")
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_def Let_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_new_observed G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_old_observed G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) []) = []")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G"
      in disjE)
   apply(rename_tac n c e1 e2 c1 x v)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)) = rule_rpop r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(clarsimp)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac n c e1 c1 x r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1 x v)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(subgoal_tac "F_PARSER_RTR__word_get_annotation (x @ F_PARSER_RTR__rules_annotate_word (rule_lpush r) (rule_rpop r)) = rule_rpop r")
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_bounded_parser_def)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(rule F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append)
  apply(subgoal_tac "valid_parser_step_label G r")
   apply(rename_tac n c e1 c1 x r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac n c e1 c1 x r)(*strict*)
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  done

theorem F_PARSER_RTR_is_forward_edge_deterministic_accessible: "
  F_PARSER_RTR_input G
  \<Longrightarrow> parserFS.is_forward_edge_deterministic_accessible (F_PARSER_RTR G)"
  apply(simp add: parserFS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: parserFS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(subgoal_tac "F_PARSER_RTR__rule_annotate__rev e1=F_PARSER_RTR__rule_annotate__rev e2")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(subgoal_tac "e1 \<in> parser_rules (F_PARSER_RTR G)")
    apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
    apply(subgoal_tac "e2 \<in> parser_rules (F_PARSER_RTR G)")
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(subgoal_tac "(e1 \<in> F_PARSER_RTR__rules_shift_new_observed G \<or> e1 \<in> F_PARSER_RTR__rules_shift_old_observed G \<or> e1 \<in> F_PARSER_RTR__rules_reduce_old_observe G \<or> e1 \<in> F_PARSER_RTR__rules_reduce_new_observe G) \<and> (e2 \<in> F_PARSER_RTR__rules_shift_new_observed G \<or> e2 \<in> F_PARSER_RTR__rules_shift_old_observed G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_old_observe G \<or> e2 \<in> F_PARSER_RTR__rules_reduce_new_observe G)")
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      prefer 2
      apply(simp add: F_PARSER_RTR_def Let_def)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_shift_new_observed G"
      in disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(rule F_PARSER_RTR__rule_annotate__rev_inj_S1)
         apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        apply(simp add: valid_parser_step_label_def)
        apply(clarsimp)
        apply(rename_tac c c1 c2 d i x xa r ra k w)(*strict*)
        apply (metis  F_PARSER_RTR_input_rpop_single F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev not_Cons_self2)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G ra")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
       apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil2 eq_Nil_appendI)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev  eq_Nil_appendI)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_new_observed G"
      in disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        apply(simp add: valid_parser_step_label_def)
        apply(clarsimp)
        apply(rename_tac c c1 c2 d i x xa r ra k w)(*strict*)
        apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR_input_rpop_single F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev not_Cons_self2)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G ra")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
       apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev append_Nil2 eq_Nil_appendI)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev  eq_Nil_appendI)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_shift_old_observed G"
      in disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(rule F_PARSER_RTR__rule_annotate__rev_inj_S2)
         apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G ra")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
       apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev  eq_Nil_appendI)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev )
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(erule_tac
      P="e2 \<in> F_PARSER_RTR__rules_shift_old_observed G"
      in disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G ra")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
       apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev  eq_Nil_appendI)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(erule_tac
      P="e1 \<in> F_PARSER_RTR__rules_reduce_old_observe G"
      in disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(erule disjE)
       apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
       apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
       apply(clarsimp)
       apply(case_tac e1)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
       apply(case_tac e2)
       apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
       apply(simp add: parserFS_step_relation_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
       apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
       apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G r")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G ra")
        apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
        prefer 2
        apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
       apply (metis F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR_input_rpop_single F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev not_Cons_self2)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(erule disjE)
      apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
      apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
      apply(clarsimp)
      apply(case_tac e1)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
      apply(case_tac e2)
      apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
      apply(simp add: parserFS_step_relation_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
      apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
      apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G r")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G ra")
       apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
       prefer 2
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
      apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR_input_rpop_single F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev not_Cons_self2)
     apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
     apply(simp add: F_PARSER_RTR__rule_annotate__rev_def)
     apply(clarsimp)
     apply(case_tac e1)
     apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
     apply(case_tac e2)
     apply(rename_tac c c1 c2 e1 e2 d i rule_lpopa rule_rpopa rule_lpusha rule_rpush rule_lpopaa rule_rpopaa rule_lpushaa rule_rpusha)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 d i rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
     apply(simp add: parserFS_step_relation_def)
     apply(clarsimp)
     apply(rename_tac c c1 c2 d i rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha x xa v va)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def F_PARSER_RTR__rules_shift_new_observed_def F_PARSER_RTR__rules_reduce_new_observe_def F_PARSER_RTR__rules_reduce_old_observe_def)
     apply(rename_tac c c1 c2 d i rule_lpopa rule_lpusha rule_rpusha rule_lpopaa rule_lpushaa rule_rpushaa x xa v va)(*strict*)
     apply(clarsimp)
     apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
     apply(subgoal_tac "valid_parser_step_label G r")
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      prefer 2
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
     apply(subgoal_tac "valid_parser_step_label G ra")
      apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
      prefer 2
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
     apply(rename_tac c c1 c2 d i x xa r ra)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac c c1 c2 d i x xa r ra k w ka wa)(*strict*)
     apply (metis F_PARSER_RTR__conf_get_annotation_def F_PARSER_RTR_input_rpop_single F_PARSER_RTR__word_get_annotation_F_PARSER_RTR__rules_annotate_word_rev_append F_PARSER_RTR__rules_annotate_word_rev_F_PARSER_RTR__rules_annotate_word_rev )
    apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
    apply(simp add: parserFS_step_relation_def)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(subgoal_tac "\<exists>dL c0L nL e. parserFS.derivation_initial (F_PARSER_RTR G) dL \<and> maximum_of_domain dL nL \<and> dL 0 = Some (pair None c0L) \<and> dL nL = Some (pair e c)")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 d i ca)(*strict*)
    apply(rule_tac
      x="derivation_take d i"
      in exI)
    apply(rule conjI)
     apply(rename_tac c c1 c2 e1 e2 d i ca)(*strict*)
     apply(rule parserFS.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i ca)(*strict*)
    apply(rule_tac
      x="ca"
      in exI)
    apply(rule_tac
      x="i"
      in exI)
    apply(simp add: get_configuration_def)
    apply(case_tac "d i")
     apply(rename_tac c c1 c2 e1 e2 d i ca)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i ca a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac c c1 c2 e1 e2 d i ca a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 d i ca option)(*strict*)
    apply(rule conjI)
     apply(rename_tac c c1 c2 e1 e2 d i ca option)(*strict*)
     apply(rule maximum_of_domain_derivation_take)
     apply(simp add: get_configuration_def)
    apply(rename_tac c c1 c2 e1 e2 d i ca option)(*strict*)
    apply(case_tac "d i")
     apply(rename_tac c c1 c2 e1 e2 d i ca option)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i ca option a)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply (metis parserFS.derivation_initial_is_derivation parserFS.some_position_has_details_at_0)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(thin_tac "parserFS.derivation_initial (F_PARSER_RTR G) d")
  apply(thin_tac "get_configuration (d i) = Some c")
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
  apply(subgoal_tac "(c0L, F_PARSER_RTR__conf_annotate__rev c0L) \<in> (F_PARSER_RTR_bisimSR G)\<inverse>")
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_RTR_bisimSR_def)
   apply(subgoal_tac "parserFS_conf_fixed c0L = []")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_never_fixed)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "c0L \<in> parserFS_configurations (F_PARSER_RTR G)")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(subgoal_tac "valid_parser (F_PARSER_RTR G)")
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
    apply(rule F_PARSER_RTR_preserves_valid_parser)
         apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<notin> set (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c0L))")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_parser_bottom_not_read)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(subgoal_tac "F_PARSER_RTR__conf_annotate__rev c0L \<in> parserFS_configurations G")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR__conf_annotate__rev_preserves_parserFS_configurations)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(rule_tac
      d="dL"
      in valid_parser_lhs_never_empty)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(simp add: F_PARSER_RTR_input_def)
      apply(rule F_PARSER_RTR_preserves_valid_parser)
           apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(rule conjI)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(simp add: F_PARSER_RTR__conf_annotate__rev_def)
   apply(subgoal_tac "F_PARSER_RTR__rules_annotate_word (F_PARSER_RTR__rules_annotate_word_rev (parserFS_conf_stack c0L)) (F_PARSER_RTR__word_get_annotation (parserFS_conf_stack c0L)) = parserFS_conf_stack c0L")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_all_reachable_configurations_only_tail_marked_FS)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(clarsimp)
   apply(rule F_PARSER_RTR_at_most_1_in_lookahead)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
  apply(subgoal_tac "\<exists>dR f. parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.stronger_simulating_der True True False (F_PARSER_RTR G) G ((F_PARSER_RTR_bisimSR G)\<inverse>) {(o1,o2)| o1 o2. o1=(o2::'b list)} ((F_PARSER_RTR_bisimISR G)\<inverse>) dL nL f dR")
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   prefer 2
   apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation True True True (F_PARSER_RTR G) G ((F_PARSER_RTR_bisimSR G)\<inverse>) {(o1,o2)| o1 o2. o1=(o2::'b list)} ((F_PARSER_RTR_bisimISR G)\<inverse>)")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_step_simulation2)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(subgoal_tac "parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation True True (F_PARSER_RTR G) G ((F_PARSER_RTR_bisimSR G)\<inverse>) {(o1,o2)| o1 o2. o1=(o2::'b list)} ((F_PARSER_RTR_bisimISR G)\<inverse>)")
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_initial_simulation2)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(rule_tac
      ?c0R.0="F_PARSER_RTR__conf_annotate__rev c0L"
      in parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.generate_simulating_derivation2)
          apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
          apply(simp add: F_PARSER_RTR_input_def)
          apply(rule F_PARSER_RTR_preserves_valid_parser)
               apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
               apply(force)
              apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
              apply(force)
             apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
             apply(force)
            apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
            apply(force)
           apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
           apply(force)
          apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
         apply(simp add: F_PARSER_RTR_input_def)
         apply(simp add: valid_bounded_parser_def)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.initial_simulation_weakening)
          apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(rule parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.step_simulation_weakening)
          apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
          apply(force)
         apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
         apply(force)
        apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
        apply(force)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f)(*strict*)
  apply(simp add: parserFS_parserFS_ATS_Simulation_Configuration_Weak_Plain.stronger_simulating_der_def)
  apply(clarsimp)
  apply(erule_tac
      x="nL"
      in allE)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR)(*strict*)
  apply(thin_tac "LT_ON (Collect (\<lambda>uu. (\<exists>o1. uu = (o1, o1)))) (parserFS_marked_effect (F_PARSER_RTR G) (derivation_take dL nL)) (parserFS_marked_effect G (derivation_take dR (f nL))) ")
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR)(*strict*)
  apply(thin_tac "parserFS_marking_condition (F_PARSER_RTR G) (derivation_take dL nL) \<longrightarrow> parserFS_marking_condition G (derivation_take dR (f nL))")
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "dR 0")
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(subgoal_tac "parserFS.is_forward_edge_deterministic_accessible G")
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in parserS_vs_parserFS.preserve_FEdetermR1)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   apply(simp add: F_PARSER_RTR_input_def)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(simp add: parserFS.is_forward_edge_deterministic_accessible_def)
  apply(subgoal_tac "cR \<in> parserFS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   prefer 2
   apply(simp add: parserFS.get_accessible_configurations_def)
   apply(rule_tac
      x="dR"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="f nL"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(erule_tac
      x="cR"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(erule_tac
      x="F_PARSER_RTR__conf_annotate__rev c1"
      in allE)
  apply(erule_tac
      x="F_PARSER_RTR__conf_annotate__rev c2"
      in allE)
  apply(erule_tac
      x="F_PARSER_RTR__rule_annotate__rev e1"
      in allE)
  apply(erule_tac
      x="F_PARSER_RTR__rule_annotate__rev e2"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(rule conjI)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   apply(rule F_PARSER_RTR_reflects_steps)
       apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
     apply(simp add: parserFS.get_accessible_configurations_def)
     apply(clarsimp)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b d i)(*strict*)
     apply(rule_tac
      x="dL"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="nL"
      in exI)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(rule F_PARSER_RTR_reflects_steps)
      apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
    apply(simp add: parserFS.get_accessible_configurations_def)
    apply(clarsimp)
    apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b d i)(*strict*)
    apply(rule_tac
      x="dL"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="nL"
      in exI)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 dL c0L nL e dR f eR cR option b)(*strict*)
  apply(force)
  done

lemma F_PARSER_RTR_determ_sound: "
  F_PARSER_RTR_input P
  \<Longrightarrow> parserS.Nonblockingness_linear_DB P
  \<Longrightarrow> parserS.Nonblockingness_linear_DB (F_PARSER_RTR P)"
  apply(subgoal_tac "valid_parser (F_PARSER_RTR P)")
   prefer 2
   apply(simp add: F_PARSER_RTR_input_def)
   apply (metis F_PARSER_RTR_preserves_valid_parser)
  apply(rule parser_Nonblockingness_linear_restricted_DB_to_Nonblockingness_linear_DB_with_not_parserS_entire_input_observed)
    apply(force)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: parserS_entire_input_observed_def)
   apply(clarsimp)
   apply(rename_tac c d e n)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d n = 0")
    apply(rename_tac c d e n)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_parser_fixed_input_length_recN)
      apply(rename_tac c d e n)(*strict*)
      apply(simp add: valid_bounded_parser_def)
      apply(force)
     apply(rename_tac c d e n)(*strict*)
     apply(force)
    apply(rename_tac c d e n)(*strict*)
    apply(force)
   apply(rename_tac c d e n)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e \<in> parser_rules (F_PARSER_RTR P). parser_bottom (F_PARSER_RTR P) \<in> set (rule_rpop e)")
    apply(rename_tac c d e n)(*strict*)
    prefer 2
    apply(rule parser_existence_of_removing_rule)
       apply(rename_tac c d e n)(*strict*)
       apply(force)
      apply(rename_tac c d e n)(*strict*)
      apply(force)
     apply(rename_tac c d e n)(*strict*)
     apply(force)
    apply(rename_tac c d e n)(*strict*)
    apply(simp add: parserS_get_unfixed_scheduler_DB_def parserS_get_scheduler_def get_configuration_def suffix_def)
   apply(rename_tac c d e n)(*strict*)
   apply(subgoal_tac "parser_not_observes_input_terminator (F_PARSER_RTR P)")
    apply(rename_tac c d e n)(*strict*)
    prefer 2
    apply(rule F_PARSER_RTR_preserves_parser_not_observes_input_terminator)
     apply(rename_tac c d e n)(*strict*)
     apply(simp add: valid_bounded_parser_def)
    apply(rename_tac c d e n)(*strict*)
    apply(force)
   apply(rename_tac c d e n)(*strict*)
   apply(simp add: parser_not_observes_input_terminator_def)
   apply(clarsimp)
   apply(rename_tac c d e n ea)(*strict*)
   apply(subgoal_tac "valid_parser_step_label (F_PARSER_RTR P) ea")
    apply(rename_tac c d e n ea)(*strict*)
    apply(erule_tac
      x="ea"
      in ballE)
     apply(rename_tac c d e n ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c d e n ea)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac c d e n ea k w xa)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac c d e n ea k w xa)(*strict*)
     apply(clarsimp)
     apply (metis in_set_takeD not_in_diff)
    apply(rename_tac c d e n ea k w xa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d e n ea k w xa nat x)(*strict*)
    apply (metis F_PARSER_RTR_makes_parser_no_top_rules parser_no_top_rules_def Suc_length Suc_neq_Zero list.size(3))
   apply(rename_tac c d e n ea)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rule parserS.AX_BF_LinDBRest_DetR_LaOp)
    apply(force)
   apply(simp add: parserS.is_forward_deterministic_accessible_def)
   apply(rule conjI)
    apply (metis parserS.is_forward_target_deterministic_implies_is_forward_target_deterministic_accessible parserS_is_forward_target_deterministic)
   apply(rule_tac
      ?G2.0="F_PARSER_RTR P"
      in parserS_vs_parserFS.preserve_FEdetermR2)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
   apply(rule F_PARSER_RTR_is_forward_edge_deterministic_accessible)
   apply(force)
  apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_RTR P)"
      and s="parserS.unmarked_language P"
      in ssubst)
   apply(metis F_PARSER_RTR_marked_unmarked_language_sound)
  apply(rule_tac
      t="parserS.marked_language (F_PARSER_RTR P)"
      and s="parserS.marked_language P"
      in ssubst)
   apply(metis F_PARSER_RTR_marked_lang_sound)
  apply(rule parserS.AX_BF_LinDB_OpLa)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def)
  apply(force)
  done

lemma epda_no_empty_steps_from_marking_states: "
  F_PARSER_RTR_input G
  \<Longrightarrow> G' = F_PARSER_RTR G
  \<Longrightarrow> e \<in> parser_rules G'
  \<Longrightarrow> last (rule_lpop e) \<in> parser_marking G'
  \<Longrightarrow> rule_rpop e \<noteq> []"
  apply(simp add: F_PARSER_RTR_def Let_def)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(thin_tac "F_PARSER_RTR__rules_annotate_element a [] = F_PARSER_RTR__rules_annotate_element (parser_initial G) [] \<or> (\<exists>r \<in> F_PARSER_RTR__rules_shift_new_observed G \<union> F_PARSER_RTR__rules_shift_old_observed G \<union> F_PARSER_RTR__rules_reduce_old_observe G \<union> F_PARSER_RTR__rules_reduce_new_observe G. F_PARSER_RTR__rules_annotate_element a [] \<in> set (rule_lpop r) \<or> F_PARSER_RTR__rules_annotate_element a [] \<in> set (rule_lpush r))")
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_new_observed_def)
   apply(clarsimp)
   apply(rename_tac a r)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a r)(*strict*)
    prefer 2
    apply(rule_tac
      e="r"
      in F_PARSER_RTR_input_rpop_single)
     apply(rename_tac a r)(*strict*)
     apply(force)
    apply(rename_tac a r)(*strict*)
    apply(force)
   apply(rename_tac a r)(*strict*)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_shift_old_observed_def)
   apply(clarsimp)
   apply(rename_tac a r)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a r)(*strict*)
    prefer 2
    apply(rule_tac
      e="r"
      in F_PARSER_RTR_input_rpop_single)
     apply(rename_tac a r)(*strict*)
     apply(force)
    apply(rename_tac a r)(*strict*)
    apply(force)
   apply(rename_tac a r)(*strict*)
   apply(clarsimp)
   apply(rename_tac a r x)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
   apply(rule_tac
      xs="rule_lpop r"
      in rev_cases)
    apply(rename_tac a r x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
    apply(clarsimp)
    apply(erule_tac
      x="r"
      and P="\<lambda>r. valid_parser_step_label G r"
      in ballE)
     apply(rename_tac a r x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac a r x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac a r x ys y)(*strict*)
   apply(subgoal_tac "last (map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (rule_lpop r)) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a [x]) [last (rule_lpop r)]) = (parser_initial G, [])")
    apply(rename_tac a r x ys y)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(case_tac ys)
     apply(rename_tac a r x ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac a r x y)(*strict*)
     apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
    apply(rename_tac a r x ys y aa list)(*strict*)
    apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
   apply(rename_tac a r x ys y)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  apply(rename_tac a)(*strict*)
  apply(erule disjE)
   apply(rename_tac a)(*strict*)
   apply(simp add: F_PARSER_RTR__rules_reduce_old_observe_def)
   apply(clarsimp)
   apply(rename_tac a r)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac a r)(*strict*)
    prefer 2
    apply(rule_tac
      e="r"
      in F_PARSER_RTR_input_rpop_single)
     apply(rename_tac a r)(*strict*)
     apply(force)
    apply(rename_tac a r)(*strict*)
    apply(force)
   apply(rename_tac a r)(*strict*)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_reduce_new_observe_def)
  apply(clarsimp)
  apply(rename_tac a r)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a r)(*strict*)
   prefer 2
   apply(rule_tac
      e="r"
      in F_PARSER_RTR_input_rpop_single)
    apply(rename_tac a r)(*strict*)
    apply(force)
   apply(rename_tac a r)(*strict*)
   apply(force)
  apply(rename_tac a r)(*strict*)
  apply(clarsimp)
  apply(rename_tac a r x)(*strict*)
  apply(simp add: F_PARSER_RTR__rules_annotate_word_def)
  apply(rule_tac
      xs="rule_lpop r"
      in rev_cases)
   apply(rename_tac a r x)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_RTR_input_def valid_bounded_parser_def valid_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="r"
      and P="\<lambda>r. valid_parser_step_label G r"
      in ballE)
    apply(rename_tac a r x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a r x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac a r x ys y)(*strict*)
  apply(subgoal_tac "last (map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a []) (butlast (rule_lpop r)) @ map (\<lambda>a. F_PARSER_RTR__rules_annotate_element a [x]) [last (rule_lpop r)]) = F_PARSER_RTR__rules_annotate_element a []")
   apply(rename_tac a r x ys y)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(case_tac ys)
    apply(rename_tac a r x ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac a r x ys y aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a r x ys y)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_RTR__rules_annotate_element_def)
  done

theorem F_PARSER_RTR_epda_no_empty_steps_from_marking_states: "
  F_PARSER_RTR_input G
  \<Longrightarrow> G' = F_PARSER_RTR G
  \<Longrightarrow> parser_no_empty_steps_from_marking_states G'"
  apply(simp add: parser_no_empty_steps_from_marking_states_def)
  apply(rule allI)
  apply(rename_tac e)(*strict*)
  apply(rule impI)+
  apply(rule epda_no_empty_steps_from_marking_states)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

definition F_PARSER_RTR__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_RTR__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_not_observes_input_terminator G
  \<and> (\<forall>r \<in> parser_rules G. rule_rpop r \<noteq> [])"

definition F_PARSER_RTR__SpecOutput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_RTR__SpecOutput Gi Go \<equiv>
  valid_bounded_parser Go (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible Go
  \<and> parser_not_observes_input_terminator Go
  \<and> parser_no_top_rules Go
  \<and> parserS.marked_language Gi = parserS.marked_language Go
  \<and> nonblockingness_language (parserS.unmarked_language Go) (parserS.marked_language Go)
  \<and> parser_no_empty_steps_from_marking_states Go"

theorem F_PARSER_RTR__SOUND: "
  F_PARSER_RTR__SpecInput G
  \<Longrightarrow> F_PARSER_RTR__SpecOutput G (F_PARSER_RTR G)"
  apply(simp add: F_PARSER_RTR__SpecOutput_def F_PARSER_RTR__SpecInput_def)
  apply(clarsimp)
  apply(subgoal_tac "parserS.is_forward_edge_deterministic_accessible G")
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in parserS_vs_parserFS.preserve_FEdetermR2)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_PARSER_RTR_preserves_PARSERl)
        apply(force)
       apply(rule valid_bounded_parser_preserves_only_pop_or_top)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_PARSER_RTR_is_forward_edge_deterministic_accessible)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(rule valid_bounded_parser_preserves_only_pop_or_top)
   apply(force)
  apply(rule context_conjI)
   apply (metis F_PARSER_RTR_preserves_parser_not_observes_input_terminator valid_bounded_parser_vs_valid_parser)
  apply(rule context_conjI)
   apply (metis F_PARSER_RTR_makes_parser_no_top_rules)
  apply(rule context_conjI)
   apply(rule F_PARSER_RTR_marked_lang_sound)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(rule valid_bounded_parser_preserves_only_pop_or_top)
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_RTR G)"
      and s="parserS.unmarked_language G"
      in ssubst)
    prefer 2
    apply(force)
   apply(rule sym)
   apply(rule F_PARSER_RTR_marked_unmarked_language_sound)
   apply(simp add: F_PARSER_RTR_input_def)
   apply(rule valid_bounded_parser_preserves_only_pop_or_top)
   apply(force)
  apply (metis F_PARSER_RTR_input_def valid_bounded_parser_preserves_only_pop_or_top F_PARSER_RTR_epda_no_empty_steps_from_marking_states )
  done

end
