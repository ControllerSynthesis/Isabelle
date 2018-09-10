section {*Derivations\_Basics*}
theory
  Derivations_Basics

imports
  PRJ_06_01__ENTRY

begin

declare [[ hypsubst_thin = false ]]
datatype ('label,'conf) derivation_configuration = pair "'label option" "'conf"
declare [[ hypsubst_thin = true ]]

type_synonym ('label,'conf) derivation = "(nat \<Rightarrow> ('label,'conf)derivation_configuration option)"

lemma equal_derivation_conf_coincide: "
  f = g
  \<Longrightarrow> f x = Some (pair e1 a)
  \<Longrightarrow> g x = Some (pair e2 b)
  \<Longrightarrow> a = b"
  apply(force)
  done

definition maximum_of_domain :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "maximum_of_domain f n \<equiv>
  f n \<noteq> None
  \<and> f (Suc n) = None"

definition get_label :: "
  (('label,'conf) derivation_configuration) option
  \<Rightarrow> 'label option"
  where
    "get_label x \<equiv>
  case x of
  None \<Rightarrow> None
  | (Some (pair e c)) \<Rightarrow> e"

definition get_configuration :: "
  (('label,'conf)derivation_configuration) option
  \<Rightarrow> 'conf option"
  where
    "get_configuration x \<equiv>
  case x of
  None \<Rightarrow> None
  | (Some (pair e c)) \<Rightarrow> Some c"

definition get_labels :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> 'label option list"
  where
    "get_labels f n \<equiv>
  map (\<lambda>i. get_label (f i)) (nat_seq (Suc 0) n)"

definition get_configurations :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> 'conf option list"
  where
    "get_configurations f n \<equiv>
  map (\<lambda>i. get_configuration (f i)) (nat_seq 0 n)"

definition derivation_map :: "
  ('label,'confA)derivation
  \<Rightarrow> ('confA \<Rightarrow> 'confB)
  \<Rightarrow> ('label,'confB)derivation"
  where
    "derivation_map f C \<equiv>
  \<lambda>n.
  case f n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow> Some (pair e (C c))"

definition derivation_append :: "
  ('label,'conf)derivation
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf)derivation"
  where
    "derivation_append f g fn \<equiv>
  \<lambda>x.
  if x \<le> fn
  then f x
  else g (x - fn)"

definition derivation_append_fit :: "
  ('label,'conf)derivation
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "derivation_append_fit f g fn \<equiv>
  case f fn of
  Some (pair e c) \<Rightarrow>
    (case g 0 of
    Some (pair None c') \<Rightarrow> c = c'
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False"

definition derivation_append_fit_ALT :: "
  ('label,'conf)derivation
  \<Rightarrow> ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "derivation_append_fit_ALT f g fn \<equiv>
  get_configuration (f fn) = get_configuration (g 0)"

definition derivation_drop :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf)derivation"
  where
    "derivation_drop f m \<equiv>
  \<lambda>n.
  if n = 0
  then (case f m of
        Some (pair e c) \<Rightarrow> Some (pair None c))
  else f (n + m)"

definition derivation_take :: "
  ('label,'conf)derivation
  \<Rightarrow> nat
  \<Rightarrow> ('label,'conf)derivation"
  where
    "derivation_take f m \<equiv>
  \<lambda>n.
  if n \<le> m
  then f n
  else None"

lemma derivation_drop_id: "
  d 0 = Some (pair None c)
  \<Longrightarrow> derivation_drop d 0 = d"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_drop_def)
  done

lemma get_labelsEmpty: "
  get_labels dp 0 = []"
  apply(simp add: get_labels_def)
  apply(rule nat_seqEmpty)
  apply(auto)
  done

lemma get_labelsLength: "
  n>0
  \<Longrightarrow> \<pi> = get_labels d n
  \<Longrightarrow> length \<pi> = n"
  apply(simp add: get_labels_def)
  apply(rule nat_seq_length_Suc0)
   apply(blast)+
  done

lemma get_labels_length: "
  w=get_labels d n
  \<Longrightarrow> length w = n"
  apply(case_tac n)
   apply(clarsimp)
   apply(rule get_labelsEmpty)
  apply(rename_tac nat)(*strict*)
  apply(rule get_labelsLength)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma get_labels_None: "
  d (Suc i)=None
  \<Longrightarrow> i<n
  \<Longrightarrow> get_labels d n ! i = None"
  apply(subgoal_tac "length (nat_seq (Suc 0) n)=n-(Suc 0)+1")
   prefer 2
   apply(rule nat_seq_length)
   apply(force)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(rule_tac
      t="map (\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n) ! i"
      and s="(\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) ((nat_seq (Suc 0) n) ! i)"
      in ssubst)
   apply(rule nth_map)
   apply(force)
  apply(subgoal_tac "(nat_seq (Suc 0) n ! i) = (Suc 0)+i")
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma get_labels_Not_None: "
  d (Suc i)=Some (pair e b)
  \<Longrightarrow> i<n
  \<Longrightarrow> get_labels d n ! i = e"
  apply(subgoal_tac "length (nat_seq (Suc 0) n)=n-(Suc 0)+1")
   prefer 2
   apply(rule nat_seq_length)
   apply(force)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(rule_tac
      t="map (\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n) ! i"
      and s="(\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) ((nat_seq (Suc 0) n) ! i)"
      in ssubst)
   apply(rule nth_map)
   apply(force)
  apply(subgoal_tac "(nat_seq (Suc 0) n ! i) = (Suc 0)+i")
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma derivation_skip_get_labels: "
  d'=derivation_drop d m
  \<Longrightarrow> m\<le>n
  \<Longrightarrow> get_labels d n = (get_labels d m)@(get_labels d' (n-m))"
  apply(simp add: derivation_drop_def)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) n)=n+1-(Suc 0)")
   prefer 2
   apply(case_tac "n")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="n + 1 - Suc 0"
      and s="n - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(subgoal_tac "length (nat_seq (Suc 0) m)=m+1-(Suc 0)")
   prefer 2
   apply(case_tac "m")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="m + 1 - Suc 0"
      and s="m - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n-m))=(n-m)+1-(Suc 0)")
   prefer 2
   apply(case_tac "n-m")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="(n-m) + 1 - Suc 0"
      and s="(n-m) - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq (Suc 0) n ! i"
      and s="(Suc 0)+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i<m")
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(map (\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) m) @ map (\<lambda>i. case if i = 0 then case d m of Some (pair e c) \<Rightarrow> Some (pair None c) else d (i + m) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) (n - m))) ! i"
      and s="map (\<lambda>i. case d i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) m)!i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq (Suc 0) m ! i"
      and s="(Suc 0)+i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i)) (nat_seq (Suc 0) m) @ map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (if i = 0 then case_option undefined (case_derivation_configuration (\<lambda>e c. Some (pair None c))) (d m) else d (i + m))) (nat_seq (Suc 0) (n - m))) ! i"
      and s="(map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (if i = 0 then case_option undefined (case_derivation_configuration (\<lambda>e c. Some (pair None c))) (d m) else d (i + m))) (nat_seq (Suc 0) (n - m))) ! (i-(length(map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i)) (nat_seq (Suc 0) m))))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "n-m")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) (n-m) ! (i-m)"
      and s="(Suc 0)+(i-m)"
      in ssubst)
   apply(rename_tac i nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  done

lemma derivation_concat_get_labels: "
  n\<le>n1
  \<Longrightarrow> d=derivation_append d1 d2 n
  \<Longrightarrow> get_labels d (n+n2) = (get_labels d1 n)@(get_labels d2 n2)"
  apply(simp add: derivation_append_def)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n+n2))=(n+n2)+1-(Suc 0)")
   prefer 2
   apply(case_tac "n+n2")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="n + n2 + 1 - Suc 0"
      and s="n + n2 - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) n)=n+1-(Suc 0)")
   prefer 2
   apply(case_tac "n")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="n + 1 - Suc 0"
      and s="n - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) n2)=n2+1-(Suc 0)")
   prefer 2
   apply(case_tac "n2")
    apply(clarsimp)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="n2 + 1 - Suc 0"
      and s="n2 - Suc 0 + 1"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_length)
   apply(force)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "i<n+n2")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(thin_tac "i < length (map (\<lambda>i. case if i \<le> n then d1 i else d2 (i - n) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) (n + n2)))")
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="map (\<lambda>i. case if i \<le> n then d1 i else d2 (i - n) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) (n + n2)) ! i"
      and s="(\<lambda>i. case if i \<le> n then d1 i else d2 (i - n) of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) (n + n2) !i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) (n + n2) ! i"
      and s="(Suc 0)+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d1 i)) (nat_seq (Suc 0) n) @ map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d2 i)) (nat_seq (Suc 0) n2)) ! i"
      and s="(map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d1 i)) (nat_seq (Suc 0) n)) ! i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d1 i)) (nat_seq (Suc 0) n) ! i"
      and s="(\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d1 i)) (nat_seq (Suc 0) n ! i)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc 0) n ! i"
      and s="(Suc 0)+i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n) @ map (\<lambda>i. case d2 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n2)) ! i"
      and s="map (\<lambda>i. case d2 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n2) ! (i-length (map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n)))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq (Suc 0) n2 ! (i-n)"
      and s="(Suc 0)+(i-n)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Suc i - n"
      and s="Suc (i-n)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma derivation_append_preserves_get_labels: "
  get_labels (derivation_append d1 d2 n1) (n1+n2) = get_labels d1 n1 @ (get_labels d2 n2)"
  apply(simp add: get_labels_def derivation_append_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n1 + n2)) = (n1+n2) + 1 - (Suc 0)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) n1) = n1 + 1 - (Suc 0)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) n2) = n2 + 1 - (Suc 0)")
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (n1 + n2) ! i = (Suc 0) + i")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(auto)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) n1 ! i = (Suc 0) + i")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: get_label_def)
   apply(rule_tac
      t="(map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1) @ map (\<lambda>i. case d2 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n2)) ! i"
      and s="(map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1))!i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_1)
    apply(rule_tac
      t="length (map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1))"
      and s="length (nat_seq (Suc 0) n1)"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(rule length_map)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1) ! i"
      and s="(\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) ((nat_seq (Suc 0) n1) ! i)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) n2 ! (i - n1) = (Suc 0) + (i - n1)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(simp add: get_label_def)
  apply(rule_tac
      t="(map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1) @ map (\<lambda>i. case d2 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n2)) ! i"
      and s="(map (\<lambda>i. case d2 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n2))!(i - length(map (\<lambda>i. case d1 i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e) (nat_seq (Suc 0) n1)))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Suc i - n1"
      and s="Suc (i-n1)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  done

lemma derivation_take_preserves_get_labels: "
  w=get_labels d (n+m)
  \<Longrightarrow> take m w= get_labels (derivation_take d m) m"
  apply(simp add: derivation_take_def)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rule listEqI)
   apply(rule_tac
      t="length (take m (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (n + m))))"
      and s="m"
      in ssubst)
    apply(rule take_all_length)
    apply(rule_tac
      t="length (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (n + m)))"
      and s="length (nat_seq (Suc 0) (n + m))"
      in ssubst)
     apply(rule length_map)
    apply(rule_tac
      t="length (nat_seq (Suc 0) (n + m))"
      and s="(n+m) + 1 - (Suc 0)"
      in ssubst)
     apply(rule nat_seq_length_prime)
    apply(force)
   apply(rule_tac
      t="length (map (\<lambda>i. get_label (if i \<le> m then d i else None)) (nat_seq (Suc 0) m))"
      and s="length (nat_seq (Suc 0) m)"
      in ssubst)
    apply(rule length_map)
   apply(rule_tac
      t="length (nat_seq (Suc 0) m)"
      and s="m + 1 - (Suc 0)"
      in ssubst)
    apply(rule nat_seq_length_prime)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(thin_tac "i < length (nat_seq (Suc 0) (n + m))")
  apply(rule_tac
      t="map (\<lambda>i. get_label (if i \<le> m then d i else None)) (nat_seq (Suc 0) m) ! i"
      and s="(\<lambda>i. get_label (if i \<le> m then d i else None)) ((nat_seq (Suc 0) m) ! i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_map)
   apply(rule_tac
      t="length (nat_seq (Suc 0) m)"
      and s="m + 1 - (Suc 0)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nat_seq_length_prime)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) (n + m) ! i"
      and s="(Suc 0)+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) m ! i"
      and s="(Suc 0)+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma derivation_map_id: "
  derivation_map dh (\<lambda>x. x) = dh"
  apply(simp add: derivation_map_def)
  apply(rule ext)
  apply(rename_tac n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n a option b)(*strict*)
  apply(clarsimp)
  done

lemma derivation_map_preserves_maximum_of_domain: "
  maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (derivation_map d C) n"
  apply(simp add: derivation_map_def maximum_of_domain_def)
  apply(auto)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(auto)
  done

lemma derivation_take_conf_0: "
  d 0 = c
  \<Longrightarrow> (derivation_take d i) 0 = c"
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_conf_end: "
  d i = c
  \<Longrightarrow> (derivation_take d i) i = c"
  apply(simp add: derivation_take_def)
  done

lemma maximum_of_domain_derivation_take: "
  d i\<noteq>None
  \<Longrightarrow> maximum_of_domain (derivation_take d i) i"
  apply(simp add: maximum_of_domain_def derivation_take_def)
  done

lemma derivation_drop_preserves_generates_maximum_of_domain: "
  maximum_of_domain d (Suc x)
  \<Longrightarrow> maximum_of_domain (derivation_drop d (Suc 0)) x"
  apply(simp add: derivation_drop_def)
  apply(simp add: maximum_of_domain_def)
  apply(auto)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(auto)
  done

lemma concat_has_max_dom: "
  maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> maximum_of_domain (derivation_append d1 d2 m1) (m1 + m2)"
  apply(simp add: derivation_append_def)
  apply(simp add: maximum_of_domain_def)
  done

lemma get_configurations_length: "
  length (get_configurations d n) = Suc n"
  apply(simp add: get_configurations_def)
  apply(rule_tac
      t="Suc n"
      and s="n - 0 + 1"
      in ssubst)
   apply(force)
  apply(rule nat_seq_length)
  apply(blast)+
  done

lemma get_configurations_elem: "
  n>0
  \<Longrightarrow> get_configurations d n = z # zs
  \<Longrightarrow> length zs = n
  \<Longrightarrow> \<forall>i<length(z#zs). \<forall>c e. d i=Some (pair e c) \<longrightarrow> (z#zs)!i=Some c"
  apply(clarsimp)
  apply(rename_tac i c e)(*strict*)
  apply(rule_tac
      t="z#zs"
      and s="get_configurations d (length zs)"
      in ssubst)
   apply(rename_tac i c e)(*strict*)
   apply(force)
  apply(rename_tac i c e)(*strict*)
  apply(simp (no_asm) add: get_configurations_def)
  apply(rule_tac
      t="map (\<lambda>i. get_configuration (d i)) (nat_seq 0 (length zs)) ! i"
      and s="(\<lambda>i. get_configuration (d i)) ((nat_seq 0 (((length zs)))) ! i)"
      in ssubst)
   apply(rename_tac i c e)(*strict*)
   apply(rule nth_map)
   apply(rule_tac
      t="length (nat_seq 0 (((length zs))))"
      and s="(((length zs))) - 0 + 1"
      in ssubst)
    apply(rename_tac i c e)(*strict*)
    apply(rule nat_seq_length)
    apply(force)
   apply(rename_tac i c e)(*strict*)
   apply(force)
  apply(rename_tac i c e)(*strict*)
  apply(rule_tac
      t="(nat_seq 0 (((length zs))) ! i)"
      and s="0+i"
      in ssubst)
   apply(rename_tac i c e)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i c e)(*strict*)
    apply(force)
   apply(rename_tac i c e)(*strict*)
   apply(force)
  apply(rename_tac i c e)(*strict*)
  apply(simp add: get_configuration_def)
  done

lemma get_configurations_elem2: "
  n>0
  \<Longrightarrow> get_configurations d n = w
  \<Longrightarrow> length zs = n
  \<Longrightarrow> \<forall>i<length w. \<forall>c e. d i=Some (pair e c) \<longrightarrow> w!i=Some c"
  apply(subgoal_tac "length (get_configurations d (length zs)) = Suc (length zs)")
   prefer 2
   apply(rule get_configurations_length)
  apply(clarsimp)
  apply(rename_tac i c e)(*strict*)
  apply(simp (no_asm) add: get_configurations_def)
  apply(rule_tac
      t="map (\<lambda>i. get_configuration (d i)) (nat_seq 0 (length zs)) ! i"
      and s="(\<lambda>i. get_configuration (d i)) ((nat_seq 0 (((length zs)))) ! i)"
      in ssubst)
   apply(rename_tac i c e)(*strict*)
   apply(rule nth_map)
   apply(rule_tac
      t="length (nat_seq 0 (((length zs))))"
      and s="(((length zs))) - 0 + 1"
      in ssubst)
    apply(rename_tac i c e)(*strict*)
    apply(rule nat_seq_length)
    apply(force)
   apply(rename_tac i c e)(*strict*)
   apply(force)
  apply(rename_tac i c e)(*strict*)
  apply(rule_tac
      t="(nat_seq 0 (((length zs))) ! i)"
      and s="0+i"
      in ssubst)
   apply(rename_tac i c e)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i c e)(*strict*)
    apply(force)
   apply(rename_tac i c e)(*strict*)
   apply(force)
  apply(rename_tac i c e)(*strict*)
  apply(simp add: get_configuration_def)
  done

lemma derivation_take_id: "
  \<forall>m>n. d m = None
  \<Longrightarrow> derivation_take d n = d"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma Context_Crop_comm: "
  derivation_map (derivation_take d i) C = derivation_take (derivation_map d C) i"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_map_def derivation_take_def)
  done

lemma Context_Skip_comm: "
  d i \<noteq> None
  \<Longrightarrow> derivation_map (derivation_drop d i) C = derivation_drop (derivation_map d C) i"
  apply(simp add: derivation_map_def derivation_drop_def)
  apply(rule ext)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma derivation_extend_with_maximum_of_domain: "
  d i \<noteq> None
  \<Longrightarrow> P d
  \<Longrightarrow> (P d \<Longrightarrow> P (derivation_take d i))
  \<Longrightarrow> \<exists>d'. P d' \<and> maximum_of_domain d' i"
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule conjI)
   apply(erule meta_impE)
    apply(force)
   apply(force)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma derivation_map_map_empty: "
  derivation_map Map.empty C = Map.empty"
  apply(simp add: derivation_map_def)
  done

lemma derivation_take_map_empty: "
  derivation_take Map.empty n = Map.empty"
  apply(simp add: derivation_take_def)
  done

lemma derivation_append_0: "
  d1 0 = d2 0
  \<Longrightarrow> derivation_append d1 d2 0 = d2"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_append_def)
  done

lemma derivation_append_with_0: "
  d1 0 = d2 0
  \<Longrightarrow> derivation_append d1 d2 0 = d2"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_append_def)
  done

lemma derivation_take_derivation_append_ignore: "
  n\<le>m
  \<Longrightarrow> derivation_take (derivation_append d1 d2 m) n = derivation_take d1 n"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def derivation_append_def)
  done

lemma derivation_take_twice: "
  n\<le>m
  \<Longrightarrow> derivation_take (derivation_take d m) n = derivation_take d n"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_twice_prime: "
  m\<le>n
  \<Longrightarrow> derivation_take (derivation_take d m) n = derivation_take d m"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def)
  done

definition der2 :: "
  'conf
  \<Rightarrow> 'label
  \<Rightarrow> 'conf
  \<Rightarrow> ('label,'conf)derivation"
  where
    "der2 c1 e c2 \<equiv>
  \<lambda>n.
  if n = 0
  then Some (pair None c1)
  else (if n = Suc 0
        then Some (pair (Some e) c2)
        else None)"

definition der1 :: "
  'conf
  \<Rightarrow> ('label,'conf)derivation"
  where
    "der1 c \<equiv>
  \<lambda>n.
  if n = 0
  then Some (pair None c)
  else None"

definition der3 :: "
  'conf
  \<Rightarrow> 'label
  \<Rightarrow> 'conf
  \<Rightarrow> 'label
  \<Rightarrow> 'conf
  \<Rightarrow> ('label,'conf)derivation"
  where
    "der3 c1 e1 c2 e2 c3 \<equiv>
  \<lambda>n.
  if n = 0
  then Some (pair None c1)
  else if n = 1
       then Some (pair (Some e1) c2)
       else if n = 2
            then Some (pair (Some e2) c3)
            else None"

lemma der3_maximum_of_domain: "
  maximum_of_domain (der3 c1 e1 c2 e2 c3) (Suc (Suc 0))"
  apply(simp add: maximum_of_domain_def der3_def)
  done

lemma der2_maximum_of_domain: "
  maximum_of_domain (der2 c1 e c2) (Suc 0)"
  apply(simp add: maximum_of_domain_def der2_def)
  done

lemma der1_maximum_of_domain: "
  maximum_of_domain (der1 c) 0"
  apply(simp add: maximum_of_domain_def der1_def)
  done

lemma derivationEQ_by_derivation_take_and_derivation_drop: "
  derivation_take d n = derivation_take d' n
  \<Longrightarrow> derivation_drop d n = derivation_drop d' n
  \<Longrightarrow> d = d'"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x\<le>n")
   apply(rename_tac x)(*strict*)
   apply(thin_tac "derivation_drop d n = derivation_drop d' n")
   apply(rule_tac
      t="d x"
      and s="derivation_take d n x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(thin_tac "derivation_take d n = derivation_take d' n")
    apply(simp add: derivation_take_def)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="d' x"
      and s="derivation_take d' n x"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(thin_tac "derivation_take d n = derivation_take d' n")
    apply(simp add: derivation_take_def)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "derivation_take d n = derivation_take d' n")
  apply(rule_tac
      t="d x"
      and s="derivation_drop d n (x-n)"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "derivation_drop d n = derivation_drop d' n")
   apply(simp add: derivation_drop_def)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="d' x"
      and s="derivation_drop d' n (x-n)"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "derivation_drop d n = derivation_drop d' n")
   apply(simp add: derivation_drop_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma get_labels_derivation_map: "
  get_labels (derivation_map d f) n = (get_labels d n)"
  apply(simp add: get_labels_def get_label_def derivation_map_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac "d x")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x a option b)(*strict*)
  apply(clarsimp)
  done

lemma get_labels_derivation_drop: "
  get_labels(derivation_drop d n)m = drop n (get_labels d (n+m))"
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) m) = n + 1 - Suc 0" for n)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n+m)) = SSn + 1 - Suc 0" for SSn)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) m ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (n+m) ! (n+i) = SSn+SSi" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def derivation_drop_def)
  apply(rule_tac
      t = "n+i"
      and s = "i+n"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma realiziable_implies_in_get_labels: "
  d i = Some (pair x c)
  \<Longrightarrow> Suc 0\<le>i
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> x \<in> set (get_labels d n)"
  apply(simp add: get_labels_def)
  apply(rule inMap)
  apply(rule_tac
      x="i"
      in bexI)
   apply(simp add: get_label_def)
  apply(rule nat_seq_interval)
   apply(force)
  apply(force)
  done

lemma get_labels_der2_decompose: "
  get_labels
  (derivation_append (der2 c1 e c2) d (Suc 0))
  (Suc n) =
  Some e # get_labels d n"
  apply(rule listEqI)
   apply(simp add: get_labels_def)
   apply (metis list.size(3) nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(simp add: get_label_def)
   apply(simp add: derivation_append_def der2_def)
   apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! 0"
      and s="Suc 0 + 0"
      in ssubst)
    apply (metis Nat.add_0_right Suc_le_lessD less_eq_nat.simps(1) nat_seq_nth_compute not_less0 not_less_eq_eq)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(simp add: derivation_append_def der2_def)
  apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! Suc nat"
      and s="Suc 0+Suc nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply (metis One_nat_def Suc_less_eq diff_Suc_1 less_eq_Suc_le nat_seq_length_Suc0 zero_less_Suc)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i)) (nat_seq (Suc 0) n) ! nat"
      and s=" (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i)) ((nat_seq (Suc 0) n) ! nat)"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply (metis get_label_def Suc_less_SucD Suc_less_eq less_trans_Suc nat_seq_length_Suc0 nth_map zero_less_Suc)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! nat"
      and s="Suc 0+nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply (metis Suc_lessD diff_Suc_Suc less_Suc_eq_le minus_nat.diff_0 nat_seq_length_Suc0 zero_less_Suc)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) n ! nat"
      and s="Suc 0+nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    apply (metis One_nat_def Suc_lessD less_Suc0 less_not_refl nat_seq_length_Suc0 trivNat)
   apply(rename_tac nat)(*strict*)
   apply (metis One_nat_def Suc_eq_plus1 add_leE diff_add_inverse le_diff_conv2 nat_seq_length_prime add.commute not_less_eq trivNat)
  apply(rename_tac nat)(*strict*)
  apply(force)
  done

lemma get_labels_derivation_drop_decompose: "
  d (Suc 0) = Some (pair (Some e) c)
  \<Longrightarrow> get_labels d (Suc (n1 + n2)) = Some e # get_labels (derivation_drop d (Suc 0)) (n1 + n2)"
  apply(rule listEqI)
   apply(clarsimp)
   apply (metis get_labels_length)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(rule_tac
      t="nat_seq (Suc 0) (Suc (n1 + n2)) ! i"
      and s="Suc 0+i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply (metis One_nat_def Suc_lessD less_Suc0 less_not_refl trivNat)
   apply(rename_tac i)(*strict*)
   apply (metis One_nat_def Suc_eq_plus1 diff_add_inverse nat_seq_length_prime add.commute not_less_eq trivNat)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="map (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (derivation_drop d (Suc 0) i)) (nat_seq (Suc 0) (n1 + n2)) ! nat"
      and s="(\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (derivation_drop d (Suc 0) i)) ((nat_seq (Suc 0) (n1 + n2)) ! nat)"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nth_map)
   apply (metis Suc_less_eq nat_seq_length_Suc0 neq0_conv not_less_eq zero_less_Suc)
  apply(rename_tac nat)(*strict*)
  apply(rule_tac
      t="nat_seq (Suc 0) (n1 + n2) ! nat"
      and s="Suc 0+nat"
      in ssubst)
   apply(rename_tac nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac nat)(*strict*)
    apply (metis One_nat_def Suc_lessD less_Suc0 less_not_refl nat_seq_length_Suc0 trivNat)
   apply(rename_tac nat)(*strict*)
   apply (metis One_nat_def Suc_eq_plus1 add_leE diff_add_inverse le_diff_conv2 nat_seq_length_prime add.commute not_less_eq trivNat)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_drop_def)
  done

lemma der2_get_labels: "
  get_labels (der2 c1 e c2) (Suc 0) = [Some e]"
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc 0)=[Suc 0]")
   apply(clarsimp)
   apply(simp add: der2_def get_label_def)
  apply (metis natUptTo_n_n)
  done

lemma der1_get_labels: "
  get_labels (der1 c) 0 = []"
  apply(rule get_labelsEmpty)
  done

definition sat_refined :: "'TSstructure \<Rightarrow> (nat \<Rightarrow> ('label,'conf)derivation_configuration option) \<Rightarrow> ('conf\<Rightarrow>'label\<Rightarrow>'conf\<Rightarrow>bool) \<Rightarrow> bool" where
  "sat_refined G d P = (\<forall>i.
  case d (Suc i) of None \<Rightarrow> True
  | Some (pair e' c') \<Rightarrow> (case d i of None \<Rightarrow> False
  | Some (pair e c) \<Rightarrow> (case e' of None \<Rightarrow> False | Some e' \<Rightarrow> P c e' c))
  )"

lemma get_labels_strict_prefix1: "
  strict_prefix (map the (get_labels d n)) (map the (get_labels d (Suc n)))"
  apply(simp add: get_labels_def strict_prefix_def)
  apply(rule_tac
      x="[the(get_label (d(Suc n)))]"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="nat_seq (Suc 0) (Suc n)"
      and s="nat_seq (Suc 0) n@[Suc n]"
      in ssubst)
   apply (metis nat_seq_drop_last_prime)
  apply(clarsimp)
  done

lemma get_labels_strict_prefix: "
  strict_prefix (map the (get_labels d n)) (map the (get_labels d (Suc n+m)))"
  apply(induct m)
   apply(clarsimp)
   apply(rule get_labels_strict_prefix1)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "strict_prefix (map the (get_labels d (Suc (n + m)))) (map the (get_labels d (Suc (Suc (n + m)))))")
   apply(rename_tac m)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac m c ca)(*strict*)
   apply(rule_tac
      x="c@ca"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="map the (get_labels d (Suc (Suc (n + m))))"
      and s="map the (get_labels d (Suc (n + m))) @ ca"
      in ssubst)
    apply(rename_tac m c ca)(*strict*)
    apply(force)
   apply(rename_tac m c ca)(*strict*)
   apply(rule_tac
      t="map the (get_labels d (Suc (n + m)))"
      and s="map the (get_labels d n) @ c"
      in ssubst)
    apply(rename_tac m c ca)(*strict*)
    apply(force)
   apply(rename_tac m c ca)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac m)(*strict*)
  apply(thin_tac "strict_prefix (map the (get_labels d n)) (map the (get_labels d (Suc (n + m))))")
  apply(rule get_labels_strict_prefix1)
  done

lemma get_labels_drop_tail: "
  get_labels d (n+m) = w@v
  \<Longrightarrow> length w=n
  \<Longrightarrow> get_labels d n = w"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length w)) = n + 1 - Suc 0" for n)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length w+m)) = n + 1 - Suc 0" for n)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (length w) ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (length w+m) ! i = SSn+SSi" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="w!i"
      and s="(w@v)!i"
      in subst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="get_label (d (Suc i))"
      and s="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length w + m)) !i"
      in ssubst)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(thin_tac "map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length w + m)) = w @ v")
  apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length w + m)) ! i"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (length w + m)) ! i)"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma getLabel_at_pos: "
  get_labels d n = w
  \<Longrightarrow> d (Suc i) = Some (pair (Some e) c)
  \<Longrightarrow> i<n
  \<Longrightarrow> w!i=Some e"
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - Suc 0" for SSn)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) n) ! i"
      and s="(\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) n) ! i)"
      in ssubst)
   apply(rule nth_map)
   apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = SSn+SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

lemma get_labels_decomp: "
  get_labels d (n+m) = (get_labels d n) @ (drop n (get_labels d (n+m)))"
  apply(subgoal_tac "length (nat_seq (Suc 0) (n+m)) = SSn + 1 - Suc 0" for SSn)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - Suc 0" for SSn)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc 0) m) = SSn + 1 - Suc 0" for SSn)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(clarsimp)
  apply(simp add: get_labels_def)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) n) @ drop n (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (n + m)))) ! i"
      and s="(map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) n) ) ! i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (n+m) ! i = SSn+SSi" for SSn SSi)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) n ! i = SSn+SSi" for SSn SSi)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="(map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) n) @ drop n (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (n + m)))) ! i"
      and s="(drop n (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (n + m)))) ! (i-length(map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) n)))"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  done

lemma der3_maximum_of_domain2: "
  maximum_of_domain (der3 c1 e1 c2 e2 c3) 2"
  apply(simp add: maximum_of_domain_def der3_def)
  done

lemma maximum_of_domain_derivation_append_der1: "
  maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (derivation_append d (der1 c) n) n"
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: derivation_append_def)
  apply(simp add: der1_def)
  done

lemma maximum_of_domain_derivation_append_der2: "
  maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (derivation_append d (der2 c e c') n) (Suc n)"
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: derivation_append_def)
  apply(simp add: der2_def)
  done

lemma derivation_map_Relects_None: "
  derivation_map d C n = None
  \<Longrightarrow> d n = None"
  apply(simp add: derivation_map_def)
  apply(case_tac "d n")
   apply(auto)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(auto)
  done

lemma get_labels__seperate_last: "
  d (Suc n) = Some (pair e c)
  \<Longrightarrow> get_labels d (Suc n) = get_labels d n @ [e]"
  apply(simp add: get_labels_def)
  apply(rule_tac t="nat_seq (Suc 0) (Suc n)" and s="nat_seq (Suc 0) n @[Suc n]" in ssubst)
   apply (metis nat_seq_drop_last_prime)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

lemma get_labels__derivation_append__trivial: "
  get_labels (derivation_append d1 d2 n) n = get_labels d1 n"
  apply(simp add: get_labels_def derivation_append_def)
  apply(clarsimp)
  apply (metis nat_seq_in_interval)
  done

end
