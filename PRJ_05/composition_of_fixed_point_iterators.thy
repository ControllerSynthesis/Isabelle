section {*composition\_of\_fixed\_point\_iterators*}
theory
  composition_of_fixed_point_iterators

imports
  operations_on_discrete_event_systems

begin

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator ((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P))) IsDES
  (predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S))) (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Star_Controllable_Subset)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
   apply(force)
  apply(rename_tac Q)(*strict*)
  apply(simp add: DES_controllability_def)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1_bf: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES)
  IsDES
  (predicate_AND (predicate_AND IsDES DES_nonblockingness) ((predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S)))))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1)
    apply(force)
   apply(force)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES) UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) ((predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S))))))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    prefer 2
    apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1_bf)
     apply(force)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_IteratorX_F_spec_cont1_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorX (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES)
(predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) ((predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S))))))"
  apply(rule_tac ssubst)
   apply(rule Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator)
  apply(rule Characteristic_Fixed_Point_Iterator_weakening)
  apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont1_bf_Enforce_Valid_DES)
   apply(force)
  apply(force)
  done

corollary unused_decomposition_sound_and_least_restrictive: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> F = (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES)
  \<Longrightarrow> gfp (\<lambda>X. F (inf X (F Y))) = gfp (\<lambda>X. F (inf X Y))"
  apply(rule gfp_invariant)
  apply(rule_tac
      t="F"
      and s="(((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Star_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES)"
      in ssubst)
   apply(force)
  apply(rule unused_Characteristic_Fixed_Point_IteratorX_F_spec_cont1_bf_Enforce_Valid_DES)
   apply(force)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec2_cont: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator ((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Controllable_Subset SigmaUC (des_langUM P))) IsDES
(predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S)))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Controllable_Subset)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
   apply(force)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec2_cont_bf: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES) IsDES
(predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S))))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    prefer 2
    apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec2_cont)
     apply(force)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont2_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES) UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S)))))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    prefer 2
    apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec2_cont_bf)
     apply(force)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_IteratorX_F_spec_cont2_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorX (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES) (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (DES_controllability SigmaUC P)) (predicate_AND IsDES (DES_specification_satisfied S)))))"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   apply(rule Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator)
  apply(rule Characteristic_Fixed_Point_Iterator_weakening)
  apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont2_bf_Enforce_Valid_DES)
   apply(force)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator ((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Marked_Controllable_Subset SigmaUC (des_langUM P))) (predicate_AND IsDES DES_nonblockingness)
(predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability SigmaUC P))) (predicate_AND IsDES (DES_specification_satisfied S)))
 (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
   apply(force)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4_bf: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Marked_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES) IsDES
(predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability SigmaUC P))) (predicate_AND IsDES (DES_specification_satisfied S))))
 (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    prefer 2
    apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4)
     apply(force)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator
  (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Marked_Controllable_Subset SigmaUC (des_langUM P) ))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES)
  UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability SigmaUC P))) (predicate_AND IsDES (DES_specification_satisfied S)))))
  (predicate_AND IsDES (DES_specification_satisfied S))"
  apply(rule Characteristic_Composition_of_Fixed_Point_Iterators)
    prefer 2
    apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4_bf)
     apply(force)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_IteratorX_F_spec_cont4_bf_Enforce_Valid_DES: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_IteratorX (((Enforce_Specification_Satisfaction S)\<circ>(Enforce_Marked_Controllable_Subset SigmaUC (des_langUM P)))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES) (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability SigmaUC P))) (predicate_AND IsDES (DES_specification_satisfied S)))))"
  apply(rule_tac
      P="\<lambda>X. X"
      in ssubst)
   apply(rule Characteristic_Fixed_Point_IteratorX_vs_Characteristic_Fixed_Point_Iterator)
  apply(rule Characteristic_Fixed_Point_Iterator_weakening)
  apply(rule unused_Characteristic_Fixed_Point_Iterator_F_spec_cont4_bf_Enforce_Valid_DES)
   apply(force)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_bf_spec: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (Enforce_Nonblockingness_DES\<circ>(\<lambda>C. Enforce_Specification_Satisfaction S C)) IsDES
  (predicate_AND (predicate_AND IsDES (DES_specification_satisfied S)) (predicate_AND IsDES DES_nonblockingness)) (predicate_AND IsDES DES_nonblockingness)"
  apply(rule_tac Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Specification_Satisfaction)
    apply(force)
   apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  apply(rename_tac Q)(*strict*)
  apply(force)
  done

lemma unused_Characteristic_Fixed_Point_Iterator_F_bf_cont4_bf_des: "
  IsDES P
  \<Longrightarrow> IsDES S
  \<Longrightarrow> Characteristic_Fixed_Point_Iterator (Enforce_Nonblockingness_DES\<circ>(Enforce_Marked_Controllable_Subset SigmaUC (des_langUM P))\<circ>Enforce_Nonblockingness_DES\<circ>Enforce_Valid_DES) UNIVmap
  (predicate_AND IsDES (predicate_AND (predicate_AND IsDES DES_nonblockingness) (predicate_AND (predicate_AND IsDES (predicate_AND DES_nonblockingness (DES_controllability SigmaUC P))) (predicate_AND IsDES DES_nonblockingness)))) (predicate_AND IsDES DES_nonblockingness)"
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Valid_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="(predicate_AND IsDES DES_nonblockingness)"
      and ?Qinter2.0="(predicate_AND IsDES DES_nonblockingness)"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule_tac
      ?Qinter1.0="IsDES"
      and ?Qinter2.0="IsDES"
      in Characteristic_Composition_of_Fixed_Point_Iterators)
    apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Marked_Controllable_Subset)
    apply(force)
   prefer 2
   apply(rename_tac Q)(*strict*)
   apply(force)
  apply(rule Characteristic_Fixed_Point_Iterator_Enforce_Nonblockingness_DES)
  done

end
