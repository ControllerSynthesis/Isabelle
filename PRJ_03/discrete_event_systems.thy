section {*discrete\_event\_systems*}
theory
  discrete_event_systems

imports
  PRJ_03__ENTRY

begin

declare [[ hypsubst_thin = false ]]
datatype '\<Sigma> DES =
  DES (des_langUM : "'\<Sigma> list set") (des_langM : "'\<Sigma> list set")
declare [[ hypsubst_thin = true ]]

definition IsDES :: "
  '\<Sigma> DES
  \<Rightarrow> bool" where
  "IsDES D \<equiv>
  des_langM D \<subseteq> des_langUM D
  \<and> prefix_closure (des_langUM D) = des_langUM D"

definition lesseqDES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> bool" where
  "lesseqDES D1 D2 \<equiv>
  des_langUM D1 \<subseteq> des_langUM D2
  \<and> des_langM D1 \<subseteq> des_langM D2"

definition lessDES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> bool" where
  "lessDES D1 D2 \<equiv>
  lesseqDES D1 D2 \<and> D1 \<noteq> D2"

definition infDES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES" where
  "infDES D1 D2 \<equiv>
  DES (des_langUM D1 \<inter> des_langUM D2) (des_langM D1 \<inter> des_langM D2)"

definition supDES :: "
  '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES
  \<Rightarrow> '\<Sigma> DES" where
  "supDES D1 D2 \<equiv>
  DES (des_langUM D1 \<union> des_langUM D2) (des_langM D1 \<union> des_langM D2)"

definition botDES :: "
  '\<Sigma> DES" where
  "botDES \<equiv>
  DES {} {}"

definition topDES :: "
  '\<Sigma> DES" where
  "topDES \<equiv>
  DES (UNIV::'\<Sigma> list set) (UNIV::'\<Sigma> list set)"

definition SupDES :: "
  '\<Sigma> DES set
  \<Rightarrow> '\<Sigma> DES" where
  "SupDES A \<equiv>
  DES (\<Union>(des_langUM ` A)) (\<Union>(des_langM ` A))"

definition InfDES :: "
  '\<Sigma> DES set
  \<Rightarrow> '\<Sigma> DES" where
  "InfDES A \<equiv>
  DES (\<Inter>(des_langUM ` A)) (\<Inter>(des_langM ` A))"

instantiation "DES" :: (type)complete_lattice
begin

print_context

definition
  bot_DES_ext_def: "bot = botDES"

definition
  inf_DES_ext_def: "inf D1 D2 = infDES D1 D2"

definition
  sup_DES_ext_def: "sup D1 D2 = supDES D1 D2"

definition
  top_DES_ext_def: "top = topDES"

definition
  less_eq_DES_ext_def: "less_eq D1 D2 = lesseqDES D1 D2"

definition
  less_DES_ext_def: "less A B = lessDES A B"

definition
  Sup_DES_ext_def: "Sup A = SupDES A"

definition
  Inf_DES_ext_def: "Inf A = InfDES A"

instance
  apply intro_classes
                 apply(rename_tac x y)(*strict*)
                 apply(unfold SupDES_def InfDES_def Inf_DES_ext_def Sup_DES_ext_def topDES_def botDES_def top_DES_ext_def bot_DES_ext_def sup_DES_ext_def inf_DES_ext_def supDES_def infDES_def lessDES_def lesseqDES_def less_eq_DES_ext_def less_DES_ext_def des_langUM_def des_langM_def)
                 apply(case_tac x)
                 apply(rename_tac x y fun1 fun2)(*strict*)
                 apply(case_tac y)
                 apply(rename_tac x y fun1 fun2 fun1a fun2a)(*strict*)
                 apply(force)
                apply(rename_tac x)(*strict*)
                apply(case_tac x)
                apply(rename_tac x fun1 fun2)(*strict*)
                apply(force)
               apply(rename_tac x y z)(*strict*)
               apply(case_tac x)
               apply(rename_tac x y z fun1 fun2)(*strict*)
               apply(case_tac y)
               apply(rename_tac x y z fun1 fun2 fun1a fun2a)(*strict*)
               apply(case_tac z)
               apply(rename_tac x y z fun1 fun2 fun1a fun2a fun1b fun2b)(*strict*)
               apply(force)
              apply(rename_tac x y)(*strict*)
              apply(case_tac x)
              apply(rename_tac x y fun1 fun2)(*strict*)
              apply(case_tac y)
              apply(rename_tac x y fun1 fun2 fun1a fun2a)(*strict*)
              apply(force)
             apply(rename_tac x y)(*strict*)
             apply(case_tac x)
             apply(rename_tac x y fun1 fun2)(*strict*)
             apply(case_tac y)
             apply(rename_tac x y fun1 fun2 fun1a fun2a)(*strict*)
             apply(force)
            apply(rename_tac x y)(*strict*)
            apply(case_tac x)
            apply(rename_tac x y fun1 fun2)(*strict*)
            apply(case_tac y)
            apply(rename_tac x y fun1 fun2 fun1a fun2a)(*strict*)
            apply(force)
           apply(rename_tac x y z)(*strict*)
           apply(case_tac x)
           apply(rename_tac x y z fun1 fun2)(*strict*)
           apply(case_tac y)
           apply(rename_tac x y z fun1 fun2 fun1a fun2a)(*strict*)
           apply(case_tac z)
           apply(rename_tac x y z fun1 fun2 fun1a fun2a fun1b fun2b)(*strict*)
           apply(force)
          apply(rename_tac x y)(*strict*)
          apply(case_tac x)
          apply(rename_tac x y fun1 fun2)(*strict*)
          apply(case_tac y)
          apply(rename_tac x y fun1 fun2 fun1a fun2a)(*strict*)
          apply(force)
         apply(rename_tac y x)(*strict*)
         apply(case_tac y)
         apply(rename_tac y x fun1 fun2)(*strict*)
         apply(case_tac x)
         apply(rename_tac y x fun1 fun2 fun1a fun2a)(*strict*)
         apply(force)
        apply(rename_tac y x z)(*strict*)
        apply(case_tac x)
        apply(rename_tac y x z fun1 fun2)(*strict*)
        apply(case_tac y)
        apply(rename_tac y x z fun1 fun2 fun1a fun2a)(*strict*)
        apply(case_tac z)
        apply(rename_tac y x z fun1 fun2 fun1a fun2a fun1b fun2b)(*strict*)
        apply(force)
       apply(rename_tac x A)(*strict*)
       apply(clarsimp)
       apply(rename_tac x A)(*strict*)
       apply(case_tac x)
       apply(rename_tac x A fun1 fun2)(*strict*)
       apply(clarsimp)
       apply(rename_tac A fun1 fun2)(*strict*)
       apply(rule conjI)
        apply(rename_tac A fun1 fun2)(*strict*)
        apply(clarsimp)
        apply(rename_tac A fun1 fun2 x)(*strict*)
        apply(erule_tac
      x="DES fun1 fun2"
      in ballE)
         apply(rename_tac A fun1 fun2 x)(*strict*)
         apply(force)
        apply(rename_tac A fun1 fun2 x)(*strict*)
        apply(force)
       apply(rename_tac A fun1 fun2)(*strict*)
       apply(clarsimp)
       apply(rename_tac A fun1 fun2 x)(*strict*)
       apply(erule_tac
      x="DES fun1 fun2"
      in ballE)
        apply(rename_tac A fun1 fun2 x)(*strict*)
        apply(force)
       apply(rename_tac A fun1 fun2 x)(*strict*)
       apply(force)
      apply(rename_tac A x)(*strict*)
      apply(case_tac x)
      apply(rename_tac A x fun1 fun2)(*strict*)
      apply(clarsimp)
      apply(rename_tac A fun1 fun2)(*strict*)
      apply(force)
     apply(rename_tac x A)(*strict*)
     apply(clarsimp)
     apply(case_tac x)
     apply(rename_tac x A fun1 fun2)(*strict*)
     apply(clarsimp)
     apply(rename_tac A fun1 fun2)(*strict*)
     apply(rule conjI)
      apply(rename_tac A fun1 fun2)(*strict*)
      apply(clarsimp)
      apply(rename_tac A fun1 fun2 x)(*strict*)
      apply(rule_tac
      x="DES fun1 fun2"
      in bexI)
       apply(rename_tac A fun1 fun2 x)(*strict*)
       apply(force)
      apply(rename_tac A fun1 fun2 x)(*strict*)
      apply(force)
     apply(rename_tac A fun1 fun2)(*strict*)
     apply(clarsimp)
     apply(rename_tac A fun1 fun2 x)(*strict*)
     apply(rule_tac
      x="DES fun1 fun2"
      in bexI)
      apply(rename_tac A fun1 fun2 x)(*strict*)
      apply(force)
     apply(rename_tac A fun1 fun2 x)(*strict*)
     apply(force)
    apply(rename_tac A z)(*strict*)
    apply(clarsimp)
    apply(case_tac z)
    apply(rename_tac A z fun1 fun2)(*strict*)
    apply(clarsimp)
    apply(rename_tac A fun1 fun2)(*strict*)
    apply(rule conjI)
     apply(rename_tac A fun1 fun2)(*strict*)
     apply(clarsimp)
     apply(rename_tac A fun1 fun2 x xa)(*strict*)
     apply(erule_tac
      x="xa"
      in meta_allE)
     apply(clarsimp)
     apply(force)
    apply(rename_tac A fun1 fun2)(*strict*)
    apply(force)
   apply(clarsimp)
  apply(clarsimp)
  done
end

end
