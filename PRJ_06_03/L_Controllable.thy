section {*L\_Controllable*}
theory
  L_Controllable

imports
  PRJ_06_03__ENTRY

begin

locale L_Controllable =
  Plant: ATS_Language
  "TSstructureP :: 'TSstructureP \<Rightarrow> bool"
  "configurationsP :: 'TSstructureP \<Rightarrow> 'confP set"
  "initial_configurationsP :: 'TSstructureP \<Rightarrow> 'confP set"
  "step_labelsP :: 'TSstructureP \<Rightarrow> 'labelP set"
  "step_relationP :: 'TSstructureP \<Rightarrow> 'confP \<Rightarrow> 'labelP \<Rightarrow> 'confP \<Rightarrow> bool"
  "effectsP :: 'TSstructureP \<Rightarrow> 'event set"
  "marking_conditionP :: 'TSstructureP \<Rightarrow> ('labelP,'confP)derivation \<Rightarrow> bool"
  "marked_effectP :: 'TSstructureP \<Rightarrow> ('labelP,'confP)derivation \<Rightarrow> 'event set"
  "unmarked_effectP :: 'TSstructureP \<Rightarrow> ('labelP,'confP)derivation \<Rightarrow> 'event set"
  +
  Controller: ATS_Language
  "TSstructureC :: 'TSstructureC \<Rightarrow> bool"
  "configurationsC :: 'TSstructureC \<Rightarrow> 'confC set"
  "initial_configurationsC :: 'TSstructureC \<Rightarrow> 'confC set"
  "step_labelsC :: 'TSstructureC \<Rightarrow> 'labelC set"
  "step_relationC :: 'TSstructureC \<Rightarrow> 'confC \<Rightarrow> 'labelC \<Rightarrow> 'confC \<Rightarrow> bool"
  "effectsC :: 'TSstructureC \<Rightarrow> 'event set"
  "marking_conditionC :: 'TSstructureC \<Rightarrow> ('labelC,'confC)derivation \<Rightarrow> bool"
  "marked_effectC :: 'TSstructureC \<Rightarrow> ('labelC,'confC)derivation \<Rightarrow> 'event set"
  "unmarked_effectC :: 'TSstructureC \<Rightarrow> ('labelC,'confC)derivation \<Rightarrow> 'event set"
  for
    TSstructureP configurationsP initial_configurationsP step_labelsP step_relationP effectsP marking_conditionP marked_effectP unmarked_effectP TSstructureC configurationsC initial_configurationsC step_labelsC step_relationC effectsC marking_conditionC marked_effectC unmarked_effectC

context L_Controllable
begin

definition controllable :: "
  'TSstructureC
  \<Rightarrow> 'TSstructureP
  \<Rightarrow> ('event \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "controllable C P uncontrollable_effect \<equiv>
  \<forall>dP nP eP cP dC nC eC cC eP' cP' effect.
  Plant.derivation_initial P dP
  \<longrightarrow> maximum_of_domain dP nP
  \<longrightarrow> dP nP = Some (pair eP cP)
  \<longrightarrow> Controller.derivation_initial C dC
  \<longrightarrow> maximum_of_domain dC nC
  \<longrightarrow> dC nC = Some (pair eC cC)
  \<longrightarrow> unmarked_effectP P dP = unmarked_effectC C dC
  \<longrightarrow> step_relationP P cP eP' cP'
  \<longrightarrow> uncontrollable_effect effect
  \<longrightarrow> effect \<in> unmarked_effectP P (derivation_append dP (der2 cP eP' cP') nP) - unmarked_effectP P dP
  \<longrightarrow> (\<exists>\<pi>P' e cC' dC'.
  Controller.derivation C dC'
  \<and> dC' 0 = Some (pair None cC)
  \<and> dC' (length \<pi>P') = Some (pair e cC')
  \<and> maximum_of_domain dC' (length \<pi>P')
  \<and> get_labels dC' (length \<pi>P') = map Some \<pi>P'
  \<and> effect \<in> unmarked_effectC C (derivation_append dC dC' nC) - unmarked_effectC C dC
  )"

definition controllableX :: "
  'TSstructureC
  \<Rightarrow> 'TSstructureP
  \<Rightarrow> ('event \<Rightarrow> bool)
  \<Rightarrow> bool"
  where
    "controllableX C P uncontrollable_effect \<equiv>
  \<forall>dP nP eP cP dC nC eC cC eP' cP' effect new_unmarked_effects.
  Plant.derivation_initial P dP
  \<longrightarrow> maximum_of_domain dP nP
  \<longrightarrow> dP nP = Some (pair eP cP)
  \<longrightarrow> Controller.derivation_initial C dC
  \<longrightarrow> maximum_of_domain dC nC
  \<longrightarrow> dC nC = Some (pair eC cC)
  \<longrightarrow> unmarked_effectP P dP = unmarked_effectC C dC
  \<longrightarrow> step_relationP P cP eP' cP'
  \<longrightarrow> uncontrollable_effect effect
  \<longrightarrow> new_unmarked_effects
        = unmarked_effectP P
            (derivation_append dP (der2 cP eP' cP') nP)
          - unmarked_effectP P dP
  \<longrightarrow> effect \<in> new_unmarked_effects
  \<longrightarrow> (\<exists>\<pi>P' e cC' dC'.
  Controller.derivation C dC'
  \<and> dC' 0 = Some (pair None cC)
  \<and> dC' (length \<pi>P') = Some (pair e cC')
  \<and> maximum_of_domain dC' (length \<pi>P')
  \<and> get_labels dC' (length \<pi>P') = map Some \<pi>P'
  \<and> new_unmarked_effects
      = unmarked_effectC C
          (derivation_append dC dC' nC)
        - unmarked_effectC C dC
  )"

end

end

