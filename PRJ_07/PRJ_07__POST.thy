section {*PRJ\_07\_\_POST*}
theory
  PRJ_07__POST

imports
  I_epda_H
  I_epda_HS
  I_epda_HS_H
  I_epda_S
  I_epda_S_HS
  I_epda_base
  I_epda_lemmas
  I_epda_main
  PRJ_07__ENTRY

begin

lemmas epda_interpretations =
  epdaS_interpretations
  epdaH_interpretations
  epdaHS_interpretations0
  epdaHS_interpretations1

end
