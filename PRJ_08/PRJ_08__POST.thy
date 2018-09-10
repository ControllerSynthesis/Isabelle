section {*PRJ\_08\_\_POST*}
theory
  PRJ_08__POST

imports
  I_kparser_FS
  I_kparser_HF
  I_kparser_HFS
  I_kparser_HFS_HF
  I_kparser_S
  I_kparser_S_FS
  I_kparser_S_HFS
  I_kparser_base
  I_kparser_lemmas
  I_kparser_main
  PRJ_08__ENTRY

begin

lemmas parser_interpretations =
  parserHFS_interpretations0
  parserHFS_interpretations1
  parserS_interpretations
  parserFS_interpretations
  parserHF_interpretations

end
