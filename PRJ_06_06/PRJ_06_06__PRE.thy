section {*PRJ\_06\_06\_\_PRE*}
theory
  PRJ_06_06__PRE

imports
  PRJ_06_06__ENTRY

begin



(*
==== L_ATS_Simulation_Configuration_Weak(...) ====
translation of
  is_forward_edge_deterministic_accessible
  get_accessible_configurations
  Nonblockingness_branching
  unmarked language
  marked language
using
  simulation relation on configuration where steps are mimicked weakly.

==== L_ATS_Branching_Versus_Linear(...) ====
translation of
  marked language
  unmarked language
  Nonblockingness_branching versus Nonblockingness_linear
using
  bisimulation relation on configuration where steps are mimicked strongly.

==== L_ATS_Bisimulation_Trace_Strong(...) ====
translation of
  is_forward_edge_deterministic_accessible
  marked language
  unmarked language
  Nonblockingness_linear_restricted_DB
  Nonblockingness_linear_DB
using
  bisimulation relation on derivations where steps are mimicked stongly.

==== L_ATS_Bisimulation_Configuration_Weak ====
translation of
  Nonblockingness_branching
using
  bisimulation relation on configuration where steps are mimicked weakly.

==== L_ATS_Simulation_Configuration_Weak_Plain ====
translation of
  marked language
  unmarked language
using
  simulation relation on configuration where steps are mimicked weakly.

=== L_ATS_Derivation_Map ===
translation of
  initial derivations
using
  simulation relation on configuration where steps are mimicked strongly.
<<can handle infinite derivations>>

*)

end
