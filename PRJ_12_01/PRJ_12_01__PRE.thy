section {*PRJ\_12\_01\_\_PRE*}
theory
  PRJ_12_01__PRE

imports
  PRJ_12_01__ENTRY

begin

type_synonym 'vertice DT_graph =
  "('vertice, 'vertice) DT_tuple2 set"

type_synonym ('state, 'stack) DT_accessibility_graph =
  "('state, 'stack list, nat option) DT_tuple3 option DT_graph"

end
