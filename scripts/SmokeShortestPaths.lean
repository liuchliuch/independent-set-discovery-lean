import IndependentSetDiscovery.Algorithms.PathDecoder

open IndependentSetDiscovery.ShortestPaths

/-- The path 0--1--2, supplied as actual finite Boolean data. -/
def pathThree : MatrixGraph 3 where
  matrix := #v[#v[false, true, false], #v[true, false, true], #v[false, true, false]]
  symmetric := by decide
  diagonal := by decide

def emptyThree : MatrixGraph 3 where
  matrix := #v[#v[false, false, false], #v[false, false, false], #v[false, false, false]]
  symmetric := by decide
  diagonal := by decide

/-- Computation checks the actual route data, including its deterministic order. -/
example : ((shortestPaths pathThree.graph 0).1[2]).map (List.map Fin.val) =
    some [2, 1] := by decide

example : ((shortestPaths pathThree.graph 0).1[0]).map (List.map Fin.val) =
    some [] := by decide

example : (shortestPaths emptyThree.graph 0).1[2] = none := by decide

example : ((walkOption pathThree.graph 0 2).1.map SimpleGraph.Walk.length) = some 2 := by
  decide

#eval ((shortestPaths pathThree.graph 0).1.toList.map
  (Option.map (List.map Fin.val)), (shortestPaths pathThree.graph 0).2)
#eval ((walkOption pathThree.graph 0 2).1.map SimpleGraph.Walk.length,
  (walkOption pathThree.graph 0 2).2)
