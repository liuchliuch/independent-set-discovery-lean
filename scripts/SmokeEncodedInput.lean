import IndependentSetDiscovery.Algorithms.EncodedInput

open IndependentSetDiscovery
open IndependentSetDiscovery.Algorithms
open IndependentSetDiscovery.ShortestPaths

def weightedTwo : EncodedInput 2 2 where
  graphData :=
    { matrix := #v[#v[false, false], #v[false, false]]
      symmetric := by decide
      diagonal := by decide }
  allowed := #v[#v[true, true], #v[true, true]]
  costs := #v[#v[2, 0], #v[0, 3]]
  nonneg := by decide

def noVertices : EncodedInput 2 0 where
  graphData :=
    { matrix := #v[]
      symmetric := by intro u; exact Fin.elim0 u
      diagonal := by intro u; exact Fin.elim0 u }
  allowed := #v[#v[], #v[]]
  costs := #v[#v[], #v[]]
  nonneg := by intro i v; exact Fin.elim0 v

def emptyInstance : EncodedInput 0 0 where
  graphData :=
    { matrix := #v[]
      symmetric := by intro u; exact Fin.elim0 u
      diagonal := by intro u; exact Fin.elim0 u }
  allowed := #v[]
  costs := #v[]
  nonneg := by intro i; exact Fin.elim0 i

example : noVertices.solve 2 = none := by decide
example : (emptyInstance.solve 2).isSome = true := by decide

#eval (weightedTwo.solve 2).map (fun x => [x 0 |>.val, x 1 |>.val])
#eval (noVertices.solve 2).isNone
#eval (emptyInstance.solve 2).isSome
