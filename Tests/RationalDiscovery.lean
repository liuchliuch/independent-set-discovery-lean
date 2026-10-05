import IndependentSetDiscovery.Extensions.RationalDiscoveryAlgorithm
import IndependentSetDiscovery.Extensions.DirectedBitComplexity

namespace IndependentSetDiscovery.Tests.RationalDiscovery

open ShortestPaths WeightedDirected

def pathFour : MatrixGraph 4 where
  matrix := Vector.ofFn fun u => Vector.ofFn fun v =>
    decide (u.val + 1 = v.val ∨ v.val + 1 = u.val)
  symmetric := by intros; simp [Bool.or_comm]
  diagonal := by intro u; simp

theorem pathFour_bicliqueFree : BicliqueFree pathFour.graph 2 2 := by
  unfold BicliqueFree HasBiclique
  decide

def fractionalMovement : RationalMatrixInput 4 where
  adjacency := Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val = 1 ∧ (v.val = 2 ∨ v.val = 3))
  weights := Vector.ofFn fun _u => Vector.ofFn fun v => if v.val = 3 then (1 / 3 : ℚ) else (1 / 2 : ℚ)
  nonneg := by intro u v h; fin_cases u <;> fin_cases v <;> norm_num

def zeroMovement : RationalMatrixInput 4 where
  adjacency := Vector.ofFn fun u => Vector.ofFn fun v =>
    decide ((u.val = 1 ∧ (v.val = 2 ∨ v.val = 3)) ∨ (u.val = 2 ∧ v.val = 3))
  weights := Vector.replicate 4 (Vector.replicate 4 0)
  nonneg := by intros; simp

def noMovement : RationalMatrixInput 4 where
  adjacency := Vector.replicate 4 (Vector.replicate 4 false)
  weights := Vector.replicate 4 (Vector.replicate 4 0)
  nonneg := by intros; simp

def replay (A : RationalMatrixInput 4) (Q : Finset (Fin 4)) :
    List (Fin 4 × Fin 4) → Option (Finset (Fin 4))
  | [] => some Q
  | uv :: moves =>
      if uv.1 ∈ Q ∧ uv.2 ∉ Q ∧ A.relation uv.1 uv.2 then
        replay A (insert uv.2 (Q.erase uv.1)) moves
      else none

/-- The verifier uses original rational arcs and direct collision checks. -/
def checkResult (label : String) (A : RationalMatrixInput 4) (cost : ℚ) (slides : ℕ)
    (answer : Option (RationalDiscoveryResult pathFour.graph A.relation A.weight {0, 1})) : IO Unit := do
  match answer with
  | none => throw <| IO.userError s!"{label}: unexpected no solution"
  | some out =>
      if rationalMovesCost A.weight out.moves != cost then
        throw <| IO.userError s!"{label}: wrong movement cost: {rationalMovesCost A.weight out.moves}"
      if out.moves.length != slides then
        throw <| IO.userError s!"{label}: wrong secondary optimum: {out.moves.length}"
      if replay A {0, 1} out.moves != some out.target then
        throw <| IO.userError s!"{label}: directed slide replay failed"
      unless (out.target.sort (· ≤ ·)).all (fun u =>
          (out.target.sort (· ≤ ·)).all fun v => decide (u = v ∨ ¬pathFour.graph.Adj u v)) do
        throw <| IO.userError s!"{label}: terminal target is not independent"
      IO.println s!"PASS {label}: cost={cost}, slides={slides}, moves={out.moves}"

def check (A : RationalMatrixInput 4) (cost : ℚ) (slides : ℕ) : IO Unit := do
  checkResult "reference rational directed" A cost slides
    (solveRationalMatrixDiscovery pathFour A {0, 1} 2 (by decide) pathFour_bicliqueFree)
  let measured := A.solveMeasured pathFour {0, 1} 2 (by decide) pathFour_bicliqueFree
  unless measured.2 > 0 do throw <| IO.userError "directed measured: zero operation counter"
  checkResult "retained-matrix measured directed" A cost slides measured.1
  let binary := A.solveBinaryMeasured pathFour {0, 1} 2 (by decide) pathFour_bicliqueFree
  unless binary.2 ≥ measured.2 do throw <| IO.userError "directed binary counter below scalar counter"
  checkResult "retained-matrix binary directed" A cost slides binary.1

def checkUnreachable : IO Unit := do
  match solveRationalMatrixDiscovery pathFour noMovement {0, 1} 2 (by decide) pathFour_bicliqueFree with
  | none => IO.println "PASS reference rational directed: unreachable"
  | some _ => throw <| IO.userError "reference incorrectly reached an independent set without movement arcs"
  let measured := noMovement.solveMeasured pathFour {0, 1} 2 (by decide) pathFour_bicliqueFree
  unless measured.1.isNone do throw <| IO.userError "retained-matrix measured incorrectly accepted unreachable input"
  let binary := noMovement.solveBinaryMeasured pathFour {0, 1} 2 (by decide) pathFour_bicliqueFree
  unless binary.1.isNone do throw <| IO.userError "retained-matrix binary incorrectly accepted unreachable input"
  unless measured.2 > 0 ∧ binary.2 ≥ measured.2 do
    throw <| IO.userError "unreachable directed driver counters invalid"
  IO.println "PASS retained-matrix measured and binary directed: unreachable"

end IndependentSetDiscovery.Tests.RationalDiscovery

def main : IO Unit := do
  IndependentSetDiscovery.Tests.RationalDiscovery.check
    IndependentSetDiscovery.Tests.RationalDiscovery.fractionalMovement (1 / 3) 1
  IndependentSetDiscovery.Tests.RationalDiscovery.check
    IndependentSetDiscovery.Tests.RationalDiscovery.zeroMovement 0 1
  IndependentSetDiscovery.Tests.RationalDiscovery.checkUnreachable
