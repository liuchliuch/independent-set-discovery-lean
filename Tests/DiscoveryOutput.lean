import IndependentSetDiscovery.DiscoveryAlgorithm
import IndependentSetDiscovery.MeasuredDiscovery

namespace IndependentSetDiscovery.Tests.DiscoveryOutput

open ShortestPaths Movement

def pathFour : MatrixGraph 4 where
  matrix := Vector.ofFn fun u => Vector.ofFn fun v =>
    decide (u.val + 1 = v.val ∨ v.val + 1 = u.val)
  symmetric := by intros; simp [Bool.or_comm]
  diagonal := by intro u; simp

theorem pathFour_bicliqueFree : BicliqueFree pathFour.graph 2 2 := by
  unfold BicliqueFree HasBiclique
  decide

def slideOK (Q : Finset (Fin 4)) (uv : Fin 4 × Fin 4) : Bool :=
  decide (uv.1 ∈ Q ∧ uv.2 ∉ Q ∧ pathFour.graph.Adj uv.1 uv.2)

def replay (Q : Finset (Fin 4)) : List (Fin 4 × Fin 4) → Option (Finset (Fin 4))
  | [] => some Q
  | uv :: moves =>
    if slideOK Q uv then replay (insert uv.2 (Q.erase uv.1)) moves else none

/-- Check raw returned moves independently, for reference and final drivers. -/
def checkResult (label : String) (S : Finset (Fin 4)) (expected : ℕ)
    (answer : Option (DiscoveryResult pathFour.graph S)) : IO Unit := do
  match answer with
  | none => throw <| IO.userError s!"{label}: unexpected unreachable result"
  | some out =>
    if out.moves.length != expected then
      throw <| IO.userError s!"{label}: wrong optimum: {out.moves.length}, expected {expected}"
    if replay S out.moves != some out.target then
      throw <| IO.userError s!"{label}: returned moves fail independent replay"
    if !((out.target.sort (· ≤ ·)).all fun u => (out.target.sort (· ≤ ·)).all fun v =>
        decide (u = v ∨ ¬pathFour.graph.Adj u v)) then
      throw <| IO.userError s!"{label}: terminal target is not independent"
    IO.println s!"PASS {label}: {out.moves.length} slides, target={(out.target.sort (· ≤ ·))}"

def check (S : Finset (Fin 4)) (expected : ℕ) : IO Unit := do
  checkResult "reference discovery" S expected
    (solveDiscovery pathFour S 2 (by decide) pathFour_bicliqueFree)
  let measured := MeasuredDiscovery.solve pathFour S 2 (by decide) pathFour_bicliqueFree
  unless measured.2 > 0 do throw <| IO.userError "measured discovery: zero operation counter"
  checkResult "measured discovery" S expected measured.1
  let binary := MeasuredDiscovery.solveBinary pathFour S 2 (by decide) pathFour_bicliqueFree
  unless binary.2 ≥ measured.2 do throw <| IO.userError "binary discovery counter below scalar counter"
  checkResult "binary measured discovery" S expected binary.1

end IndependentSetDiscovery.Tests.DiscoveryOutput

def main : IO Unit := do
  IndependentSetDiscovery.Tests.DiscoveryOutput.check {0, 1} 1
  IndependentSetDiscovery.Tests.DiscoveryOutput.check {0, 2} 0
  IndependentSetDiscovery.Tests.DiscoveryOutput.check ∅ 0
