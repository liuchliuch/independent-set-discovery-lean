import IndependentSetDiscovery.Algorithms.EncodedInput

/-!
Independent executable cross-checks. The oracle enumerates all functions from
labels to vertices and checks the raw input tables. It does not call solver
correctness theorems, selection predicates, threshold lemmas, or solver search.
The finite suite exercises all 8 simple graphs on 3 vertices, all 64 incidence
tables for 2 labels, and three cost patterns, including exact fractions.
-/
namespace IndependentSetDiscovery.Tests.Exhaustive

open Algorithms ShortestPaths

/-- Cartesian product enumeration independent of the solver's search tree. -/
def assignments : (k n : ℕ) → List (Fin k → Fin n)
  | 0, _ => [fun i => Fin.elim0 i]
  | k+1, n => (List.finRange n).flatMap fun v =>
      (assignments k n).map fun x => Fin.cases v x

def valid {k n : ℕ} (E : EncodedInput k n) (x : Fin k → Fin n) : Bool :=
  (List.finRange k).all (fun i => E.allowed[i][x i]) &&
  (List.finRange k).all (fun i => (List.finRange k).all fun j =>
    i == j || (x i != x j && !E.graphData.matrix[x i][x j]))

def totalCost {k n : ℕ} (E : EncodedInput k n) (x : Fin k → Fin n) : ℚ :=
  ((List.finRange k).map fun i => E.costs[i][x i]).sum

def oracleCosts {k n : ℕ} (E : EncodedInput k n) : List ℚ :=
  ((assignments k n).filter (valid E)).map (totalCost E)

def minimum : List ℚ → Option ℚ
  | [] => none
  | x :: xs => some (xs.foldl min x)

def checkOptimizer {k n : ℕ} (E : EncodedInput k n) (label : String) : IO Unit := do
  let costs := oracleCosts E
  let measured := E.solveMeasured 2
  if measured.2 == 0 then throw <| IO.userError s!"{label}: zero operation counter"
  match measured.1, minimum costs with
  | none, none => pure ()
  | some x, some best =>
    unless valid E x do throw <| IO.userError s!"{label}: returned illegal assignment"
    unless totalCost E x == best do
      throw <| IO.userError s!"{label}: solver cost {totalCost E x}, oracle {best}"
  | _, _ => throw <| IO.userError s!"{label}: feasibility disagreement"

def budgets : List ℚ := [-1, 0, 1/3, 1, 2, 5]

def checkBudgets {k n : ℕ} (E : EncodedInput k n) (label : String) : IO Unit := do
  let costs := oracleCosts E
  for b in budgets do
    let state : EagerState k n := ⟨Finset.univ, E.candidateTable, b⟩
    let answer := eagerDecide (Compatible E.graph) E.normalizedCost
      (balancedSearchThreshold 2) state
    let expected := costs.any fun c => decide (c ≤ b)
    unless answer.1 == expected do
      throw <| IO.userError s!"{label}: budget {b}, got {answer.1}, oracle {expected}"

def graphThree (mask : ℕ) : MatrixGraph 3 where
  matrix := Vector.ofFn fun u => Vector.ofFn fun v =>
    decide (u ≠ v) && mask.testBit
      (if u.val + v.val = 1 then 0 else if u.val + v.val = 2 then 1 else 2)
  symmetric := by intro u v; simp [Nat.add_comm, eq_comm]
  diagonal := by intro u; simp

def smallInput (graphMask incidenceMask costSeed : ℕ) : EncodedInput 2 3 where
  graphData := graphThree graphMask
  allowed := Vector.ofFn fun i => Vector.ofFn fun v => incidenceMask.testBit (3*i.val+v.val)
  costs := Vector.ofFn fun i => Vector.ofFn fun v =>
    if costSeed = 0 then 0 else
      (((costSeed+3*i.val+v.val)%7 : ℕ) : ℚ) / (((costSeed+i.val+2*v.val)%3+1 : ℕ) : ℚ)
  nonneg := by
    intro i v _
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs
    · norm_num
    · positivity

def emptyGraph (n : ℕ) : MatrixGraph n where
  matrix := Vector.replicate n (Vector.replicate n false)
  symmetric := by intros; simp
  diagonal := by intros; simp

def emptyInput (k n : ℕ) : EncodedInput k n where
  graphData := emptyGraph n
  allowed := Vector.replicate k (Vector.replicate n false)
  costs := Vector.replicate k (Vector.replicate n 0)
  nonneg := by intros; simp

def fullPrefixInput : EncodedInput 2 64 where
  graphData := emptyGraph 64
  allowed := Vector.replicate 2 (Vector.replicate 64 true)
  costs := Vector.replicate 2 (Vector.replicate 64 0)
  nonneg := by intros; simp

def checkFullPrefix : IO Unit := do
  let E := fullPrefixInput
  checkOptimizer E "full-prefix/64"
  checkBudgets E "full-prefix/64"
  let state : EagerState 2 64 := ⟨Finset.univ, E.candidateTable, 0⟩
  match (eagerStepCounted (Compatible E.graph) E.normalizedCost
      (balancedSearchThreshold 2) state).1 with
  | .yes => pure ()
  | _ => throw <| IO.userError "full-prefix/64: root did not take affirmative prefix branch"
  IO.println "PASS full-prefix: 64-vertex overlapping rows, root affirmative branch, oracle optimum 0"

end IndependentSetDiscovery.Tests.Exhaustive

open IndependentSetDiscovery.Tests.Exhaustive in
def main : IO Unit := do
    let mut count := 0
    for graphMask in List.range 8 do
      for incidenceMask in List.range 64 do
        for seed in List.range 3 do
          let E := smallInput graphMask incidenceMask seed
          let label := s!"graph={graphMask}/incidence={incidenceMask}/cost={seed}"
          checkOptimizer E label
          checkBudgets E label
          count := count + 1
    IO.println s!"PASS exhaustive encoded solver: {count} inputs; all 8 graphs and 64 candidate tables; {count * budgets.length} budget comparisons"
    checkOptimizer (emptyInput 0 0) "zero-label/zero-vertex"
    checkOptimizer (emptyInput 0 3) "zero-label"
    checkOptimizer (emptyInput 2 0) "zero-vertex"
    checkOptimizer (emptyInput 2 3) "empty-candidate"
    IO.println "PASS empty boundaries: zero labels, zero vertices, empty candidate rows"
    checkFullPrefix
