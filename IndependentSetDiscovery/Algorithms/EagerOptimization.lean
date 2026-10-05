import IndependentSetDiscovery.Algorithms.MeasuredExecution
import IndependentSetDiscovery.Algorithms.OracleWork

namespace IndependentSetDiscovery.Algorithms

/-- Measured probing evaluates each attempted predicate exactly once. -/
def probeMeasured (p : α → Bool × ℕ) : List α → Option α × ℕ
  | [] => (none, 0)
  | a :: as =>
    let answer := p a
    if answer.1 then (some a, answer.2 + 1)
    else let tail := probeMeasured p as; (tail.1, answer.2 + 1 + tail.2)

theorem probeMeasured_value (p : α → Bool × ℕ) (xs : List α) :
    (probeMeasured p xs).1 = xs.find? (fun a => (p a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases h : (p a).1 <;> simp [probeMeasured, h, ih]

/-- Binary search together with primitive midpoint/control work and measured
predicate invocations. -/
def bisectMeasured (p : ℕ → Bool × ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
    let mid := (lo+hi)/2
    let answer := p mid
    let rest := if answer.1 then bisectMeasured p fuel lo mid else bisectMeasured p fuel (mid+1) hi
    (rest.1, answer.2 + rest.2 + 4)

theorem bisectMeasured_value (p : ℕ → Bool × ℕ) : ∀ fuel lo hi,
    (bisectMeasured p fuel lo hi).1 = bisect (fun n => (p n).1) fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; rfl
  | succ fuel ih =>
    intro lo hi
    cases h : (p ((lo+hi)/2)).1 <;> simp [bisectMeasured, bisect, h, ih]

def leastBudgetMeasured (p : ℕ → Bool × ℕ) (U : ℕ) : Option ℕ × ℕ :=
  let answer := p U
  if answer.1 then
    let rest := bisectMeasured p (Nat.log2 U+1) 0 U
    (some rest.1, answer.2 + rest.2 + 1)
  else (none, answer.2+1)

theorem leastBudgetMeasured_value (p : ℕ → Bool × ℕ) (U : ℕ) :
    (leastBudgetMeasured p U).1 = leastBudget (fun n => (p n).1) U := by
  cases h : (p U).1 <;> simp [leastBudgetMeasured, leastBudget, h, bisectMeasured_value]

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- Measured self-reduction over eagerly stored candidate rows. -/
def recoverMeasured [Inhabited (Fin n)] (oracle : EagerState k n → Bool × ℕ) :
    ℕ → EagerState k n → Option (Fin k → Fin n) × ℕ
  | 0, s => if s.labels = ∅ ∧ 0 ≤ s.budget then (some (fun _ => default), 2) else (none, 2)
  | fuel + 1, s =>
    if h : s.labels.Nonempty then
      let i := s.labels.min' h
      let choices := (s.rows[i]).sort (· ≤ ·)
      let probes := probeMeasured (fun v =>
        let child := eagerChild R cost s i v
        let answer := oracle child
        (answer.1, eagerChildWork s + answer.2)) choices
      let overhead := 4*((s.rows[i]).card+1)^2 + 2*(s.labels.card+1)
      match probes.1 with
      | none => (none, probes.2+overhead)
      | some v =>
        let tail := recoverMeasured oracle fuel (eagerChild R cost s i v)
        (tail.1.map (fun x => Function.update x i v),
          probes.2+overhead+eagerChildWork s+tail.2+1)
    else if 0 ≤ s.budget then (some (fun _ => default), 2) else (none, 2)

theorem recoverMeasured_refinement [Inhabited (Fin n)]
    (oracle : EagerState k n → Bool × ℕ) (old : State (Fin k) (Fin n) → Bool)
    (horacle : ∀ s, (oracle s).1 = old s.toState) :
    ∀ fuel s, (recoverMeasured R cost oracle fuel s).1 = (recover R cost old fuel s.toState).1 := by
  intro fuel
  induction fuel with
  | zero => intro s; simp only [recoverMeasured, recover, EagerState.toState]; split_ifs <;> rfl
  | succ fuel ih =>
    intro s
    by_cases h : s.labels.Nonempty
    · let i := s.labels.min' h
      have hprobe : (probeMeasured (fun v =>
          let answer := oracle (eagerChild R cost s i v)
          (answer.1, eagerChildWork s+answer.2)) ((s.rows[i]).sort (· ≤ ·))).1 =
          (firstYes (fun v => old (child R cost s.toState i v)) ((s.rows[i]).sort (· ≤ ·))).1 := by
        rw [probeMeasured_value, firstYes_value]
        simp [horacle, eagerChild_refinement]
      simp only [recoverMeasured, recover, EagerState.toState, dif_pos h]
      rw [hprobe]
      cases hp : (firstYes (fun v => old (child R cost s.toState i v)) ((s.rows[i]).sort (· ≤ ·))).1 with
      | none =>
        simp only [i, EagerState.toState] at hp
        simp only [hp]
      | some v =>
        simp only [i, EagerState.toState] at hp
        simp only [hp]
        rw [ih]
        simp [eagerChild, EagerState.ofState, EagerState.toState]
    · simp only [recoverMeasured, recover, EagerState.toState, dif_neg h]
      split_ifs <;> rfl

/-- Concrete eager optimizer. Preprocessing uses the finite integer and rational
operations whose counted folds are provided in `PrimitiveCosts`. -/
def optimizeEager [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) : Option (Fin k → Fin n) × ℕ :=
  let A := fun i => rows[i]
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ)/D)
  let oracle := eagerDecide R cost threshold
  let search := leastBudgetMeasured (fun b => oracle (initial b)) U
  match search.1 with
  | none => (none, search.2)
  | some b =>
    let witness := recoverMeasured R cost oracle L.card (initial b)
    (witness.1, search.2+witness.2)

theorem optimizeEager_refinement [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEager R cost threshold L rows).1 =
      optimize R cost costPrefixOperations threshold L (fun i => rows[i]) := by
  have ho := eagerDecide_refinement R cost threshold
  unfold optimizeEager optimize
  dsimp only
  rw [leastBudgetMeasured_value]
  simp only [ho, EagerState.toState, budgetState]
  split
  · rename_i hcase
    simp only [hcase]
  · rename_i b hcase
    simp only [hcase]
    exact recoverMeasured_refinement R cost _ _ ho _ _

end IndependentSetDiscovery.Algorithms
