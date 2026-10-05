import IndependentSetDiscovery.Algorithms.EagerComplete
import IndependentSetDiscovery.Algorithms.EagerOptimizationBounds

namespace IndependentSetDiscovery.Algorithms

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- Full measured optimization, including concrete preprocessing and every
initial rational-budget division, has the same bounded-search factor. -/
theorem optimizeEagerComplete_cost_le [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost threshold L rows).2 ≤
      (6*numericSize L (fun i => rows[i]) cost+6+(k+1)*(n+1)) *
        (128*(k+1)^2*(n+1)^2) * treeBound (k*maxThreshold) k := by
  let A : Fin k → Finset (Fin n) := fun i => rows[i]
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let C := eagerOracleBound k n maxThreshold
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ)/D)
  let p := fun b =>
    let answer := eagerDecide R cost threshold (initial b)
    (answer.1, answer.2+1)
  have hCbase : 128*(k+1)^2*(n+1)^2 ≤ C :=
    Nat.le_mul_of_pos_right _ (one_le_treeBound _ _)
  have hC : 5 ≤ C := by
    have hk : 1 ≤ (k+1)^2 := Nat.one_le_pow _ _ (by omega)
    have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    have hh : 128 ≤ 128*(k+1)^2*(n+1)^2 := by
      calc
        128 = 128*1*1 := by norm_num
        _ ≤ _ := by gcongr
    omega
  have hp : ∀ b, (p b).2 ≤ C+1 := by
    intro b
    have hh := eagerDecide_uniform_cost_le R cost threshold maxThreshold hthreshold (initial b)
    change _+1 ≤ C+1
    omega
  have hsearch : (leastBudgetMeasured p U).2 ≤ (Nat.log2 U+2)*2*C := by
    have hh := leastBudgetMeasured_cost_le p (C+1) hp U
    have hmul := Nat.mul_le_mul_left (Nat.log2 U+2) (by omega : C+1+4 ≤ 2*C)
    nlinarith
  have hl : L.card ≤ k := by simpa using Finset.card_le_univ L
  have hw (b : ℕ) :
      (recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).2 ≤
        (k+1)*(n+1)*C := by
    exact (recoverEager_cost_le R cost threshold maxThreshold hthreshold _ _).trans
      (by gcongr)
  have hprep : (prepareMeasured cost L rows).2 ≤ C := by
    have hh := prepareMeasured_cost cost L rows
    nlinarith
  have hnum := optimizationCalls_le_numericSize L A cost
  have hfactor : (Nat.log2 U+2)*2 + 2 + (k+1)*(n+1) ≤
      6*numericSize L A cost+6+(k+1)*(n+1) := by
    change Nat.log2 U + 2 ≤ 3*numericSize L A cost+2 at hnum
    omega
  have htotal : (optimizeEagerComplete R cost threshold L rows).2 ≤
      ((Nat.log2 U+2)*2+2+(k+1)*(n+1))*C := by
    unfold optimizeEagerComplete
    simp only [prepareMeasured_value]
    change (match (leastBudgetMeasured p U).1 with
      | none => (none, (prepareMeasured cost L rows).2+(leastBudgetMeasured p U).2)
      | some b => ((recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).1,
        (prepareMeasured cost L rows).2+(leastBudgetMeasured p U).2+1+
          (recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).2)).2 ≤ _
    split
    · dsimp only
      calc
        _ ≤ C + (Nat.log2 U+2)*2*C := Nat.add_le_add hprep hsearch
        _ = ((Nat.log2 U+2)*2+1)*C := by ring
        _ ≤ _ := Nat.mul_le_mul_right C (by omega)
    · rename_i b hb
      dsimp only
      have hrec := hw b
      calc
        _ ≤ C + (Nat.log2 U+2)*2*C + C + (k+1)*(n+1)*C := by
          exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hprep hsearch) (by omega)) hrec
        _ = _ := by ring
  calc
    _ ≤ (6*numericSize L A cost+6+(k+1)*(n+1))*C :=
      htotal.trans (Nat.mul_le_mul_right C hfactor)
    _ = _ := by unfold C eagerOracleBound A; ring

end IndependentSetDiscovery.Algorithms
