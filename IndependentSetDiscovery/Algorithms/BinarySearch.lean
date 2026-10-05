import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace IndependentSetDiscovery.Algorithms

/-- Binary search on a closed interval known to contain a feasible upper endpoint.
The recursion is structurally bounded by the number of bits, never by the budget. -/
def bisect (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    if p mid then bisect p fuel lo mid else bisect p fuel (mid + 1) hi

/-- The exact number of calls to the decision predicate. -/
def bisectCalls (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    1 + if p mid then bisectCalls p fuel lo mid else bisectCalls p fuel (mid + 1) hi

theorem bisectCalls_eq (p : ℕ → Bool) (fuel lo hi : ℕ) :
    bisectCalls p fuel lo hi = fuel := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih => simp [bisectCalls, ih, Nat.add_comm]

/-- The search returns the least feasible natural-number budget.
`hi - lo < 2^fuel` is the explicit numerical stopping invariant. -/
theorem bisect_correct (p : ℕ → Bool)
    (mono : ∀ a b, a ≤ b → p a = true → p b = true) :
    ∀ fuel lo hi, lo ≤ hi → hi - lo < 2 ^ fuel →
      p hi = true → (∀ n < lo, p n = false) →
      p (bisect p fuel lo hi) = true ∧
      (∀ n < bisect p fuel lo hi, p n = false) ∧
      lo ≤ bisect p fuel lo hi ∧ bisect p fuel lo hi ≤ hi := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hle hwidth hhi hlow
    have heq : hi = lo := by simp only [pow_zero] at hwidth; omega
    subst hi
    exact ⟨hhi, hlow, le_rfl, le_rfl⟩
  | succ fuel ih =>
    intro lo hi hle hwidth hhi hlow
    let mid := (lo + hi) / 2
    have hmidlo : lo ≤ mid := by dsimp [mid]; omega
    have hmidhi : mid ≤ hi := by dsimp [mid]; omega
    have hwidth' : hi - lo < 2 ^ fuel * 2 := by simpa [pow_succ] using hwidth
    have hleft : mid - lo < 2 ^ fuel := by dsimp [mid]; omega
    by_cases hp : p mid = true
    · have hr := ih lo mid hmidlo hleft hp hlow
      simpa [bisect, mid, hp] using
        And.intro hr.1 (And.intro hr.2.1 (And.intro hr.2.2.1 (hr.2.2.2.trans hmidhi)))
    · have hpfalse : p mid = false := by cases h : p mid <;> simp_all
      have hmidlt : mid < hi := by
        by_contra h
        have : mid = hi := by omega
        simp_all
      have hright : hi - (mid + 1) < 2 ^ fuel := by dsimp [mid]; omega
      have hbelow : ∀ n < mid + 1, p n = false := by
        intro n hn
        by_cases hpn : p n = true
        · have := mono n mid (by omega) hpn
          simp_all
        · cases h : p n <;> simp_all
      have hr := ih (mid + 1) hi (by omega) hright hhi hbelow
      simpa [bisect, mid, hpfalse] using
        And.intro hr.1 (And.intro hr.2.1 (And.intro (by omega : lo ≤ bisect p fuel (mid + 1) hi) hr.2.2.2))

def leastBudget (p : ℕ → Bool) (upper : ℕ) : Option ℕ :=
  if p upper then some (bisect p (Nat.log2 upper + 1) 0 upper) else none

theorem leastBudget_some_spec (p : ℕ → Bool) (upper : ℕ)
    (mono : ∀ a b, a ≤ b → p a = true → p b = true)
    (hu : p upper = true) :
    ∃ answer, leastBudget p upper = some answer ∧ p answer = true ∧
      (∀ n < answer, p n = false) ∧ answer ≤ upper := by
  have hwidth : upper - 0 < 2 ^ (Nat.log2 upper + 1) := by
    simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) upper
  have hs := bisect_correct p mono (Nat.log2 upper + 1) 0 upper (Nat.zero_le _) hwidth hu
    (by intro n hn; omega)
  exact ⟨_, by simp [leastBudget, hu], hs.1, hs.2.1, hs.2.2.2⟩

theorem leastBudget_none_iff (p : ℕ → Bool) (upper : ℕ) :
    leastBudget p upper = none ↔ p upper = false := by
  simp only [leastBudget]
  cases h : p upper <;> simp [h]

/-- One upper-bound test and exactly one call per binary-search bit. -/
def optimizationCalls (upper : ℕ) : ℕ := Nat.log2 upper + 2

end IndependentSetDiscovery.Algorithms
