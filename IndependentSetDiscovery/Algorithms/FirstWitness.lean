import Mathlib.Tactic

namespace IndependentSetDiscovery.Algorithms

/-- Sequential self-reduction probe with its exact number of oracle calls. -/
def firstYes (p : α → Bool) : List α → Option α × ℕ
  | [] => (none, 0)
  | a :: as => if p a then (some a, 1) else
      let result := firstYes p as
      (result.1, result.2 + 1)

theorem firstYes_value (p : α → Bool) (as : List α) :
    (firstYes p as).1 = as.find? p := by
  induction as with
  | nil => rfl
  | cons a as ih => cases hp : p a <;> simp [firstYes, hp, ih]

theorem firstYes_calls_le (p : α → Bool) (as : List α) :
    (firstYes p as).2 ≤ as.length := by
  induction as with
  | nil => simp [firstYes]
  | cons a as ih => cases hp : p a <;> simp [firstYes, hp] <;> omega

theorem firstYes_some (p : α → Bool) (as : List α) (a : α)
    (h : (firstYes p as).1 = some a) : a ∈ as ∧ p a = true := by
  rw [firstYes_value] at h
  exact ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

theorem firstYes_exists (p : α → Bool) (as : List α)
    (h : ∃ a ∈ as, p a = true) : ∃ a, (firstYes p as).1 = some a := by
  cases heq : (firstYes p as).1 with
  | some a => exact ⟨a, rfl⟩
  | none =>
    rw [firstYes_value, List.find?_eq_none] at heq
    rcases h with ⟨a, ha, hp⟩
    exact False.elim (heq a ha hp)

end IndependentSetDiscovery.Algorithms
