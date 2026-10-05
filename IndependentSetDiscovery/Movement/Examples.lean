import IndependentSetDiscovery.Movement.PlanTable

/-! Executable smoke tests for the zero-token and occupied-path cases. -/

namespace IndependentSetDiscovery.Movement.Examples

def pathFour : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := by intro u v h; exact h.symm
  loopless := by intro u h; rcases h with h | h <;> omega

instance : DecidableRel pathFour.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def walkZeroThree : pathFour.Walk 0 3 :=
  .cons (show pathFour.Adj 0 1 by decide)
    (.cons (show pathFour.Adj 1 2 by decide) (.cons (show pathFour.Adj 2 3 by decide) .nil))

def walkOneTwo : pathFour.Walk 1 2 := .cons (by decide) .nil

def blockingPlan : RoutePlan pathFour {0, 1} {2, 3} where
  target := fun v => if v = 0 then 3 else if v = 1 then 2 else v
  injective := by
    intro u hu v hv heq
    have hu' : u = 0 ∨ u = 1 := by simpa using hu
    have hv' : v = 0 ∨ v = 1 := by simpa using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> simp_all
  image_eq := by decide
  cost := fun v => if v = 0 then 3 else if v = 1 then 1 else 0
  paths := by
    intro v hv
    by_cases h0 : v = 0
    · subst v
      exact ⟨walkZeroThree, by decide⟩
    · by_cases h1 : v = 1
      · subst v
        exact ⟨walkOneTwo, by decide⟩
      · exact False.elim (by simp [h0, h1] at hv)

def emptyPlan : RoutePlan pathFour ∅ ∅ where
  target := id
  injective := fun _ _ _ _ h => h
  image_eq := by simp
  cost := fun _ => 0
  paths := by intro x hx; exact False.elim (Finset.notMem_empty x hx)

def zeroVertexPlan : RoutePlan (⊥ : SimpleGraph (Fin 0)) ∅ ∅ where
  target := id
  injective := fun _ _ _ _ h => h
  image_eq := by simp
  cost := fun _ => 0
  paths := by intro x hx; exact False.elim (Finset.notMem_empty x hx)

theorem bot_sequence_has_equal_endpoints {n : ℕ} {Q T : Finset (Fin 2)}
    (h : SlideSequence (⊥ : SimpleGraph (Fin 2)) Q T n) : Q = T := by
  cases h with
  | nil => rfl
  | cons hs _ =>
    rcases hs with ⟨u, _, v, _, huv, _⟩
    exact False.elim huv

theorem disconnected_assignment_infinite :
    assignmentDistance (⊥ : SimpleGraph (Fin 2)) {0} {1} = ⊤ := by
  apply (assignmentDistance_eq_top_iff _ _ _).mpr
  rintro ⟨n, hs⟩
  have h := bot_sequence_has_equal_endpoints hs
  have hne : ({0} : Finset (Fin 2)) ≠ {1} := by decide
  exact hne h

-- The assigned 0--3 walk initially runs through the token at 1. These evaluate
-- the compiled reconstruction, including the destination-exchange branch.
#eval (reconstruct blockingPlan).moves
#eval (reconstruct blockingPlan).work
#eval (reconstruct emptyPlan).moves
#eval (reconstructCached blockingPlan).moves
#eval (reconstructCached blockingPlan).work
#eval (reconstructCached emptyPlan).moves
#eval (reconstructCached zeroVertexPlan).moves

theorem blockingPlan_valid :
    ValidMoves pathFour {0, 1} (reconstruct blockingPlan).moves {2, 3} :=
  (reconstruct blockingPlan).valid

theorem emptyPlan_valid :
    ValidMoves pathFour ∅ (reconstruct emptyPlan).moves ∅ :=
  (reconstruct emptyPlan).valid

end IndependentSetDiscovery.Movement.Examples
