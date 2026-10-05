import IndependentSetDiscovery.Movement.CachedPaths
import Mathlib.Algebra.BigOperators.Fin

/-! Exact source-call accounting for the eager dependent cache used by
reconstruction. The counted refinement invokes each source once and returns
the same cached function. Lookup is a linear traversal of at most `n` cached
branches; it never reruns source preprocessing. -/

namespace IndependentSetDiscovery.Movement

def cacheFinCounted : {n : ℕ} → {α : Fin n → Type} →
    ((i : Fin n) → α i × ℕ) → ((i : Fin n) → α i) × ℕ
  | 0, _, _ => (fun i => Fin.elim0 i, 0)
  | n + 1, α, f =>
    let first := f 0
    let rest := cacheFinCounted (α := fun i : Fin n => α i.succ) (fun i => f i.succ)
    ((fun i => Fin.cases first.1 rest.1 i), first.2 + rest.2 + 1)

theorem cacheFinCounted_value {n : ℕ} {α : Fin n → Type} (f : (i : Fin n) → α i × ℕ) :
    (cacheFinCounted f).1 = cacheFin (fun i => (f i).1) := by
  rw [cacheFin_eq]
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have h := congrFun (ih (fun j => f j.succ)) j
      simpa only [cacheFin_eq] using h

theorem cacheFinCounted_work {n : ℕ} {α : Fin n → Type} (f : (i : Fin n) → α i × ℕ) :
    (cacheFinCounted f).2 = n + ∑ i, (f i).2 := by
  induction n with
  | zero => simp [cacheFinCounted]
  | succ n ih =>
    simp only [cacheFinCounted, ih, Fin.sum_univ_succ]
    omega

theorem cacheFinCounted_work_le {n : ℕ} {α : Fin n → Type}
    (f : (i : Fin n) → α i × ℕ) (bound : ℕ) (h : ∀ i, (f i).2 ≤ bound) :
    (cacheFinCounted f).2 ≤ n * (bound + 1) := by
  rw [cacheFinCounted_work]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  nlinarith

open ShortestPaths

/-- Actual shortest-path source work over the selected starting vertices.
The extra `n*(|S|+2)` pays for cache construction and linear finite-set
membership tests across all `n` possible source vertices. -/
def selectedPathsSourceWork {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n) : ℕ :=
  n * (S.card + 2) + ∑ s : S, (walkOption G s.val (x s)).2

theorem selectedPathsSourceWork_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n) :
    selectedPathsSourceWork G S x ≤ n * (S.card + 2) +
      S.card * (2 * n ^ 4 + 18 * n ^ 3 + 6 * n ^ 2 + 11 * n + 4) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => walkOption_cost G s.val (x s))
  simpa [selectedPathsSourceWork, Fintype.card_coe, nsmul_eq_mul] using
    Nat.add_le_add_left hs (n * (S.card + 2))

/-- The executable selected-path cache with source counters produced alongside
the actual paths. Target-map lookup is supplied by the caller; encoded drivers
use the explicitly materialized target vectors. -/
def cachedSelectedPathsCounted {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n)
    (hx : (movementInstance G S).Selection x) :
    ((s : S) → {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) × ℕ := by
  let α := fun v : Fin n =>
    if hv : v ∈ S then
      {p : G.Walk v (x ⟨v, hv⟩) // p.length = G.dist v (x ⟨v, hv⟩)}
    else PUnit
  let source : (v : Fin n) → α v × ℕ := by
    intro v
    by_cases hv : v ∈ S
    · let path := walkOfReachableWithCost G v (x ⟨v, hv⟩)
        ((movementInstance_mem G S ⟨v, hv⟩ _).mp (hx.1 ⟨v, hv⟩))
      let value : α v := by simpa only [α, dif_pos hv] using path.1
      exact (value, path.2 + S.card + 1)
    · let value : α v := by simp only [α, dif_neg hv]; exact PUnit.unit
      exact (value, S.card + 1)
  let stored := cacheFinCounted source
  let paths : (s : S) → {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)} := by
    intro s
    have h := stored.1 s.val
    simpa only [α, dif_pos s.property] using h
  exact (paths, stored.2)

theorem cachedSelectedPathsCounted_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n) (hx : (movementInstance G S).Selection x) :
    (cachedSelectedPathsCounted G S x hx).1 = cachedSelectedPaths G S x hx := by
  funext s
  simp only [cachedSelectedPathsCounted, cachedSelectedPaths,
    cacheFinCounted_value, cacheFin_eq, dif_pos s.property]
  rfl

theorem cachedSelectedPathsCounted_work {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n) (hx : (movementInstance G S).Selection x) :
    (cachedSelectedPathsCounted G S x hx).2 = selectedPathsSourceWork G S x := by
  unfold cachedSelectedPathsCounted
  rw [cacheFinCounted_work]
  simp only [walkOfReachableWithCost_work]
  have hs : (∑ v : Fin n, if hv : v ∈ S then (walkOption G v (x ⟨v, hv⟩)).2 + S.card + 1
      else S.card + 1) = (∑ s : S, (walkOption G s.val (x s)).2) + n * (S.card+1) := by
    have hsplit : ∀ v : Fin n,
        (if hv : v ∈ S then (walkOption G v (x ⟨v,hv⟩)).2 + S.card + 1 else S.card+1) =
        (if hv : v ∈ S then (walkOption G v (x ⟨v,hv⟩)).2 else 0) + (S.card+1) := by
      intro v
      split_ifs <;> omega
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    · exact (Finset.sum_attach_eq_sum_dite S (fun s => (walkOption G s.val (x s)).2)).symm
    · simp only [Nat.cast_id]; ring
  calc
    _ = n + (∑ v : Fin n, if hv : v ∈ S then
        (walkOption G v (x ⟨v,hv⟩)).2 + S.card+1 else S.card+1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : v ∈ S <;> simp [h]
    _ = _ := by rw [hs]; unfold selectedPathsSourceWork; ring

end IndependentSetDiscovery.Movement
