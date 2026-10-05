import IndependentSetDiscovery.Algorithms.PathDecoder
import IndependentSetDiscovery.Movement.Reduction

/-! # Eager finite caching of selected path witnesses

`cacheFin` evaluates the source at each index once, storing a nested product
through closures. Lookup follows at most `n` branches and never reruns the
source computation. This deliberately uses a linear lookup bound, not a claim
of constant-time lookup for arbitrary functions.
-/

namespace IndependentSetDiscovery.Movement

def cacheFin : {n : ℕ} → {α : Fin n → Type} →
    ((i : Fin n) → α i) → ((i : Fin n) → α i)
  | 0, _, _ => fun i => Fin.elim0 i
  | n + 1, α, f =>
    let first := f 0
    let rest := cacheFin (α := fun i : Fin n => α i.succ) (fun i => f i.succ)
    fun i => Fin.cases first rest i

theorem cacheFin_eq {n : ℕ} {α : Fin n → Type} (f : (i : Fin n) → α i) :
    cacheFin f = f := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => f j.succ)) j

def cachedSelectedPaths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (x : S → Fin n)
    (hx : (movementInstance G S).Selection x) :
    (s : S) → {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)} := by
  let α := fun v : Fin n =>
    if hv : v ∈ S then
      {p : G.Walk v (x ⟨v, hv⟩) // p.length = G.dist v (x ⟨v, hv⟩)}
    else PUnit
  let source : (v : Fin n) → α v := by
    intro v
    by_cases hv : v ∈ S
    · simp only [α, dif_pos hv]
      exact ShortestPaths.walkOfReachable G v (x ⟨v, hv⟩)
        ((movementInstance_mem G S ⟨v, hv⟩ _).mp (hx.1 ⟨v, hv⟩))
    · simp only [α, dif_neg hv]
      exact PUnit.unit
  let stored := cacheFin source
  intro s
  have h := stored s.val
  simpa only [α, dif_pos s.property] using h

end IndependentSetDiscovery.Movement
