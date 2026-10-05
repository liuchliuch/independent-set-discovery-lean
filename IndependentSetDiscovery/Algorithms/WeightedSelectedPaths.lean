import IndependentSetDiscovery.Algorithms.WeightedCachedReduction
import IndependentSetDiscovery.Algorithms.EncodedMovement
import IndependentSetDiscovery.Movement.PlanTable

/-! # Decode each selected shortest path once, into an eager dependent table -/

namespace IndependentSetDiscovery.WeightedShortestPaths.PreparedRows

open WeightedDirected EncodedMovement Movement

variable {n : ℕ} {D : Fin n → Fin n → Prop} [DecidableRel D]
variable {w : Fin n → Fin n → ℕ} (P : PreparedRows D w)

def countedWalkOfFiniteDistance (s v : Fin n) (h : distance D w s v ≠ ⊤) :
    {q : DWalk D s v // q.cost w = (distance D w s v).toNat ∧ q.length ≤ n - 1} × ℕ :=
  let decoded := P.walkOption s v
  let hp : decoded.1.isSome := by
    obtain ⟨q, hq⟩ := (P.walkOption_exists_iff s v).mpr h
    simp [decoded, hq]
  let q := decoded.1.get hp
  (⟨q, by
    have hs := P.walkOption_spec s v q (Option.some_get hp).symm
    refine ⟨?_, hs.2⟩
    have heq := congrArg ENat.toNat hs.1
    simpa using heq⟩, decoded.2)

theorem countedWalk_cost (s v : Fin n) (h : distance D w s v ≠ ⊤) :
    (P.countedWalkOfFiniteDistance s v h).2 ≤ n ^ 2 + 8 * n + 4 :=
  P.walkOption_cost s v

abbrev SelectedPath (S : Finset (Fin n)) (x : S → Fin n) (s : S) :=
  {q : DWalk D s.val (x s) //
    q.cost w = (distance D w s.val (x s)).toNat ∧ q.length ≤ n - 1}

structure SelectedPaths (S : Finset (Fin n)) (x : S → Fin n) where
  paths : ∀ s, SelectedPath (D := D) (w := w) S x s
  work : ℕ
  work_le : work ≤ S.card * (2 * n ^ 2 + 24 * n + 24) + n * (n ^ 2 + 16 * n + 20) + 8

def selectedPathCell (S : Finset (Fin n)) (x : S → Fin n)
    (h : ∀ s : S, distance D w s.val (x s) ≠ ⊤) (i : Fin S.card) :
    (Sigma fun j : Fin S.card => SelectedPath (D := D) (w := w) S x (labelEquiv S j)) × ℕ :=
  let s := labelEquiv S i
  let decoded := P.countedWalkOfFiniteDistance s.val (x s) (h s)
  (⟨i, decoded.1⟩, decoded.2 + n ^ 2 + 16 * n + 16)

def inverseIndexCell (S : Finset (Fin n)) (v : Fin n) : Option (Fin S.card) × ℕ :=
  (if hv : v ∈ S then some ((labelEquiv S).symm ⟨v, hv⟩) else none,
    n ^ 2 + 16 * n + 16)

/-- The returned getters perform only bounded vector access and proof-erased
casts. Decoding and inverse-index computation happen in the eager loops. -/
def prepareSelectedPaths (S : Finset (Fin n)) (x : S → Fin n)
    (h : ∀ s : S, distance D w s.val (x s) ≠ ⊤) : SelectedPaths (D := D) (w := w) S x := by
  let cells := Vector.ofFn (P.selectedPathCell S x h)
  let table : FinTable (fun i : Fin S.card => SelectedPath (D := D) (w := w) S x (labelEquiv S i)) :=
    { entries := cells.map Prod.fst
      indexed := by intro i; simp [cells, selectedPathCell] }
  let inverse := Vector.ofFn (inverseIndexCell S)
  let getPath : ∀ s : S, SelectedPath (D := D) (w := w) S x s := fun s => by
    have hi : (inverse[s.val]).1 = some ((labelEquiv S).symm s) := by
      simp [inverse, inverseIndexCell, s.property]
    let index := (inverse[s.val]).1.get (by simp [inverse, inverseIndexCell, s.property])
    have heq : labelEquiv S index = s := by simp [index, inverse, inverseIndexCell, s.property]
    exact heq ▸ table.get index
  refine
    { paths := getPath
      work := 4 * S.card + 4 * n + 8 + (cells.toList.map Prod.snd).sum +
        (inverse.toList.map Prod.snd).sum
      work_le := ?_ }
  have hc : (∑ i : Fin S.card, (P.selectedPathCell S x h i).2) ≤
      S.card * (2 * n ^ 2 + 24 * n + 20) := by
    calc
      _ ≤ ∑ _i : Fin S.card, (2 * n ^ 2 + 24 * n + 20) := by
        apply Finset.sum_le_sum
        intro i hi
        have hd := P.countedWalk_cost (labelEquiv S i).val (x (labelEquiv S i)) (h _)
        dsimp [selectedPathCell]
        omega
      _ = _ := by simp
  simp only [cells, inverse, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, inverseIndexCell, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

end IndependentSetDiscovery.WeightedShortestPaths.PreparedRows
