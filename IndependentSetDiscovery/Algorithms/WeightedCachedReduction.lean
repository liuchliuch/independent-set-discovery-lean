import IndependentSetDiscovery.Algorithms.WeightedPathDecoder
import IndependentSetDiscovery.Extensions.DirectedReduction

/-!
# Cached executable two-graph reduction

All directed shortest-path rows are materialized once. The weighted instance
reads candidates and costs from those cached vectors, and typed minimum-weight
walks are decoded from the same stored routes. Its equality to the semantic
reduction eliminates any shortest-path oracle from Corollary 5.6.
-/
namespace IndependentSetDiscovery.WeightedShortestPaths

open WeightedDirected Finset
variable {n : ℕ} (D : Fin n → Fin n → Prop) [DecidableRel D]
variable (w : Fin n → Fin n → ℕ)

/-- Materialize all source rows and sum their actual preprocessing counters. -/
def allPairs : Vector (Table n) n × ℕ :=
  let rows := Vector.ofFn (shortestPaths D w)
  (rows.map Prod.fst, 4 * n + (rows.toList.map Prod.snd).sum)

@[simp] theorem allPairs_get (s : Fin n) :
    (allPairs D w).1[s] = (shortestPaths D w s).1 := by simp [allPairs]

theorem allPairs_cost :
    (allPairs D w).2 ≤ 4 * n + 3 * n ^ 2 + 5 * n ^ 3 + 24 * n ^ 4 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => shortestPaths_cost D w s)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [allPairs, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  nlinarith

/-- Runtime data plus an erased correctness certificate for its cached rows. -/
structure PreparedRows where
  rows : Vector (Table n) n
  correct : ∀ s : Fin n, rows[s] = (shortestPaths D w s).1

def prepareRows : PreparedRows D w :=
  ⟨(allPairs D w).1, allPairs_get D w⟩

namespace PreparedRows
variable {D w} (P : PreparedRows D w)

/-- Constant-time lookup in the two materialized vectors. -/
def entry (s v : Fin n) : Option (Route n) := P.rows[s][v]

theorem row_sound (s v : Fin n) {p : Route n} (hp : P.entry s v = some p) :
    Valid D w s v p ∧ p.vertices.length ≤ n - 1 := by
  unfold entry at hp
  rw [P.correct s] at hp
  exact shortestPaths_sound D w s v hp

theorem row_score_eq_distance (s v : Fin n) {p : Route n}
    (hp : P.entry s v = some p) : (p.score : ℕ∞) = WeightedDirected.distance D w s v := by
  unfold entry at hp
  rw [P.correct s] at hp
  exact shortestPaths_score_eq_distance D w s v hp

theorem row_exists_iff (s v : Fin n) :
    (∃ p, P.entry s v = some p) ↔ WeightedDirected.distance D w s v ≠ ⊤ := by
  unfold entry
  rw [P.correct s, shortestPaths_exists_iff]
  exact ENat.iInf_coe_ne_top.symm

/-- Decode a stored row entry; no shortest-path search is repeated. -/
def walkOption (s v : Fin n) : Option (DWalk D s v) × ℕ :=
  match P.entry s v with
  | none => (none, 1)
  | some p =>
    let decoded := decodeTo D s v p
    (decoded.1, decoded.2 + 1)

theorem walkOption_exists_iff (s v : Fin n) :
    (∃ q, (P.walkOption s v).1 = some q) ↔ WeightedDirected.distance D w s v ≠ ⊤ := by
  constructor
  · rintro ⟨q, _⟩
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) q.distance_le
  · intro h
    obtain ⟨p, hp⟩ := (P.row_exists_iff s v).mpr h
    obtain ⟨q, hq, _, _⟩ := decodeTo_valid D w (P.row_sound s v hp).1
    exact ⟨q, by simp [walkOption, hp, hq]⟩

theorem walkOption_spec (s v : Fin n) (q : DWalk D s v)
    (hq : (P.walkOption s v).1 = some q) :
    (q.cost w : ℕ∞) = WeightedDirected.distance D w s v ∧ q.length ≤ n - 1 := by
  unfold walkOption at hq
  cases hp : P.entry s v with
  | none => simp [hp] at hq
  | some p =>
    simp only [hp] at hq
    obtain ⟨r, hr, hscore, hlen⟩ := decodeTo_valid D w (P.row_sound s v hp).1
    have he : r = q := Option.some.inj (hr.symm.trans hq)
    subst r
    refine ⟨?_, hlen.le.trans (P.row_sound s v hp).2⟩
    rw [hscore]
    exact P.row_score_eq_distance s v hp

/-- An actual cached minimum-weight path with the tight `n-1` hop certificate. -/
def walkOfFiniteDistance (s v : Fin n) (h : WeightedDirected.distance D w s v ≠ ⊤) :
    {q : DWalk D s v // (q.cost w : ℕ∞) = WeightedDirected.distance D w s v ∧ q.length ≤ n - 1} :=
  let hp : (P.walkOption s v).1.isSome := by
    obtain ⟨q, hq⟩ := (P.walkOption_exists_iff s v).mpr h
    simp [hq]
  let q := (P.walkOption s v).1.get hp
  ⟨q, P.walkOption_spec s v q (Option.some_get hp).symm⟩

theorem walkOption_cost (s v : Fin n) :
    (P.walkOption s v).2 ≤ n ^ 2 + 8 * n + 4 := by
  unfold walkOption
  cases hp : P.entry s v with
  | none => simp [hp]
  | some p =>
    have hd := decodeTo_cost D s v p
    have hlen := (P.row_sound s v hp).2.trans (Nat.sub_le n 1)
    have hsq := Nat.pow_le_pow_left hlen 2
    simp only [hp]
    nlinarith

/-- The actual weighted-transversal input, computed only from cached entries. -/
def movementInstance (Gf : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    WeightedInstance S (Fin n) where
  graph := Gf
  candidates := fun s => univ.filter fun v => (P.entry s.val v).isSome
  cost := fun s v => match P.entry s.val v with
    | none => 0
    | some p => (p.score : ℚ)
  nonneg := by
    intro s v _
    split <;> positivity

theorem movementInstance_mem (Gf : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (s : S) (v : Fin n) :
    v ∈ (P.movementInstance Gf S).candidates s ↔ WeightedDirected.distance D w s.val v ≠ ⊤ := by
  simp only [movementInstance, mem_filter, mem_univ, true_and]
  rw [← P.row_exists_iff s.val v]
  cases hp : P.entry s.val v <;> simp

theorem movementInstance_cost (Gf : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (s : S) (v : Fin n) :
    (P.movementInstance Gf S).cost s v = ((WeightedDirected.distance D w s.val v).toNat : ℚ) := by
  cases hp : P.entry s.val v with
  | none =>
    have hd : WeightedDirected.distance D w s.val v = ⊤ := by
      by_contra hn
      obtain ⟨p, hq⟩ := (P.row_exists_iff s.val v).mpr hn
      simp [hp] at hq
    simp [movementInstance, hp, hd]
  | some p =>
    have hd := P.row_score_eq_distance s.val v hp
    simp [movementInstance, hp, ← hd]

theorem movementInstance_eq (Gf : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    P.movementInstance Gf S = WeightedDirected.movementInstance Gf D w S := by
  have hA : (P.movementInstance Gf S).candidates =
      (WeightedDirected.movementInstance Gf D w S).candidates := by
    funext s
    ext v
    rw [P.movementInstance_mem, WeightedDirected.movementInstance_mem]
  have hc : (P.movementInstance Gf S).cost =
      (WeightedDirected.movementInstance Gf D w S).cost := by
    funext s v
    exact P.movementInstance_cost Gf S s v
  have hg : (P.movementInstance Gf S).graph =
      (WeightedDirected.movementInstance Gf D w S).graph := rfl
  generalize hI : P.movementInstance Gf S = I at *
  generalize hJ : WeightedDirected.movementInstance Gf D w S = J at *
  cases I
  cases J
  cases hg
  cases hA
  cases hc
  rfl

end PreparedRows
end IndependentSetDiscovery.WeightedShortestPaths
