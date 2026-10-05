import IndependentSetDiscovery.Algorithms.WeightedCachedReduction
import IndependentSetDiscovery.Algorithms.BitComplexity

/-!
# Explicit finite directed weighted input and binary preprocessing bounds

Adjacency and weight queries are reads from two finite vectors. The generic
Bellman--Ford core therefore does not assume a constant-time external oracle.
The binary bound covers every cached score and every candidate formed during
a relaxation; zero weights require one binary digit.
-/
namespace IndependentSetDiscovery.WeightedShortestPaths

open WeightedDirected Algorithms Finset

/-- A directed weighted graph supplied as actual finite adjacency/weight tables.
Weights at absent arcs are harmless input entries and are never traversed. -/
structure MatrixInput (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  weights : Vector (Vector ℕ n) n
  deriving Repr

namespace MatrixInput
variable {n : ℕ} (A : MatrixInput n)

def relation (u v : Fin n) : Prop := A.adjacency[u][v] = true
instance : DecidableRel A.relation := fun _ _ => inferInstanceAs (Decidable (_ = true))

def weight (u v : Fin n) : ℕ := A.weights[u][v]

/-- The numeric encoding length of the weight matrix, plus one framing digit. -/
def numericBits : ℕ := 1 + ∑ p : Fin n × Fin n, binaryLength (A.weight p.1 p.2)

/-- Finite input preparation, with no implicit graph or weight oracle. -/
def prepared : PreparedRows A.relation A.weight := prepareRows A.relation A.weight

def preprocessRAMWork : ℕ := (allPairs A.relation A.weight).2

/-- Schoolbook bit-operation tariff: each RAM primitive is charged the square
of a uniform bound on its numeric operands. This includes addition, comparison,
indexing and control overhead; it is deliberately conservative. -/
def preprocessBitWork : ℕ := A.preprocessRAMWork * (n + A.numericBits + 2) ^ 2

theorem numericBits_pos : 0 < A.numericBits := by unfold numericBits; omega

theorem arc_binaryLength_le (u v : Fin n) :
    binaryLength (A.weight u v) ≤ A.numericBits := by
  have h := Finset.single_le_sum (f := fun p : Fin n × Fin n =>
    binaryLength (A.weight p.1 p.2)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (u, v))
  unfold numericBits
  exact h.trans (Nat.le_add_left _ _)

theorem arc_weight_le (u v : Fin n) : A.weight u v ≤ 2 ^ A.numericBits := by
  apply (nat_lt_two_pow_bits (A.weight u v)).le.trans
  apply Nat.pow_le_pow_right (by decide)
  exact A.arc_binaryLength_le u v

/-- This covers even a candidate route with one extra trial edge. -/
theorem valid_score_binaryLength {s v : Fin n} {p : Route n}
    (hp : Valid A.relation A.weight s v p) (hlen : p.vertices.length ≤ n + 1) :
    binaryLength p.score ≤ n + A.numericBits + 2 := by
  have hscore := valid_score_le A.relation A.weight hp
    (fun u v _ => A.arc_weight_le u v)
  have hpow : p.score ≤ 2 ^ (n + 1 + A.numericBits) := by
    calc
      _ ≤ p.vertices.length * 2 ^ A.numericBits := hscore
      _ ≤ (n + 1) * 2 ^ A.numericBits := Nat.mul_le_mul_right _ hlen
      _ ≤ 2 ^ (n + 1) * 2 ^ A.numericBits :=
        Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = _ := (pow_add _ _ _).symm
  have h := binaryLength_le_of_le_pow hpow
  omega

theorem table_score_binaryLength (s v : Fin n) {fuel : ℕ} (hfuel : fuel ≤ n)
    {p : Route n} (hp : (table A.relation A.weight s fuel).1[v] = some p) :
    binaryLength p.score ≤ n + A.numericBits + 2 := by
  have hs := table_sound A.relation A.weight s fuel v p hp
  exact A.valid_score_binaryLength hs.1 (by omega)

theorem shortestPaths_score_binaryLength (s v : Fin n) {p : Route n}
    (hp : (shortestPaths A.relation A.weight s).1[v] = some p) :
    binaryLength p.score ≤ n + A.numericBits + 2 :=
  A.table_score_binaryLength s v (Nat.sub_le n 1) hp

theorem prepared_score_binaryLength (s v : Fin n) {p : Route n}
    (hp : A.prepared.entry s v = some p) :
    binaryLength p.score ≤ n + A.numericBits + 2 := by
  have hs := A.prepared.row_sound s v hp
  exact A.valid_score_binaryLength hs.1 (by omega)

/-- All-sources weighted preprocessing has a fixed polynomial RAM bound. -/
theorem preprocessRAMWork_le :
    A.preprocessRAMWork ≤ 4 * n + 3 * n ^ 2 + 5 * n ^ 3 + 24 * n ^ 4 :=
  allPairs_cost A.relation A.weight

/-- The explicit finite-table preprocessing remains polynomial with binary
weights; the exponent does not depend on their numeric values. -/
theorem preprocessBitWork_le :
    A.preprocessBitWork ≤ (4 * n + 3 * n ^ 2 + 5 * n ^ 3 + 24 * n ^ 4) *
      (n + A.numericBits + 2) ^ 2 :=
  Nat.mul_le_mul_right _ A.preprocessRAMWork_le

end MatrixInput
end IndependentSetDiscovery.WeightedShortestPaths
