import IndependentSetDiscovery.MeasuredDiscovery

/-! The budgeted decision consequence of Theorem 1.2. The budget is compared
in binary; no loop is indexed by its numerical value. The extra cost is an
explicit fixed polynomial in the binary budget length and graph size. -/

namespace IndependentSetDiscovery.BudgetedDiscovery

open ShortestPaths Algorithms Movement

def lengthCounted : List α → ℕ × ℕ
  | [] => (0, 1)
  | _ :: xs => let r := lengthCounted xs; (r.1 + 1, r.2 + 2)

theorem lengthCounted_spec (xs : List α) :
    (lengthCounted xs).1 = xs.length ∧ (lengthCounted xs).2 = 2*xs.length+1 := by
  induction xs with
  | nil => simp [lengthCounted]
  | cons x xs ih => simp [lengthCounted, ih.1, ih.2]; omega

def compareMoves (moves : List α) (budget : ℕ) : Bool × ℕ :=
  let size := lengthCounted moves
  let width := binaryRegisterWidth 0 0 size.1 (binaryLength budget)
  (decide (size.1 ≤ budget), (size.2+3)*binaryScalarTariff width)

theorem compareMoves_value (moves : List α) (budget : ℕ) :
    (compareMoves moves budget).1 = true ↔ moves.length ≤ budget := by
  simp [compareMoves, (lengthCounted_spec moves).1]

theorem compareMoves_work (moves : List α) (budget bound : ℕ) (h : moves.length ≤ bound) :
    (compareMoves moves budget).2 ≤
      4*(bound+1)*binaryScalarTariff (binaryRegisterWidth 0 0 bound (binaryLength budget)) := by
  unfold compareMoves
  dsimp only
  rw [(lengthCounted_spec moves).1, (lengthCounted_spec moves).2]
  apply Nat.mul_le_mul
  · omega
  · unfold binaryScalarTariff binaryRegisterWidth
    gcongr

def decideMeasured {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (budget : ℕ) : Bool × ℕ :=
  let result := MeasuredDiscovery.solveBinary a S d hd hG
  match result.1 with
  | none => (false, result.2+1)
  | some out =>
    let answer := compareMoves out.moves budget
    (answer.1, result.2+answer.2+1)

theorem decideMeasured_correct {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (budget : ℕ) :
    (decideMeasured a S d hd hG budget).1 = true ↔ DiscoveryWithin a.graph S budget := by
  unfold decideMeasured
  cases hresult : (MeasuredDiscovery.solveBinary a S d hd hG).1 with
  | none =>
    have hn := (MeasuredDiscovery.binary_none_iff a S d hd hG).mp hresult
    simp only [hresult, Bool.false_eq_true, false_iff]
    rintro ⟨T, m, hi, hs, _⟩
    exact hn ⟨T, m, hi, hs⟩
  | some out =>
    simp only [hresult, compareMoves_value]
    constructor
    · intro hb
      exact ⟨out.target, out.moves.length, out.independent, out.valid.slideSequence, hb⟩
    · rintro ⟨T, m, hi, hs, hb⟩
      exact (out.optimal T m hi hs).trans hb

theorem decideMeasured_work {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ S.card) (hG : BicliqueFree a.graph d d) (budget m : ℕ) :
    (decideMeasured a S d hd hG budget).2 ≤
      2^(30*d*S.card*(S.card.log2+1))*(n+m+1)^25 +
      4*(n^2+1)*binaryScalarTariff (binaryRegisterWidth 0 0 (n^2) (binaryLength budget)) + 1 := by
  have hbase := MeasuredDiscovery.binary_bound a S d hd hk hG m
  unfold decideMeasured
  cases hresult : (MeasuredDiscovery.solveBinary a S d hd hG).1 with
  | none => simp only [hresult]; omega
  | some out =>
    have hkn : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hlen : out.moves.length ≤ n^2 := by
      have hl := out.length_le
      simp only [Fintype.card_fin] at hl
      exact hl.trans (by simpa [pow_two] using Nat.mul_le_mul hkn (Nat.sub_le n 1))
    have hcompare := compareMoves_work out.moves budget (n^2) hlen
    simp only [hresult]
    omega

end IndependentSetDiscovery.BudgetedDiscovery
