import IndependentSetDiscovery.Extensions.DirectedReconstructionBridge
import IndependentSetDiscovery.Extensions.Discovery
import IndependentSetDiscovery.Algorithms.WeightedEncodedReduction
import IndependentSetDiscovery.Algorithms.WeightedSelectedPaths
import IndependentSetDiscovery.Algorithms.RationalMatrixInput
import IndependentSetDiscovery.Algorithms.ShortestPaths

/-! # Executable rational two-graph discovery, Corollary 5.6 -/

namespace IndependentSetDiscovery

variable {V : Type*} [DecidableEq V]

def rationalMovesCost (w : V → V → ℚ) (moves : List (V × V)) : ℚ :=
  (moves.map fun e => w e.1 e.2).sum

theorem WeightedDirected.ValidMoves.rationalSlideSequence
    {D : V → V → Prop} {w : V → V → ℚ} {S T : Finset V} {moves : List (V × V)}
    (h : WeightedDirected.ValidMoves D S moves T) :
    RationalSlideSequence D w S T (rationalMovesCost w moves) moves.length := by
  induction h with
  | nil Q => exact .nil Q
  | cons hu hv huv _ ih => exact .cons ⟨hu, hv, huv, rfl⟩ ih

theorem WeightedDirected.ValidMoves.integerized_cost
    {D : V → V → Prop} {w : V → V → ℚ} {z : V → V → ℕ} {C : ℕ}
    (hscale : ∀ u v, D u v → (z u v : ℚ) = C * w u v)
    {S T : Finset V} {moves : List (V × V)}
    (h : WeightedDirected.ValidMoves D S moves T) :
    (WeightedDirected.movesCost z moves : ℚ) = C * rationalMovesCost w moves := by
  induction h with
  | nil Q => simp [WeightedDirected.movesCost, rationalMovesCost]
  | cons hu hv huv ht ih =>
      simp only [WeightedDirected.movesCost, rationalMovesCost, List.map_cons, List.sum_cons,
        Nat.cast_add] at *
      rw [ih, hscale _ _ huv]
      ring

structure RationalDiscoveryResult [Fintype V] (Gf : SimpleGraph V)
    (D : V → V → Prop) (w : V → V → ℚ) (S : Finset V) where
  target : Finset V
  moves : List (V × V)
  valid : WeightedDirected.ValidMoves D S moves target
  optimal : RationalLexOptimal Gf D w S target (rationalMovesCost w moves) moves.length
  length_le : moves.length ≤ S.card * (Fintype.card V - 1)
  pathDecodingWork : ℕ
  pathDecodingWork_le : pathDecodingWork ≤
    S.card * (2 * (Fintype.card V) ^ 2 + 24 * Fintype.card V + 24) +
      Fintype.card V * ((Fintype.card V) ^ 2 + 16 * Fintype.card V + 20) + 8
  reconstructionWork : ℕ
  work_le : reconstructionWork ≤ (S.card * (Fintype.card V - 1) + 1) *
    WeightedDirected.reconstructionStepBudget (Fintype.card V) (S.card * (Fintype.card V - 1))

def rationalizeDiscoveryResult [Fintype V]
    {Gf : SimpleGraph V} {D : V → V → Prop} {w : V → V → ℚ}
    {z : V → V → ℕ} {C : ℕ} (hC : 0 < C)
    (hscale : ∀ u v, D u v → (z u v : ℚ) = C * w u v)
    {S : Finset V} (out : WeightedDirected.DirectedDiscoveryResult Gf D z S) :
    RationalDiscoveryResult Gf D w S :=
  { target := out.target
    moves := out.moves
    valid := out.valid
    optimal := by
      obtain ⟨c, hc, heq⟩ := rational_optimal_of_integerized hC hscale out.optimal
      have hcost := out.valid.integerized_cost hscale
      have hpos : (0 : ℚ) < C := by exact_mod_cast hC
      have hsame : rationalMovesCost w out.moves = c := by
        exact (mul_left_cancel₀ (ne_of_gt hpos)) (hcost.symm.trans heq)
      simpa only [hsame] using hc
    length_le := out.length_le
    pathDecodingWork := 0
    pathDecodingWork_le := Nat.zero_le _
    reconstructionWork := out.reconstructionWork
    work_le := out.work_le }

namespace WeightedDirected

open ShortestPaths WeightedShortestPaths

variable {n : ℕ} [NeZero n]

local instance preparedGraphDecidable {D : Fin n → Fin n → Prop} [DecidableRel D]
    {z : Fin n → Fin n → ℕ} (P : WeightedShortestPaths.PreparedRows D z)
    (Gf : SimpleGraph (Fin n)) [DecidableRel Gf.Adj] (S : Finset (Fin n)) :
    DecidableRel (P.movementInstance Gf S).graph.Adj :=
  inferInstanceAs (DecidableRel Gf.Adj)

/-- Reconstruct using cached paths; every selected path is decoded once and
its exact decoder counter is retained in the returned result. -/
def reconstructRationalPreparedSelection (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v) (S : Finset (Fin n))
    (P : PreparedRows D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
      integerArcWeight D w u v + 1))
    (x : S → Fin n)
    (hopt : (movementInstance a.graph D
      (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) * integerArcWeight D w u v + 1)
      S).Optimal x) : RationalDiscoveryResult a.graph D w S := by
  let z := integerArcWeight D w
  let C := scalarizationBase S.card (Fintype.card (Fin n))
  let scalar := fun u v => C * z u v + 1
  let cached := P.prepareSelectedPaths S x (fun s =>
    (movementInstance_mem a.graph D scalar S s (x s)).mp (hopt.1.1 s))
  let paths := fun s : S =>
    (⟨(cached.paths s).val, by
      refine ⟨(cached.paths s).property.1, ?_⟩
      simpa only [Fintype.card_fin] using (cached.paths s).property.2⟩ :
      {p : DWalk D s.val (x s) //
        p.cost scalar = (distance D scalar s.val (x s)).toNat ∧
        p.length ≤ Fintype.card (Fin n) - 1})
  let out := reconstructOptimalSelection (w := z) x hopt paths
  let rationalOut := rationalizeDiscoveryResult (arcDenominator_pos D w)
    (integerArcWeight_cast D w hnonneg) out
  exact { rationalOut with
    pathDecodingWork := cached.work
    pathDecodingWork_le := by simpa only [Fintype.card_fin] using cached.work_le }

/-- All preprocessing, target optimization, path decoding and reconstruction
are executable; the concrete encoded optimizer owns all search state. -/
def solveRationalDirectedDiscoveryPrepared (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v) (S : Finset (Fin n))
    (P : PreparedRows D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
      integerArcWeight D w u v + 1))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (RationalDiscoveryResult a.graph D w S) := by
  match hx : P.solveEncoded a S d with
  | none => exact none
  | some x =>
      exact some (reconstructRationalPreparedSelection a D w hnonneg S P x
        (P.solveEncoded_some a S hd hG hx))

theorem solveRationalDirectedDiscoveryPrepared_none_iff (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v) (S : Finset (Fin n))
    (P : PreparedRows D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
      integerArcWeight D w u v + 1))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    solveRationalDirectedDiscoveryPrepared a D w hnonneg S P d hd hG = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence D w S T c k := by
  unfold solveRationalDirectedDiscoveryPrepared
  split <;> rename_i hx
  · have h := (P.solveEncoded_none_iff a S hd hG).mp hx
    have h' : ¬ ∃ x, (rationalMovementInstance a.graph D w S).Selection x := h
    simp only [true_iff]
    exact (rational_no_selection_iff_unreachable a.graph D w hnonneg S).mp h'
  · rename_i x
    simp only [Option.some_ne_none, false_iff, not_not]
    have h := P.solveEncoded_some a S hd hG hx
    have hs : ∃ x, (rationalMovementInstance a.graph D w S).Selection x := ⟨x, h.1⟩
    by_contra hn
    exact ((rational_no_selection_iff_unreachable a.graph D w hnonneg S).mpr hn) hs

def solveRationalDirectedDiscovery (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (RationalDiscoveryResult a.graph D w S) :=
  solveRationalDirectedDiscoveryPrepared a D w hnonneg S
    (prepareRows D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
      integerArcWeight D w u v + 1)) d hd hG

theorem solveRationalDirectedDiscovery_none_iff (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    solveRationalDirectedDiscovery a D w hnonneg S d hd hG = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence D w S T c k :=
  solveRationalDirectedDiscoveryPrepared_none_iff a D w hnonneg S _ d hd hG

/-- The actual matrix entrypoint materializes the integer and scalar weights
before preparing its cached shortest-path rows. -/
def rationalPreparedForConfiguration (A : RationalMatrixInput n) (S : Finset (Fin n)) :
    PreparedRows A.relation (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
      integerArcWeight A.relation A.weight u v + 1) := by
  let P := A.prepared S
  have heq : (A.scalarMatrix (scalarizationBase S.card n)).weight =
      (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) *
        integerArcWeight A.relation A.weight u v + 1) := by
    funext u v
    simp only [A.scalarMatrix_weight, Fintype.card_fin]
  exact heq ▸ P

def solveRationalMatrixDiscovery (a : ShortestPaths.MatrixGraph n)
    (A : RationalMatrixInput n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (RationalDiscoveryResult a.graph A.relation A.weight S) :=
  solveRationalDirectedDiscoveryPrepared a A.relation A.weight A.nonneg S
    (rationalPreparedForConfiguration A S) d hd hG

theorem solveRationalMatrixDiscovery_none_iff (a : ShortestPaths.MatrixGraph n)
    (A : RationalMatrixInput n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    solveRationalMatrixDiscovery a A S d hd hG = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence A.relation A.weight S T c k :=
  solveRationalDirectedDiscoveryPrepared_none_iff a A.relation A.weight A.nonneg S _ d hd hG

end WeightedDirected
end IndependentSetDiscovery
