import IndependentSetDiscovery.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The weighted static problem

Definition 2.3 allows candidate sets to overlap and costs to depend on the
coordinate. Costs are meaningful, and required to be nonnegative, only on
the corresponding candidate set. The normalization below extends them by
zero outside that set for use by the recursive algorithm.
-/

namespace IndependentSetDiscovery

/-- Data of a weighted independent-transversal optimization instance. -/
structure WeightedInstance (ι V : Type*) where
  graph : SimpleGraph V
  candidates : ι → Finset V
  cost : ι → V → ℚ
  nonneg : ∀ i v, v ∈ candidates i → 0 ≤ cost i v

/-- Distinct nonadjacent vertices are mutually compatible destinations. -/
def Compatible {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v

theorem compatible_symm {V : Type*} (G : SimpleGraph V) : Symmetric (Compatible G) := by
  intro u v h
  exact ⟨Ne.symm h.1, fun hvu => h.2 (G.symm hvu)⟩

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (Compatible G) := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

namespace WeightedInstance

variable {ι V : Type*} (I : WeightedInstance ι V)

/-- A genuine feasible transversal: one candidate per label, no repeats or edges. -/
def Selection (x : ι → V) : Prop :=
  (∀ i, x i ∈ I.candidates i) ∧ Function.Injective x ∧
    ∀ i j, i ≠ j → ¬ I.graph.Adj (x i) (x j)

/-- Label-dependent cost, summed once for each label. -/
def selectionCost [Fintype ι] (x : ι → V) : ℚ := ∑ i, I.cost i (x i)

/-- The budgeted decision predicate. Nonnegative budgets are a separate input
promise; keeping all rational budgets here is convenient for residual states. -/
def Within [Fintype ι] (B : ℚ) : Prop :=
  ∃ x, I.Selection x ∧ I.selectionCost x ≤ B

/-- A minimum-cost solution is a feasible selection dominating every other one. -/
def Optimal [Fintype ι] (x : ι → V) : Prop :=
  I.Selection x ∧ ∀ y, I.Selection y → I.selectionCost x ≤ I.selectionCost y

theorem selection_iff_compatible (x : ι → V) :
    I.Selection x ↔ (∀ i, x i ∈ I.candidates i) ∧
      ∀ i j, i ≠ j → Compatible I.graph (x i) (x j) := by
  constructor
  · rintro ⟨hmem, hinj, hadj⟩
    exact ⟨hmem, fun i j hij => ⟨fun h => hij (hinj h), hadj i j hij⟩⟩
  · rintro ⟨hmem, hpair⟩
    refine ⟨hmem, ?_, fun i j hij => (hpair i j hij).2⟩
    intro i j heq
    by_contra hne
    exact (hpair i j hne).1 heq

theorem selectionCost_nonneg [Fintype ι] {x : ι → V} (h : I.Selection x) :
    0 ≤ I.selectionCost x :=
  Finset.sum_nonneg fun i _ => I.nonneg i (x i) (h.1 i)

theorem Within.nonneg [Fintype ι] {B : ℚ} (h : I.Within B) : 0 ≤ B := by
  rcases h with ⟨x, hx, hcost⟩
  exact (I.selectionCost_nonneg hx).trans hcost

theorem Within.mono [Fintype ι] {B C : ℚ} (h : I.Within B) (hBC : B ≤ C) :
    I.Within C := by
  rcases h with ⟨x, hx, hcost⟩
  exact ⟨x, hx, hcost.trans hBC⟩

variable [DecidableEq V]

/-- Extend the input cost by zero off the corresponding candidate set. -/
def normalizedCost (i : ι) (v : V) : ℚ :=
  if v ∈ I.candidates i then I.cost i v else 0

theorem normalizedCost_nonneg (i : ι) (v : V) : 0 ≤ I.normalizedCost i v := by
  unfold normalizedCost
  split_ifs with h
  · exact I.nonneg i v h
  · exact le_rfl

theorem normalizedCost_eq {i : ι} {v : V} (h : v ∈ I.candidates i) :
    I.normalizedCost i v = I.cost i v := by simp [normalizedCost, h]

theorem sum_normalizedCost [Fintype ι] {x : ι → V} (h : I.Selection x) :
    (∑ i, I.normalizedCost i (x i)) = I.selectionCost x := by
  apply Finset.sum_congr rfl
  intro i _
  exact I.normalizedCost_eq (h.1 i)

theorem Selection.independent_range [Fintype ι] {x : ι → V} (h : I.Selection x) :
    Independent I.graph (Finset.univ.image x) := by
  intro u hu v hv huv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  exact h.2.2 i j (fun hij => huv (congrArg x hij))

theorem Selection.card_range [Fintype ι] {x : ι → V} (h : I.Selection x) :
    (Finset.univ.image x).card = Fintype.card ι := by
  rw [Finset.card_image_iff.mpr h.2.1.injOn, Finset.card_univ]

end WeightedInstance

end IndependentSetDiscovery
