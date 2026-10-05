import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A deterministic bounded-branching interpreter

The interpreter below is executable. Its cost counts one state expansion, plus all
recursive state expansions. It deliberately evaluates every child (rather than relying
on short-circuit evaluation), so the returned counter is an exact cost in this model.
The cost of constructing a node is accounted for separately by `weightedCost`.
-/

namespace IndependentSetDiscovery.Algorithms

inductive Instruction (σ : Type*) where
  | yes : Instruction σ
  | no : Instruction σ
  | branch : List σ → Instruction σ
  deriving Inhabited

/-- Execute a finite depth of a search; `fuel` bounds recursive edges, not nodes. -/
def run (step : σ → Instruction σ) : ℕ → σ → Bool × ℕ
  | 0, s =>
    match step s with
    | .yes => (true, 1)
    | .no => (false, 1)
    | .branch _ => (false, 1)
  | fuel + 1, s =>
    match step s with
    | .yes => (true, 1)
    | .no => (false, 1)
    | .branch children =>
      let answers := children.map (run step fuel)
      (answers.any Prod.fst, 1 + (answers.map Prod.snd).sum)

/-- Semantic contracts are local facts about the concrete node construction. -/
structure CorrectStep (step : σ → Instruction σ) (P : σ → Prop) (rank : σ → ℕ) : Prop where
  yes : ∀ s, step s = .yes → P s
  no : ∀ s, step s = .no → ¬ P s
  branch : ∀ s children, step s = .branch children →
    (P s ↔ ∃ child ∈ children, P child)
  decreases : ∀ s children, step s = .branch children →
    ∀ child ∈ children, rank child < rank s
  positive : ∀ s children, step s = .branch children → 0 < rank s

/-- The bounded interpreter is an exact decision procedure once all local facts hold. -/
theorem run_correct (step : σ → Instruction σ) (P : σ → Prop) (rank : σ → ℕ)
    (h : CorrectStep step P rank) :
    ∀ fuel s, rank s ≤ fuel → ((run step fuel s).1 = true ↔ P s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs
    cases hstep : step s with
    | yes => simp [run, hstep, h.yes s hstep]
    | no => simp [run, hstep, h.no s hstep]
    | branch children => have := h.positive s children hstep; omega
  | succ fuel ih =>
    intro s hs
    cases hstep : step s with
    | yes => simp [run, hstep, h.yes s hstep]
    | no => simp [run, hstep, h.no s hstep]
    | branch children =>
      simp only [run, hstep, List.any_map, Function.comp_def, List.any_eq_true,
        Prod.fst]
      rw [h.branch s children hstep]
      apply exists_congr
      intro child
      constructor
      · rintro ⟨hc, hb⟩
        exact ⟨hc, (ih child (by have := h.decreases s children hstep child hc; omega)).mp hb⟩
      · rintro ⟨hc, hp⟩
        exact ⟨hc, (ih child (by have := h.decreases s children hstep child hc; omega)).mpr hp⟩

/-- Exact worst-case number of state expansions of a full bounded search tree. -/
def treeBound (branching : ℕ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 => 1 + branching * treeBound branching depth

theorem one_le_treeBound (branching depth : ℕ) : 1 ≤ treeBound branching depth := by
  cases depth <;> simp [treeBound]

theorem list_sum_le_length_mul {xs : List α} {f : α → ℕ} {bound : ℕ}
    (h : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    omega

/-- A verified explicit node bound; the hypothesis is a bound on the computed list. -/
theorem run_cost_le (step : σ → Instruction σ) (branching : ℕ)
    (hb : ∀ s children, step s = .branch children → children.length ≤ branching) :
    ∀ fuel s, (run step fuel s).2 ≤ treeBound branching fuel := by
  intro fuel
  induction fuel with
  | zero => intro s; cases h : step s <;> simp [run, h, treeBound]
  | succ fuel ih =>
    intro s
    cases h : step s with
    | yes => simpa [run, h] using one_le_treeBound branching (fuel + 1)
    | no => simpa [run, h] using one_le_treeBound branching (fuel + 1)
    | branch children =>
      simp only [run, h, List.map_map, Function.comp_def, treeBound, Prod.snd]
      have hsum := list_sum_le_length_mul (xs := children)
        (f := fun child => (run step fuel child).2) (bound := treeBound branching fuel)
        (fun child _ => ih child)
      have hmul := Nat.mul_le_mul_right (treeBound branching fuel) (hb s children h)
      omega

/-- The coarse bound works even when the branching factor is zero or one. -/
theorem treeBound_le_power (branching depth : ℕ) :
    treeBound branching depth ≤ (branching + 1) ^ depth := by
  induction depth with
  | zero => simp [treeBound]
  | succ depth ih =>
    have hpos : 1 ≤ (branching + 1) ^ depth := Nat.one_le_pow _ _ (by omega)
    simp only [treeBound, pow_succ]
    nlinarith

/-- For branching factor at least two this is the paper's geometric-tree bound. -/
theorem treeBound_add_one_le (branching depth : ℕ) (hb : 2 ≤ branching) :
    treeBound branching depth + 1 ≤ 2 * branching ^ depth := by
  induction depth with
  | zero => simp [treeBound]
  | succ depth ih =>
    simp only [treeBound, pow_succ]
    nlinarith

def weightedCost (step : σ → Instruction σ) (perNode fuel : ℕ) (s : σ) : ℕ :=
  perNode * (run step fuel s).2

theorem weightedCost_le (step : σ → Instruction σ) (branching perNode fuel : ℕ)
    (hb : ∀ s children, step s = .branch children → children.length ≤ branching) (s : σ) :
    weightedCost step perNode fuel s ≤ perNode * treeBound branching fuel := by
  exact Nat.mul_le_mul_left perNode (run_cost_le step branching hb fuel s)

/-- Restricting the branching bound to the ranks actually visited is sufficient. -/
theorem run_cost_le_of_rank (step : σ → Instruction σ) (rank : σ → ℕ)
    (branching maxRank : ℕ)
    (hdec : ∀ s children, step s = .branch children →
      ∀ child ∈ children, rank child < rank s)
    (hb : ∀ s children, rank s ≤ maxRank → step s = .branch children →
      children.length ≤ branching) :
    ∀ fuel s, rank s ≤ maxRank → (run step fuel s).2 ≤ treeBound branching fuel := by
  intro fuel
  induction fuel with
  | zero => intro s hs; cases h : step s <;> simp [run, h, treeBound]
  | succ fuel ih =>
    intro s hs
    cases h : step s with
    | yes => simpa [run, h] using one_le_treeBound branching (fuel + 1)
    | no => simpa [run, h] using one_le_treeBound branching (fuel + 1)
    | branch children =>
      simp only [run, h, List.map_map, Function.comp_def, treeBound]
      have hsum := list_sum_le_length_mul (xs := children)
        (f := fun child => (run step fuel child).2) (bound := treeBound branching fuel)
        (fun child hc => ih child (by have := hdec s children h child hc; omega))
      have hmul := Nat.mul_le_mul_right (treeBound branching fuel) (hb s children hs h)
      omega

end IndependentSetDiscovery.Algorithms
