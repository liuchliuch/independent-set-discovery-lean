import IndependentSetDiscovery.Extensions.DirectedPaths
import IndependentSetDiscovery.Extensions.DirectedAssignment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Executable nonnegative weighted directed shortest paths

A materialized vector Bellman--Ford table keeps a route and its accumulated
natural weight. Selection compares weight, not hop count. Zero-weight arcs,
directed cycles, missing routes, and length-zero routes are supported.

The work counter charges primitive arc tests, weight/array reads, additions,
comparisons, and list construction. Thus the cubic RAM bound is independent
of weight magnitudes; binary arithmetic refinement is handled by operand-size
bounds, not by pretending that weights are unary.
-/
namespace IndependentSetDiscovery.WeightedShortestPaths

open WeightedDirected
variable {n : ℕ}

/-- Visited vertices are stored in reverse order; the original source is omitted.
The cached score avoids traversing the route at every comparison. -/
structure Route (n : ℕ) where
  vertices : List (Fin n)
  score : ℕ
  deriving DecidableEq, Repr

def Route.empty : Route n := ⟨[], 0⟩
def Route.extend (w : Fin n → Fin n → ℕ) (u v : Fin n) (p : Route n) : Route n :=
  ⟨v :: p.vertices, p.score + w u v⟩

/-- Soundness of the actual stored route and its cached score. -/
inductive Valid (D : Fin n → Fin n → Prop) (w : Fin n → Fin n → ℕ) (s : Fin n) :
    Fin n → Route n → Prop
  | nil : Valid D w s s .empty
  | extend {u v p} : Valid D w s u p → D u v → Valid D w s v (p.extend w u v)

theorem walk_length_append {D : Fin n → Fin n → Prop} {a b c : Fin n}
    (p : DWalk D a b) (q : DWalk D b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [DWalk.append]
  | cons h p ih => simp [DWalk.append, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Valid.exists_walk {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {s v : Fin n} {p : Route n} (h : Valid D w s v p) :
    ∃ q : DWalk D s v, q.cost w = p.score ∧ q.length = p.vertices.length := by
  induction h with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | @extend u v p hp he ih =>
    obtain ⟨q, hq, hl⟩ := ih
    refine ⟨q.append (.cons he .nil), ?_, ?_⟩
    · simp [Route.extend, hq]
    · simp [Route.extend, walk_length_append, hl]

theorem Valid.prepend {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {a s v : Fin n} {p : Route n} (he : D a s) (h : Valid D w s v p) :
    ∃ q, Valid D w a v q ∧ q.score = w a s + p.score ∧
      q.vertices.length = p.vertices.length + 1 := by
  induction h with
  | nil =>
    exact ⟨Route.empty.extend w a s, Valid.extend Valid.nil he, by simp [Route.extend, Route.empty], rfl⟩
  | @extend u v p hp huv ih =>
    obtain ⟨q, hq, hs, hl⟩ := ih
    refine ⟨q.extend w u v, Valid.extend hq huv, ?_, ?_⟩
    · simp [Route.extend, hs, Nat.add_assoc]
    · simp [Route.extend, hl]

theorem exists_route_of_walk {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {s v : Fin n} (p : DWalk D s v) :
    ∃ q, Valid D w s v q ∧ q.score = p.cost w ∧ q.vertices.length = p.length := by
  induction p with
  | nil => exact ⟨.empty, Valid.nil, rfl, rfl⟩
  | cons he p ih =>
    obtain ⟨q, hq, hs, hl⟩ := ih
    obtain ⟨r, hr, hrs, hrl⟩ := hq.prepend he
    exact ⟨r, hr, by simpa [hs] using hrs, by simpa [hl] using hrl⟩

/-- Stable minimum by accumulated weight. -/
def pick (a b : Option (Route n)) : Option (Route n) :=
  match a, b with
  | none, b => b
  | a, none => a
  | some p, some q => if p.score ≤ q.score then some p else some q

def Dominates (a b : Option (Route n)) : Prop :=
  ∀ q, b = some q → ∃ p, a = some p ∧ p.score ≤ q.score

theorem dominates_refl (a : Option (Route n)) : Dominates a a := by
  intro q hq
  exact ⟨q, hq, le_rfl⟩

theorem Dominates.trans {a b c : Option (Route n)}
    (hab : Dominates a b) (hbc : Dominates b c) : Dominates a c := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := hbc q hq
  obtain ⟨r, hr, hrp⟩ := hab p hp
  exact ⟨r, hr, hrp.trans hpq⟩

theorem pick_eq (a b : Option (Route n)) : pick a b = a ∨ pick a b = b := by
  cases a with
  | none => cases b <;> exact Or.inr rfl
  | some p =>
    cases b with
    | none => exact Or.inl rfl
    | some q => by_cases h : p.score ≤ q.score <;> simp [pick, h]

theorem pick_left (a b : Option (Route n)) : Dominates (pick a b) a := by
  intro p hp
  subst a
  cases b with
  | none => exact ⟨p, rfl, le_rfl⟩
  | some q =>
    dsimp only [pick]
    split_ifs with h
    · exact ⟨p, rfl, le_rfl⟩
    · exact ⟨q, rfl, by omega⟩

theorem pick_right (a b : Option (Route n)) : Dominates (pick a b) b := by
  intro q hq
  subst b
  cases a with
  | none => exact ⟨q, rfl, le_rfl⟩
  | some p =>
    dsimp only [pick]
    split_ifs with h
    · exact ⟨p, rfl, h⟩
    · exact ⟨q, rfl, le_rfl⟩

/-- One materialized scan, with fixed primitive-operation charge per candidate. -/
def bestAmong (candidate : Fin n → Option (Route n)) :
    List (Fin n) → Option (Route n) → Option (Route n) × ℕ
  | [], base => (base, 1)
  | u :: us, base =>
    let tail := bestAmong candidate us base
    (pick (candidate u) tail.1, tail.2 + 24)

theorem bestAmong_base (candidate : Fin n → Option (Route n))
    (xs : List (Fin n)) (base : Option (Route n)) :
    Dominates (bestAmong candidate xs base).1 base := by
  induction xs with
  | nil => exact dominates_refl _
  | cons u us ih => exact (pick_right _ _).trans ih

theorem bestAmong_candidate (candidate : Fin n → Option (Route n))
    (xs : List (Fin n)) (base : Option (Route n)) {u : Fin n} (hu : u ∈ xs) :
    Dominates (bestAmong candidate xs base).1 (candidate u) := by
  induction xs with
  | nil => simp at hu
  | cons v vs ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · exact pick_left _ _
    · exact (pick_right _ _).trans (ih hu)

theorem bestAmong_property (candidate : Fin n → Option (Route n))
    (xs : List (Fin n)) (base : Option (Route n)) (P : Route n → Prop)
    (hb : ∀ p, base = some p → P p)
    (hc : ∀ u ∈ xs, ∀ p, candidate u = some p → P p) :
    ∀ p, (bestAmong candidate xs base).1 = some p → P p := by
  induction xs with
  | nil => exact hb
  | cons u us ih =>
    intro p hp
    rcases pick_eq (candidate u) (bestAmong candidate us base).1 with h | h
    · exact hc u (by simp) p (h.symm.trans hp)
    · exact ih (fun v hv => hc v (by simp [hv])) p (h.symm.trans hp)

theorem bestAmong_cost (candidate : Fin n → Option (Route n))
    (xs : List (Fin n)) (base : Option (Route n)) :
    (bestAmong candidate xs base).2 = 1 + 24 * xs.length := by
  induction xs with
  | nil => simp [bestAmong]
  | cons u us ih => simp [bestAmong, ih, Nat.mul_add]; omega

variable (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℕ)

abbrev Table (n : ℕ) := Vector (Option (Route n)) n

def candidate (old : Table n) (v u : Fin n) : Option (Route n) :=
  if D u v then old[u].map (fun p => p.extend w u v) else none

def relax (old : Table n) (v : Fin n) : Option (Route n) × ℕ :=
  bestAmong (candidate D w old v) (List.finRange n) old[v]

def round (old : Table n) : Table n × ℕ :=
  let entries := Vector.ofFn (relax D w old)
  (entries.map Prod.fst, 4 * n + (entries.toList.map Prod.snd).sum)

def table (s : Fin n) : ℕ → Table n × ℕ
  | 0 => (Vector.ofFn (fun v => if s = v then some Route.empty else none), 3 * n)
  | fuel + 1 =>
    let old := table s fuel
    let next := round D w old.1
    (next.1, old.2 + next.2)

@[simp] theorem round_get (old : Table n) (v : Fin n) :
    (round D w old).1[v] = (relax D w old v).1 := by simp [round]

@[simp] theorem table_succ_get (s : Fin n) (fuel : ℕ) (v : Fin n) :
    (table D w s (fuel + 1)).1[v] = (relax D w (table D w s fuel).1 v).1 := by
  simp [table, round]

theorem relax_sound {s : Fin n} (old : Table n) (fuel : ℕ)
    (h : ∀ v p, old[v] = some p → Valid D w s v p ∧ p.vertices.length ≤ fuel) :
    ∀ v p, (relax D w old v).1 = some p → Valid D w s v p ∧ p.vertices.length ≤ fuel + 1 := by
  intro v
  apply bestAmong_property
  · intro p hp
    exact ⟨(h v p hp).1, (h v p hp).2.trans (Nat.le_succ _)⟩
  · intro u hu p hp
    unfold candidate at hp
    split_ifs at hp with hadj
    · cases ho : old[u] with
      | none => simp [ho] at hp
      | some q =>
        simp only [ho, Option.map_some, Option.some.injEq] at hp
        subst p
        exact ⟨Valid.extend (h u q ho).1 hadj,
          by simpa [Route.extend] using Nat.succ_le_succ (h u q ho).2⟩

theorem table_sound (s : Fin n) (fuel : ℕ) :
    ∀ v p, (table D w s fuel).1[v] = some p → Valid D w s v p ∧ p.vertices.length ≤ fuel := by
  induction fuel with
  | zero =>
    intro v p hp
    simp only [table, Fin.getElem_fin, Vector.getElem_ofFn] at hp
    split_ifs at hp with h
    · change s = v at h
      subst v
      cases hp
      exact ⟨Valid.nil, le_rfl⟩
  | succ fuel ih =>
    intro v p hp
    rw [table_succ_get] at hp
    exact relax_sound D w _ fuel ih v p hp

/-- Every bounded-hop route is dominated by the computed entry, by weight. -/
theorem table_complete (s : Fin n) (fuel : ℕ) :
    ∀ v p, Valid D w s v p → p.vertices.length ≤ fuel →
      ∃ q, (table D w s fuel).1[v] = some q ∧ q.score ≤ p.score := by
  induction fuel with
  | zero =>
    intro v p hp hlen
    cases hp with
    | nil => exact ⟨.empty, by simp [table], le_rfl⟩
    | extend _ _ => simp [Route.extend] at hlen
  | succ fuel ih =>
    intro v p hp hlen
    cases hp with
    | nil =>
      obtain ⟨q, hq, hscore⟩ := ih s .empty Valid.nil (Nat.zero_le _)
      obtain ⟨r, hr, hrl⟩ := bestAmong_base
        (candidate D w (table D w s fuel).1 s) (List.finRange n) (table D w s fuel).1[s] q hq
      exact ⟨r, by simpa [table, round, relax] using hr, hrl.trans hscore⟩
    | @extend u v p hp hadj =>
      obtain ⟨q, hq, hqp⟩ := ih u p hp (by simpa [Route.extend] using hlen)
      have hc : candidate D w (table D w s fuel).1 v u = some (q.extend w u v) := by
        simp [candidate, hadj, hq]
      obtain ⟨r, hr, hrl⟩ := bestAmong_candidate
        (candidate D w (table D w s fuel).1 v) (List.finRange n)
        (table D w s fuel).1[v] (List.mem_finRange u) (q.extend w u v) hc
      exact ⟨r, by simpa [table, round, relax] using hr,
        hrl.trans (Nat.add_le_add_right hqp _)⟩

/-- Exact weight minimization among all walks fitting the round budget. -/
theorem table_optimal (s : Fin n) (fuel : ℕ) {v : Fin n} {p : Route n}
    (hp : (table D w s fuel).1[v] = some p) (q : DWalk D s v)
    (hq : q.length ≤ fuel) : p.score ≤ q.cost w := by
  obtain ⟨r, hr, hscore, hlen⟩ := exists_route_of_walk (w := w) q
  obtain ⟨p', hp', hle⟩ := table_complete D w s fuel v r hr (hlen ▸ hq)
  have : p = p' := Option.some.inj (hp.symm.trans hp')
  subst p'
  exact hle.trans hscore.le

/-- Cycle removal permits exactly `n-1` rounds, including zero-weight arcs. -/
def shortestPaths (s : Fin n) : Table n × ℕ := table D w s (n - 1)

theorem relax_cost (old : Table n) (v : Fin n) :
    (relax D w old v).2 = 1 + 24 * n := by
  simp [relax, bestAmong_cost]

theorem round_cost (old : Table n) : (round D w old).2 = 5 * n + 24 * n ^ 2 := by
  simp only [round, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    relax_cost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  <;> ring

theorem table_cost (s : Fin n) (fuel : ℕ) :
    (table D w s fuel).2 = 3 * n + fuel * (5 * n + 24 * n ^ 2) := by
  induction fuel with
  | zero => simp [table]
  | succ fuel ih => simp [table, round_cost, ih]; ring

/-- The executable preprocessing has a cubic primitive-operation bound. -/
theorem shortestPaths_cost_exact (s : Fin n) :
    (shortestPaths D w s).2 = 3 * n + (n - 1) * (5 * n + 24 * n ^ 2) := by
  rw [shortestPaths, table_cost]

theorem shortestPaths_cost (s : Fin n) :
    (shortestPaths D w s).2 ≤ 3 * n + 5 * n ^ 2 + 24 * n ^ 3 := by
  rw [shortestPaths_cost_exact]
  have h := Nat.mul_le_mul_right (5 * n + 24 * n ^ 2) (Nat.sub_le n 1)
  nlinarith only [h]

/-- Both the actual route and the tight simple-path length bound. -/
theorem shortestPaths_sound (s v : Fin n) {p : Route n}
    (hp : (shortestPaths D w s).1[v] = some p) :
    Valid D w s v p ∧ p.vertices.length ≤ n - 1 :=
  table_sound D w s (n - 1) v p hp

/-- Every available directed path is represented by a computed finite entry. -/
theorem shortestPaths_exists_iff (s v : Fin n) :
    (∃ p, (shortestPaths D w s).1[v] = some p) ↔ Nonempty (DWalk D s v) := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨q, _, _⟩ := (table_sound D w s (n - 1) v p hp).1.exists_walk
    exact ⟨q⟩
  · rintro ⟨p⟩
    obtain ⟨q, hq, hlen⟩ := p.exists_bounded_le_cost w
    simp only [Fintype.card_fin] at hlen
    obtain ⟨r, hr, hs, hl⟩ := exists_route_of_walk (w := w) q
    obtain ⟨p', hp', _⟩ := table_complete D w s (n - 1) v r hr (by simpa [hl] using hlen)
    exact ⟨p', hp'⟩

/-- The output minimizes weight over every directed walk, without a hop bound. -/
theorem shortestPaths_optimal (s v : Fin n) {p : Route n}
    (hp : (shortestPaths D w s).1[v] = some p) (q : DWalk D s v) :
    p.score ≤ q.cost w := by
  obtain ⟨r, hcost, hlen⟩ := q.exists_bounded_le_cost w
  simp only [Fintype.card_fin] at hlen
  exact (table_optimal D w s (n - 1) hp r hlen).trans hcost

/-- Exact agreement with the directed weighted distance specification. -/
theorem shortestPaths_score_eq_distance (s v : Fin n) {p : Route n}
    (hp : (shortestPaths D w s).1[v] = some p) :
    (p.score : ℕ∞) = WeightedDirected.distance D w s v := by
  apply le_antisymm
  · apply le_iInf
    intro q
    exact_mod_cast shortestPaths_optimal D w s v hp q
  · obtain ⟨q, hscore, _⟩ := (table_sound D w s (n - 1) v p hp).1.exists_walk
    have h := q.distance_le (w := w)
    simpa [hscore] using h

theorem shortestPaths_none_iff (s v : Fin n) :
    (shortestPaths D w s).1[v] = none ↔ ¬ Nonempty (DWalk D s v) := by
  rw [← shortestPaths_exists_iff D w s v]
  cases h : (shortestPaths D w s).1[v] <;> simp

/-- The cached scores have polynomial binary length whenever arc weights do. -/
theorem valid_score_le {s v : Fin n} {p : Route n} (hp : Valid D w s v p)
    {W : ℕ} (hW : ∀ u v, D u v → w u v ≤ W) : p.score ≤ p.vertices.length * W := by
  induction hp with
  | nil => simp [Route.empty]
  | @extend u v p hp he ih =>
    simp only [Route.extend, List.length_cons, Nat.add_mul]
    have h := hW u v he
    omega

theorem shortestPaths_score_le (s v : Fin n) {p : Route n}
    (hp : (shortestPaths D w s).1[v] = some p) {W : ℕ}
    (hW : ∀ u v, D u v → w u v ≤ W) : p.score ≤ n * W := by
  have hs := table_sound D w s (n - 1) v p hp
  exact (valid_score_le D w hs.1 hW).trans (Nat.mul_le_mul_right W (hs.2.trans (Nat.sub_le n 1)))

end IndependentSetDiscovery.WeightedShortestPaths
