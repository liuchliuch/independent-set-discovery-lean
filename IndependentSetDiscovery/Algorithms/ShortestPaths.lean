import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Executable polynomial shortest paths with route witnesses

The table is stored in a `Vector`, hence its previous round is materialized
once and reused. In particular this is not the exponentially recomputed
recurrence obtained by representing each previous row as an unevaluated
recursive function. Routes list the visited vertices in reverse order, omit
the original source, and therefore support constant-time extension by `cons`.

The cost model counts adjacency probes, array accesses, list construction,
and list-length traversal used by comparisons. An adjacency matrix supplies
the graph probes directly; no shortest-path oracle is assumed.
-/

namespace IndependentSetDiscovery.ShortestPaths

variable {n : ℕ}

/-- Explicit finite graph input, represented by a Boolean adjacency matrix. -/
structure MatrixGraph (n : ℕ) where
  matrix : Vector (Vector Bool n) n
  symmetric : ∀ u v : Fin n, matrix[u][v] = matrix[v][u]
  diagonal : ∀ u : Fin n, matrix[u][u] = false

def MatrixGraph.graph (a : MatrixGraph n) : SimpleGraph (Fin n) where
  Adj u v := a.matrix[u][v] = true
  symm := fun {u v} h => (a.symmetric v u).trans h
  loopless := fun u h => Bool.false_ne_true ((a.diagonal u).symm.trans h)

instance (a : MatrixGraph n) : DecidableRel a.graph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

abbrev Route (n : ℕ) := List (Fin n)

/-- Route entries are actual consecutive vertices, stored from end to start. -/
inductive Valid (G : SimpleGraph (Fin n)) (s : Fin n) : Fin n → Route n → Prop
  | nil : Valid G s s []
  | extend {u v p} : Valid G s u p → G.Adj u v → Valid G s v (v :: p)

theorem Valid.exists_walk {G : SimpleGraph (Fin n)} {s v : Fin n} {p : Route n}
    (h : Valid G s v p) : ∃ w : G.Walk s v, w.length = p.length := by
  induction h with
  | nil => exact ⟨.nil, rfl⟩
  | extend hp he ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w.concat he, by simp [hw]⟩

theorem exists_route_of_walk {G : SimpleGraph (Fin n)} {s v : Fin n}
    (w : G.Walk s v) : ∃ p, Valid G s v p ∧ p.length = w.length := by
  induction w using SimpleGraph.Walk.concatRec with
  | Hnil => exact ⟨[], Valid.nil, rfl⟩
  | @Hconcat u v w p h ih =>
    obtain ⟨q, hq, hlen⟩ := ih
    exact ⟨w :: q, Valid.extend hq h, by simp [hlen]⟩

/-- `none` means no route; between routes choose the shorter, with stable ties. -/
def pick (a b : Option (Route n)) : Option (Route n) :=
  match a, b with
  | none, b => b
  | a, none => a
  | some p, some q => if p.length ≤ q.length then some p else some q

def Dominates (a b : Option (Route n)) : Prop :=
  ∀ q, b = some q → ∃ p, a = some p ∧ p.length ≤ q.length

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
    | some q =>
      by_cases h : p.length ≤ q.length <;> simp [pick, h]

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

def routeSize (p : Option (Route n)) : ℕ :=
  match p with | none => 0 | some p => p.length

/-- Enumerate actual candidates and charge each comparison and list traversal. -/
def bestAmong (candidate : Fin n → Option (Route n)) :
    List (Fin n) → Option (Route n) → Option (Route n) × ℕ
  | [], base => (base, 1)
  | u :: us, base =>
      let tail := bestAmong candidate us base
      let c := candidate u
      (pick c tail.1, tail.2 + 16 + routeSize c + routeSize tail.1)

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
    · exact ih (fun u hu => hc u (by simp [hu])) p (h.symm.trans hp)

theorem bestAmong_cost (candidate : Fin n → Option (Route n))
    (xs : List (Fin n)) (base : Option (Route n)) (bound : ℕ)
    (hb : routeSize base ≤ bound) (hc : ∀ u ∈ xs, routeSize (candidate u) ≤ bound) :
    (bestAmong candidate xs base).2 ≤ 1 + xs.length * (16 + 2 * bound) := by
  induction xs with
  | nil => simp [bestAmong]
  | cons u us ih =>
    have ht := ih (fun v hv => hc v (by simp [hv]))
    have hbest : routeSize (bestAmong candidate us base).1 ≤ bound := by
      cases h : (bestAmong candidate us base).1 with
      | none => simp [routeSize]
      | some p =>
        exact bestAmong_property candidate us base (fun p => p.length ≤ bound)
          (by intro p hp; simpa [hp, routeSize] using hb)
          (by intro v hv p hp; simpa [hp, routeSize] using hc v (by simp [hv])) p h
    have hu := hc u (by simp)
    simp only [bestAmong, List.length_cons]
    nlinarith

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

abbrev Table (n : ℕ) := Vector (Option (Route n)) n

def candidate (old : Table n) (v u : Fin n) : Option (Route n) :=
  if G.Adj u v then old[u].map (fun p => v :: p) else none

def relax (old : Table n) (v : Fin n) : Option (Route n) × ℕ :=
  bestAmong (candidate G old v) (List.finRange n) old[v]

/-- Materialize every row of one Bellman--Ford relaxation round. -/
def round (old : Table n) : Table n × ℕ :=
  let entries := Vector.ofFn (relax G old)
  (entries.map Prod.fst, 4 * n + (entries.toList.map Prod.snd).sum)

/-- Source row after `fuel` rounds, together with its accumulated operation count. -/
def table (s : Fin n) : ℕ → Table n × ℕ
  | 0 => (Vector.ofFn (fun v => if s = v then some [] else none), 3 * n)
  | fuel + 1 =>
      let old := table s fuel
      let next := round G old.1
      (next.1, old.2 + next.2)

@[simp] theorem round_get (old : Table n) (v : Fin n) :
    (round G old).1[v] = (relax G old v).1 := by simp [round]

@[simp] theorem table_succ_get (s : Fin n) (fuel : ℕ) (v : Fin n) :
    (table G s (fuel + 1)).1[v] = (relax G (table G s fuel).1 v).1 := by
  simp [table, round]

theorem relax_sound {s : Fin n} (old : Table n) (fuel : ℕ)
    (h : ∀ v p, old[v] = some p → Valid G s v p ∧ p.length ≤ fuel) :
    ∀ v p, (relax G old v).1 = some p → Valid G s v p ∧ p.length ≤ fuel + 1 := by
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
        exact ⟨Valid.extend (h u q ho).1 hadj, by simpa using Nat.succ_le_succ (h u q ho).2⟩

theorem table_sound (s : Fin n) (fuel : ℕ) :
    ∀ v p, (table G s fuel).1[v] = some p → Valid G s v p ∧ p.length ≤ fuel := by
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
    exact relax_sound G _ fuel ih v p hp

theorem table_complete (s : Fin n) (fuel : ℕ) :
    ∀ v p, Valid G s v p → p.length ≤ fuel →
      ∃ q, (table G s fuel).1[v] = some q ∧ q.length ≤ p.length := by
  induction fuel with
  | zero =>
    intro v p hp hlen
    cases hp with
    | nil => exact ⟨[], by simp [table], le_rfl⟩
    | extend _ _ => simp at hlen
  | succ fuel ih =>
    intro v p hp hlen
    cases hp with
    | nil =>
      obtain ⟨q, hq, hlen⟩ := ih s [] Valid.nil (Nat.zero_le _)
      obtain ⟨r, hr, hrl⟩ := bestAmong_base
        (candidate G (table G s fuel).1 s) (List.finRange n) (table G s fuel).1[s] q hq
      exact ⟨r, by simpa [table, round, relax] using hr, hrl.trans hlen⟩
    | @extend u v p hp hadj =>
      obtain ⟨q, hq, hqp⟩ := ih u p hp (by simpa using hlen)
      have hc : candidate G (table G s fuel).1 v u = some (v :: q) := by
        simp [candidate, hadj, hq]
      obtain ⟨r, hr, hrl⟩ := bestAmong_candidate
        (candidate G (table G s fuel).1 v) (List.finRange n)
        (table G s fuel).1[v] (List.mem_finRange u) (v :: q) hc
      exact ⟨r, by simpa [table, round, relax] using hr,
        by simpa using hrl.trans (Nat.succ_le_succ hqp)⟩

/-- An output route minimizes length among every route fitting the round budget. -/
theorem table_optimal (s : Fin n) (fuel : ℕ) {v : Fin n} {p : Route n}
    (hp : (table G s fuel).1[v] = some p) (w : G.Walk s v)
    (hw : w.length ≤ fuel) : p.length ≤ w.length := by
  obtain ⟨q, hq, hlen⟩ := exists_route_of_walk w
  obtain ⟨r, hr, hrl⟩ := table_complete G s fuel v q hq (hlen ▸ hw)
  have : p = r := Option.some.inj (hp.symm.trans hr)
  subst r
  exact hrl.trans hlen.le

/-- The executable preprocessing used for finite graphs. -/
def shortestPaths (s : Fin n) : Table n × ℕ := table G s n

theorem relax_cost (old : Table n) (fuel : ℕ)
    (h : ∀ (v : Fin n) (p : Route n), old[v] = some p → p.length ≤ fuel) (v : Fin n) :
    (relax G old v).2 ≤ 1 + n * (18 + 2 * fuel) := by
  have hb : routeSize old[v] ≤ fuel + 1 := by
    cases ho : old[v] with
    | none => simp [routeSize]
    | some p => simpa [routeSize] using (h v p ho).trans (Nat.le_succ fuel)
  have hc : ∀ u ∈ List.finRange n, routeSize (candidate G old v u) ≤ fuel + 1 := by
    intro u hu
    unfold candidate
    split_ifs with hadj
    · cases ho : old[u] with
      | none => simp [routeSize]
      | some p => simpa [routeSize] using Nat.succ_le_succ (h u p ho)
    · simp [routeSize]
  have hc := bestAmong_cost (candidate G old v) (List.finRange n) old[v] (fuel + 1) hb hc
  simp only [List.length_finRange] at hc
  change (bestAmong (candidate G old v) (List.finRange n) old[v]).2 ≤ _
  nlinarith

theorem round_cost (old : Table n) (fuel : ℕ)
    (h : ∀ (v : Fin n) (p : Route n), old[v] = some p → p.length ≤ fuel) :
    (round G old).2 ≤ 5 * n + n ^ 2 * (18 + 2 * fuel) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => relax_cost G old fuel h v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [round, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  nlinarith

/-- A direct polynomial bound for the counter attached to the executed DP. -/
theorem table_cost (s : Fin n) (fuel : ℕ) :
    (table G s fuel).2 ≤ 3 * n + fuel * (5 * n + n ^ 2 * (18 + 2 * fuel)) := by
  induction fuel with
  | zero => simp [table]
  | succ fuel ih =>
    have hround := round_cost G (table G s fuel).1 fuel
      (fun v p hp => (table_sound G s fuel v p hp).2)
    simp only [table]
    nlinarith

/-- Preprocessing is polynomial and produces every actual shortest-route witness. -/
theorem shortestPaths_cost (s : Fin n) :
    (shortestPaths G s).2 ≤ 3 * n + 5 * n ^ 2 + 18 * n ^ 3 + 2 * n ^ 4 := by
  have h := table_cost G s n
  dsimp [shortestPaths]
  nlinarith

theorem shortestPaths_exists_iff (s v : Fin n) :
    (∃ p, (shortestPaths G s).1[v] = some p) ↔ G.Reachable s v := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨w, _⟩ := (table_sound G s n v p hp).1.exists_walk
    exact ⟨w⟩
  · intro hr
    obtain ⟨w, hw, hdist⟩ := hr.exists_path_of_dist
    obtain ⟨p, hp, hlen⟩ := exists_route_of_walk w
    have hbound : w.length ≤ n := by
      have := hw.length_lt
      simpa using this.le
    obtain ⟨q, hq, _⟩ := table_complete G s n v p hp (hlen ▸ hbound)
    exact ⟨q, hq⟩

/-- Exact graph-distance agreement connects executable preprocessing to the
paper's metric specification. -/
theorem shortestPaths_length_eq_dist (s v : Fin n) {p : Route n}
    (hp : (shortestPaths G s).1[v] = some p) : p.length = G.dist s v := by
  obtain ⟨w, hw⟩ := (table_sound G s n v p hp).1.exists_walk
  have hr : G.Reachable s v := ⟨w⟩
  obtain ⟨q, hq, hdist⟩ := hr.exists_path_of_dist
  have hbound : q.length ≤ n := by simpa using hq.length_lt.le
  apply le_antisymm
  · exact (table_optimal G s n hp q hbound).trans hdist.le
  · exact hw ▸ SimpleGraph.dist_le w

theorem shortestPaths_none_iff (s v : Fin n) :
    (shortestPaths G s).1[v] = none ↔ ¬ G.Reachable s v := by
  rw [← shortestPaths_exists_iff G s v]
  cases h : (shortestPaths G s).1[v] <;> simp

end IndependentSetDiscovery.ShortestPaths
