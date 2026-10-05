import IndependentSetDiscovery.Algorithms.WeightedShortestPaths

/-!
# Executable decoding of weighted directed shortest-route witnesses

This decoder consumes the actual stored vertex list. No path is obtained by
`Classical.choose` or by extracting computational data from a proposition.
-/
namespace IndependentSetDiscovery.WeightedShortestPaths

open WeightedDirected
variable {n : ℕ} (D : Fin n → Fin n → Prop) [DecidableRel D]
variable (w : Fin n → Fin n → ℕ)

def castTarget {s u v : Fin n} (p : DWalk D s u) (h : u = v) : DWalk D s v := h ▸ p

@[simp] theorem cost_castTarget {s u v : Fin n} (p : DWalk D s u) (h : u = v) :
    (castTarget D p h).cost w = p.cost w := by subst v; rfl

@[simp] theorem length_castTarget {s u v : Fin n} (p : DWalk D s u) (h : u = v) :
    (castTarget D p h).length = p.length := by subst v; rfl

theorem Valid.headD {s v : Fin n} {p : Route n} (h : Valid D w s v p) :
    p.vertices.headD s = v := by cases h <;> rfl

/-- Decode a reverse vertex list to a typed directed walk; charge append visits. -/
def decode (s : Fin n) : (xs : List (Fin n)) → Option (DWalk D s (xs.headD s)) × ℕ
  | [] => (some .nil, 1)
  | v :: xs =>
    let prior := decode s xs
    if h : D (xs.headD s) v then
      (prior.1.map (fun p => p.append (.cons h .nil)), prior.2 + xs.length + 8)
    else (none, prior.2 + xs.length + 8)

def decodeTo (s v : Fin n) (p : Route n) : Option (DWalk D s v) × ℕ :=
  let d := decode D s p.vertices
  if h : p.vertices.headD s = v then
    (d.1.map (fun q => castTarget D q h), d.2 + 2)
  else (none, d.2 + 2)

theorem decode_valid {s v : Fin n} {p : Route n} (h : Valid D w s v p) :
    ∃ q, (decode D s p.vertices).1 = some q ∧
      q.cost w = p.score ∧ q.length = p.vertices.length := by
  induction h with
  | nil => exact ⟨.nil, rfl, rfl, rfl⟩
  | @extend u v p hp hadj ih =>
    obtain ⟨q, hq, hscore, hlen⟩ := ih
    have ha : D (p.vertices.headD s) v := by rw [hp.headD]; exact hadj
    refine ⟨q.append (.cons ha .nil), ?_, ?_, ?_⟩
    · dsimp only [Route.extend, decode]
      rw [dif_pos ha, hq]
      rfl
    · simp only [DWalk.cost_append, DWalk.cost_cons, DWalk.cost_nil, Nat.add_zero,
        Route.extend, hscore]
      rw [hp.headD]
    · simp [Route.extend, walk_length_append, hlen]

theorem decodeTo_valid {s v : Fin n} {p : Route n} (h : Valid D w s v p) :
    ∃ q, (decodeTo D s v p).1 = some q ∧
      q.cost w = p.score ∧ q.length = p.vertices.length := by
  obtain ⟨q, hq, hs, hl⟩ := decode_valid D w h
  refine ⟨castTarget D q h.headD, ?_, by simpa using hs, by simpa using hl⟩
  unfold decodeTo
  rw [dif_pos h.headD, hq]
  rfl

theorem decodeTo_score {s v : Fin n} {p : Route n} (h : Valid D w s v p)
    (q : DWalk D s v) (hq : (decodeTo D s v p).1 = some q) : q.cost w = p.score := by
  obtain ⟨r, hr, hs, _⟩ := decodeTo_valid D w h
  have : r = q := Option.some.inj (hr.symm.trans hq)
  simpa [this] using hs

theorem decode_cost (s : Fin n) (xs : List (Fin n)) :
    (decode D s xs).2 ≤ 1 + 8 * xs.length + xs.length ^ 2 := by
  induction xs with
  | nil => simp [decode]
  | cons v xs ih =>
    dsimp only [decode]
    split_ifs <;> simp only [List.length_cons] <;> nlinarith

theorem decodeTo_cost (s v : Fin n) (p : Route n) :
    (decodeTo D s v p).2 ≤ 3 + 8 * p.vertices.length + p.vertices.length ^ 2 := by
  have h := decode_cost D s p.vertices
  unfold decodeTo
  split_ifs <;> dsimp <;> omega

/-- Return an actual optional minimum-weight directed walk. -/
def walkOption (s v : Fin n) : Option (DWalk D s v) × ℕ :=
  let row := shortestPaths D w s
  match row.1[v] with
  | none => (none, row.2 + 1)
  | some p =>
    let decoded := decodeTo D s v p
    (decoded.1, row.2 + decoded.2 + 1)

theorem walkOption_exists_iff (s v : Fin n) :
    (∃ p, (walkOption D w s v).1 = some p) ↔ Nonempty (DWalk D s v) := by
  constructor
  · rintro ⟨p, _⟩; exact ⟨p⟩
  · intro h
    obtain ⟨p, hp⟩ := (shortestPaths_exists_iff D w s v).mpr h
    obtain ⟨q, hq, _, _⟩ := decodeTo_valid D w (table_sound D w s (n - 1) v p hp).1
    exact ⟨q, by simp [walkOption, hp, hq]⟩

theorem walkOption_distance (s v : Fin n) (q : DWalk D s v)
    (hq : (walkOption D w s v).1 = some q) :
    (q.cost w : ℕ∞) = WeightedDirected.distance D w s v := by
  unfold walkOption at hq
  cases hp : (shortestPaths D w s).1[v] with
  | none => simp [hp] at hq
  | some p =>
    simp only [hp] at hq
    rw [decodeTo_score D w (table_sound D w s (n - 1) v p hp).1 q hq]
    exact shortestPaths_score_eq_distance D w s v hp

/-- Construct a minimum-weight typed walk from a reachability proof; the proof
only rules out `none`, while the walk itself is obtained by computation. -/
def walkOfReachable (s v : Fin n) (h : Nonempty (DWalk D s v)) :
    {q : DWalk D s v // (q.cost w : ℕ∞) = WeightedDirected.distance D w s v} :=
  let hp : (walkOption D w s v).1.isSome := by
    obtain ⟨q, hq⟩ := (walkOption_exists_iff D w s v).mpr h
    simp [hq]
  let q := (walkOption D w s v).1.get hp
  ⟨q, walkOption_distance D w s v q (Option.some_get hp).symm⟩

def walkOfFiniteDistance (s v : Fin n) (h : WeightedDirected.distance D w s v ≠ ⊤) :
    {q : DWalk D s v // (q.cost w : ℕ∞) = WeightedDirected.distance D w s v} :=
  walkOfReachable D w s v (ENat.iInf_coe_ne_top.mp h)

theorem walkOption_cost (s v : Fin n) :
    (walkOption D w s v).2 ≤ 24 * n ^ 3 + 6 * n ^ 2 + 11 * n + 4 := by
  have hb := shortestPaths_cost D w s
  unfold walkOption
  cases hp : (shortestPaths D w s).1[v] with
  | none => simp only [hp]; nlinarith
  | some p =>
    have hd := decodeTo_cost D s v p
    have hlen := (table_sound D w s (n - 1) v p hp).2.trans (Nat.sub_le n 1)
    have hsq : p.vertices.length ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hlen 2
    simp only [hp]
    nlinarith

end IndependentSetDiscovery.WeightedShortestPaths
