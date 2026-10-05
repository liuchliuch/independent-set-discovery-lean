import IndependentSetDiscovery.Algorithms.ShortestPaths

/-! Executable decoding of Bellman--Ford's route lists into typed graph walks.
The implementation does not extract data from existential proofs or use
`Classical.choice`: every returned walk is computed from the route vertices.
The attached counter charges the list traversal performed by `Walk.concat`. -/

namespace IndependentSetDiscovery.ShortestPaths

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem Valid.headD {s v : Fin n} {p : Route n} (h : Valid G s v p) :
    p.headD s = v := by cases h <;> rfl

/-- Decode a reversed route into its actual typed walk, counting list visits. -/
def decode (s : Fin n) : (p : Route n) → Option (G.Walk s (p.headD s)) × ℕ
  | [] => (some .nil, 1)
  | v :: p =>
    let prior := decode s p
    if h : G.Adj (p.headD s) v then
      (prior.1.map (fun w => w.concat h), prior.2 + p.length + 8)
    else (none, prior.2 + p.length + 8)

def decodeTo (s v : Fin n) (p : Route n) : Option (G.Walk s v) × ℕ :=
  let d := decode G s p
  if h : p.headD s = v then (d.1.map (fun w => w.copy rfl h), d.2 + 2)
  else (none, d.2 + 2)

theorem decode_length (s : Fin n) (p : Route n) :
    ∀ w, (decode G s p).1 = some w → w.length = p.length := by
  induction p with
  | nil => intro w hw; simp [decode] at hw; subst w; rfl
  | cons v p ih =>
    intro w hw
    dsimp only [decode] at hw
    split_ifs at hw with ha
    · cases hd : (decode G s p).1 with
      | none => simp [hd] at hw
      | some q =>
        simp only [hd, Option.map_some, Option.some.injEq] at hw
        subst w
        simpa using congrArg Nat.succ (ih q hd)

theorem decode_valid {s v : Fin n} {p : Route n} (h : Valid G s v p) :
    ∃ w, (decode G s p).1 = some w ∧ w.length = p.length := by
  induction h with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | @extend u v p hp hadj ih =>
    obtain ⟨w, hw, hlen⟩ := ih
    have ha : G.Adj (p.headD s) v := by rw [hp.headD]; exact hadj
    refine ⟨w.concat ha, ?_, by simp [hlen]⟩
    dsimp only [decode]
    rw [dif_pos ha, hw]
    rfl

theorem decodeTo_length (s v : Fin n) (p : Route n) (w : G.Walk s v)
    (hw : (decodeTo G s v p).1 = some w) : w.length = p.length := by
  unfold decodeTo at hw
  split_ifs at hw with hv
  · cases hd : (decode G s p).1 with
    | none => simp [hd] at hw
    | some q =>
      simp only [hd, Option.map_some, Option.some.injEq] at hw
      subst w
      simpa using decode_length G s p q hd

theorem decodeTo_valid {s v : Fin n} {p : Route n} (h : Valid G s v p) :
    ∃ w, (decodeTo G s v p).1 = some w ∧ w.length = p.length := by
  obtain ⟨w, hw, hlen⟩ := decode_valid G h
  refine ⟨w.copy rfl h.headD, ?_, by simpa using hlen⟩
  unfold decodeTo
  rw [dif_pos h.headD, hw]
  rfl

theorem decode_cost (s : Fin n) (p : Route n) :
    (decode G s p).2 ≤ 1 + 8 * p.length + p.length ^ 2 := by
  induction p with
  | nil => simp [decode]
  | cons v p ih =>
    dsimp only [decode]
    split_ifs <;> simp only [List.length_cons] <;> nlinarith

theorem decodeTo_cost (s v : Fin n) (p : Route n) :
    (decodeTo G s v p).2 ≤ 3 + 8 * p.length + p.length ^ 2 := by
  have h := decode_cost G s p
  unfold decodeTo
  split_ifs <;> dsimp <;> omega

/-- A fully executable, optional shortest walk and its complete preprocessing
and decoding counter. -/
def walkOption (s v : Fin n) : Option (G.Walk s v) × ℕ :=
  let row := shortestPaths G s
  match row.1[v] with
  | none => (none, row.2 + 1)
  | some p =>
    let decoded := decodeTo G s v p
    (decoded.1, row.2 + decoded.2 + 1)

theorem walkOption_exists_iff (s v : Fin n) :
    (∃ w, (walkOption G s v).1 = some w) ↔ G.Reachable s v := by
  constructor
  · rintro ⟨w, _⟩
    exact ⟨w⟩
  · intro h
    obtain ⟨p, hp⟩ := (shortestPaths_exists_iff G s v).mpr h
    obtain ⟨w, hw, _⟩ := decodeTo_valid G (table_sound G s n v p hp).1
    exact ⟨w, by simp [walkOption, hp, hw]⟩

theorem walkOption_length (s v : Fin n) (w : G.Walk s v)
    (hw : (walkOption G s v).1 = some w) : w.length = G.dist s v := by
  unfold walkOption at hw
  cases hp : (shortestPaths G s).1[v] with
  | none => simp [hp] at hw
  | some p =>
    simp only [hp] at hw
    exact (decodeTo_length G s v p w hw).trans (shortestPaths_length_eq_dist G s v hp)

/-- A reachable pair yields an actual computable shortest walk. The reachability
proof is used only to discharge the impossible `none` case. -/
def walkOfReachable (s v : Fin n) (h : G.Reachable s v) :
    {w : G.Walk s v // w.length = G.dist s v} :=
  let hp : (walkOption G s v).1.isSome := by
    obtain ⟨w, hw⟩ := (walkOption_exists_iff G s v).mpr h
    simp [hw]
  let w := (walkOption G s v).1.get hp
  ⟨w, walkOption_length G s v w (Option.some_get hp).symm⟩

theorem walkOption_cost (s v : Fin n) :
    (walkOption G s v).2 ≤ 2 * n ^ 4 + 18 * n ^ 3 + 6 * n ^ 2 + 11 * n + 4 := by
  have hb := shortestPaths_cost G s
  unfold walkOption
  cases hp : (shortestPaths G s).1[v] with
  | none => simp only [hp]; nlinarith
  | some p =>
    have hd := decodeTo_cost G s v p
    have hlen := (table_sound G s n v p hp).2
    have hsq : p.length ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hlen 2
    simp only [hp]
    nlinarith

/-- Costed certified extraction. The concrete `walkOption` result is evaluated
once and shared by the returned walk and work counter. -/
def walkOfReachableWithCost (s v : Fin n) (h : G.Reachable s v) :
    {w : G.Walk s v // w.length = G.dist s v} × ℕ :=
  let out := walkOption G s v
  let hp : out.1.isSome := by
    obtain ⟨w, hw⟩ := (walkOption_exists_iff G s v).mpr h
    simp [out, hw]
  let w := out.1.get hp
  (⟨w, walkOption_length G s v w (Option.some_get hp).symm⟩, out.2)

@[simp] theorem walkOfReachableWithCost_work (s v : Fin n) (h : G.Reachable s v) :
    (walkOfReachableWithCost G s v h).2 = (walkOption G s v).2 := rfl

@[simp] theorem walkOfReachableWithCost_value (s v : Fin n) (h : G.Reachable s v) :
    (walkOfReachableWithCost G s v h).1 = walkOfReachable G s v h := rfl

theorem walkOfReachableWithCost_cost (s v : Fin n) (h : G.Reachable s v) :
    (walkOfReachableWithCost G s v h).2 ≤
      2 * n ^ 4 + 18 * n ^ 3 + 6 * n ^ 2 + 11 * n + 4 :=
  walkOption_cost G s v

end IndependentSetDiscovery.ShortestPaths
