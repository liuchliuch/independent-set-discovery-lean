import IndependentSetDiscovery.Algorithms.EagerComplete

/-! # Lookup-depth certificates for returned selections -/
namespace IndependentSetDiscovery.Algorithms

/-- The only function shapes the witness extractor can return. -/
inductive SelectionCode (k n : ℕ) where
  | constant : Fin n → SelectionCode k n
  | write : SelectionCode k n → Fin k → Fin n → SelectionCode k n

def SelectionCode.depth : SelectionCode k n → ℕ
  | .constant _ => 0
  | .write old _ _ => old.depth+1

def SelectionCode.eval : SelectionCode k n → Fin k → Fin n
  | .constant v => fun _ => v
  | .write old i v => Function.update old.eval i v

/-- A measured interpretation of the exact constant/update closures. -/
def SelectionCode.lookup : SelectionCode k n → Fin k → Fin n × ℕ
  | .constant v, _ => (v,1)
  | .write old i v, j =>
    if j=i then (v,1) else
      let answer := old.lookup j
      (answer.1,answer.2+1)

theorem SelectionCode.lookup_spec (p : SelectionCode k n) (i : Fin k) :
    (p.lookup i).1 = p.eval i ∧ (p.lookup i).2 ≤ p.depth+1 := by
  induction p with
  | constant v => simp [SelectionCode.lookup, SelectionCode.eval, SelectionCode.depth]
  | write p j v ih =>
    by_cases h : i=j
    · subst i; simp [SelectionCode.lookup, SelectionCode.eval, SelectionCode.depth]
    · simp [SelectionCode.lookup, SelectionCode.eval, SelectionCode.depth, h, ih.1, ih.2,
        Function.update_of_ne h]

def SelectionCode.materialize (p : SelectionCode k n) : Vector (Fin n) k × ℕ :=
  let entries := Vector.ofFn p.lookup
  (entries.map Prod.fst, k + (entries.toList.map Prod.snd).sum)

theorem SelectionCode.materialize_spec (p : SelectionCode k n) :
    (p.materialize).1 = Vector.ofFn p.eval ∧ (p.materialize).2 ≤ k*(p.depth+2) := by
  constructor
  · apply Vector.ext
    intro i hi
    simp [SelectionCode.materialize, (p.lookup_spec ⟨i,hi⟩).1]
  · have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => (p.lookup_spec (i : Fin k)).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    simp only [SelectionCode.materialize, Vector.toList_ofFn, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    nlinarith

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)
variable [Inhabited (Fin n)]

/-- No arbitrary output callback is assumed: every produced function consists
of at most `fuel` explicit update closures over a constant base function. -/
theorem recoverMeasured_origin (oracle : EagerState k n → Bool × ℕ) :
    ∀ fuel s x, (recoverMeasured R cost oracle fuel s).1 = some x →
      ∃ p : SelectionCode k n, p.eval = x ∧ p.depth ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro s x hx
    simp only [recoverMeasured] at hx
    split_ifs at hx with h
    · have hx' : (fun _ => (default : Fin n)) = x := Option.some.inj hx
      exact ⟨.constant default, hx', by simp [SelectionCode.depth]⟩
  | succ fuel ih =>
    intro s x hx
    simp only [recoverMeasured] at hx
    split_ifs at hx with h hbudget
    · split at hx
      · contradiction
      · rename_i v hv
        rcases Option.map_eq_some_iff.mp hx with ⟨y, hy, hxy⟩
        rcases ih _ y hy with ⟨p, hp, hdepth⟩
        refine ⟨.write p (s.labels.min' h) v, ?_, ?_⟩
        · simpa only [SelectionCode.eval, hp] using hxy
        · simp only [SelectionCode.depth]; omega
    · have hx' : (fun _ => (default : Fin n)) = x := Option.some.inj hx
      exact ⟨.constant default, hx', by simp [SelectionCode.depth]⟩

theorem optimizeEagerComplete_origin (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) (x : Fin k → Fin n)
    (hx : (optimizeEagerComplete R cost threshold L rows).1 = some x) :
    ∃ p : SelectionCode k n, p.eval = x ∧ p.depth ≤ k := by
  unfold optimizeEagerComplete at hx
  dsimp only at hx
  split at hx
  · contradiction
  · rcases recoverMeasured_origin R cost _ L.card _ x hx with ⟨p, hp, hd⟩
    exact ⟨p, hp, hd.trans (by simpa using Finset.card_le_univ L)⟩

/-- A returned selection can be cached in a vector using at most `k(k+2)`
primitive lookup/array-store instructions. -/
theorem optimizeEagerComplete_output_cache_bound (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) (x : Fin k → Fin n)
    (hx : (optimizeEagerComplete R cost threshold L rows).1 = some x) :
    ∃ p : SelectionCode k n, (p.materialize).1 = Vector.ofFn x ∧
      (p.materialize).2 ≤ k*(k+2) := by
  rcases optimizeEagerComplete_origin R cost threshold L rows x hx with ⟨p, hp, hd⟩
  refine ⟨p, ?_, ?_⟩
  · simpa [hp] using p.materialize_spec.1
  · exact p.materialize_spec.2.trans (Nat.mul_le_mul_left k (by omega))

end IndependentSetDiscovery.Algorithms
