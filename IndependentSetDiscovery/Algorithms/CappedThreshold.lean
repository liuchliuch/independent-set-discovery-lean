import IndependentSetDiscovery.Algorithms.EagerOptimization

namespace IndependentSetDiscovery.Algorithms

/-- Any threshold beyond all possible candidate-set sizes has the same small-list branch. -/
def capThreshold (n : ℕ) (threshold : ℕ → ℕ) : ℕ → ℕ :=
  fun r => min (n+1) (threshold r)

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- A node consults only the threshold at its current active rank. -/
theorem prefixStep_threshold_congr (ops : PrefixOperations (Fin n))
    (a b : ℕ → ℕ) (s : State (Fin k) (Fin n)) (h : a s.labels.card = b s.labels.card) :
    prefixStep R cost ops a s = prefixStep R cost ops b s := by
  simp only [prefixStep, smallLabels, prefixTotal, prefixes, allPrefixBranches, h]

theorem prefixStep_cap (ops : PrefixOperations (Fin n)) (threshold : ℕ → ℕ)
    (s : State (Fin k) (Fin n)) :
    prefixStep R cost ops (capThreshold n threshold) s = prefixStep R cost ops threshold s := by
  by_cases ht : threshold s.labels.card ≤ n+1
  · apply prefixStep_threshold_congr
    exact Nat.min_eq_right ht
  · have hall : smallLabels threshold s = s.labels := by
      ext i
      simp only [smallLabels, Finset.mem_filter, and_iff_left_iff_imp]
      intro hi
      have hc : (s.candidates i).card ≤ n := by simpa using Finset.card_le_univ (s.candidates i)
      omega
    have hcap : smallLabels (capThreshold n threshold) s = s.labels := by
      ext i
      simp only [smallLabels, Finset.mem_filter, and_iff_left_iff_imp]
      intro hi
      have hc : (s.candidates i).card ≤ n := by simpa using Finset.card_le_univ (s.candidates i)
      unfold capThreshold
      omega
    by_cases hb : s.budget < 0
    · simp [prefixStep, hb]
    by_cases he : s.labels = ∅
    · simp [prefixStep, hb, he]
    have hn := Finset.nonempty_iff_ne_empty.mpr he
    simp [prefixStep, hb, he, hall, hcap, hn]

theorem decidePrefix_cap (ops : PrefixOperations (Fin n)) (threshold : ℕ → ℕ)
    (s : State (Fin k) (Fin n)) :
    decidePrefix R cost ops (capThreshold n threshold) s = decidePrefix R cost ops threshold s := by
  have hf : prefixStep R cost ops (capThreshold n threshold) = prefixStep R cost ops threshold := by
    funext s
    exact prefixStep_cap R cost ops threshold s
  simp only [decidePrefix, hf]

theorem optimize_cap [Inhabited (Fin n)] (ops : PrefixOperations (Fin n)) (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (A : Fin k → Finset (Fin n)) :
    optimize R cost ops (capThreshold n threshold) L A = optimize R cost ops threshold L A := by
  have hf : decidePrefix R cost ops (capThreshold n threshold) = decidePrefix R cost ops threshold := by
    funext s
    exact decidePrefix_cap R cost ops threshold s
  simp only [optimize, hf]

/-- Constant-time threshold lookup after one finite vector has been prepared. -/
def cachedThreshold (table : Vector ℕ (k+1)) (r : ℕ) : ℕ :=
  if h : r < k+1 then table[(⟨r,h⟩ : Fin (k+1))] else 1

theorem prefixStep_cached (ops : PrefixOperations (Fin n)) (threshold : ℕ → ℕ)
    (table : Vector ℕ (k+1)) (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r))
    (s : State (Fin k) (Fin n)) :
    prefixStep R cost ops (cachedThreshold table) s = prefixStep R cost ops threshold s := by
  calc
    _ = prefixStep R cost ops (capThreshold n threshold) s := by
      apply prefixStep_threshold_congr
      have hr : s.labels.card < k+1 := by
        have := Finset.card_le_univ s.labels
        simpa using Nat.lt_succ_of_le this
      simp only [cachedThreshold, dif_pos hr, capThreshold]
      exact htable ⟨s.labels.card,hr⟩
    _ = _ := prefixStep_cap R cost ops threshold s

theorem optimize_cached [Inhabited (Fin n)] (ops : PrefixOperations (Fin n)) (threshold : ℕ → ℕ)
    (table : Vector ℕ (k+1)) (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r))
    (L : Finset (Fin k)) (A : Fin k → Finset (Fin n)) :
    optimize R cost ops (cachedThreshold table) L A = optimize R cost ops threshold L A := by
  have hf : prefixStep R cost ops (cachedThreshold table) = prefixStep R cost ops threshold := by
    funext s
    exact prefixStep_cached R cost ops threshold table htable s
  have hd : decidePrefix R cost ops (cachedThreshold table) = decidePrefix R cost ops threshold := by
    funext s
    simp only [decidePrefix, hf]
  simp only [optimize, hd]

theorem cachedThreshold_bound (threshold : ℕ → ℕ) (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r))
    (mono : Monotone threshold) (r : ℕ) (hr : r ≤ k) :
    cachedThreshold table r ≤ threshold k := by
  have hlt : r < k+1 := by omega
  rw [cachedThreshold, dif_pos hlt, htable ⟨r,hlt⟩]
  exact (Nat.min_le_right _ _).trans (mono hr)

end IndependentSetDiscovery.Algorithms
