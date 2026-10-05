import IndependentSetDiscovery.Transversal.CheapPrefix
import Mathlib.Tactic

/-!
# Costed finite-list primitives and refinement

One instruction is a list-cell inspection/construction, a vertex equality/order
comparison, or an exact rational comparison/addition. Counters below are
computed by the actual recursive programs. Value-refinement theorems connect
them to the list and finite-set operations used by the concrete prefix solver.
-/
namespace IndependentSetDiscovery.Algorithms

/-- Costed merge, with one comparison/cons instruction at each nonempty pair. -/
def mergeCounted (cmp : α → α → Bool) : List α → List α → List α × ℕ
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if cmp x y then
      let r := mergeCounted cmp xs (y :: ys)
      (x :: r.1, r.2 + 1)
    else
      let r := mergeCounted cmp (x :: xs) ys
      (y :: r.1, r.2 + 1)

theorem mergeCounted_value (cmp : α → α → Bool) : ∀ xs ys,
    (mergeCounted cmp xs ys).1 = xs.merge ys cmp
  | [], ys => by simp [mergeCounted, List.merge]
  | x :: xs, [] => by simp [mergeCounted, List.merge]
  | x :: xs, y :: ys => by
      cases h : cmp x y <;>
        simp [mergeCounted, List.merge, h, mergeCounted_value cmp xs (y :: ys),
          mergeCounted_value cmp (x :: xs) ys]
termination_by xs ys => xs.length + ys.length

theorem mergeCounted_cost (cmp : α → α → Bool) : ∀ xs ys,
    (mergeCounted cmp xs ys).2 ≤ xs.length + ys.length
  | [], ys => by simp [mergeCounted]
  | x :: xs, [] => by simp [mergeCounted]
  | x :: xs, y :: ys => by
      cases h : cmp x y
      · have ih := mergeCounted_cost cmp (x :: xs) ys
        simp only [mergeCounted, h, Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_cons] at *
        omega
      · have ih := mergeCounted_cost cmp xs (y :: ys)
        simp only [mergeCounted, h, ↓reduceIte]
        simp only [List.length_cons] at *
        omega
termination_by xs ys => xs.length + ys.length

/-- The same contiguous split, recursive calls and merge as Lean's merge sort.
The split is billed one instruction per input cell. -/
def mergeSortCounted (cmp : α → α → Bool) : (xs : List α) → List α × ℕ
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: as =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a :: b :: as, rfl⟩
    have := by simpa using lr.2.2
    have := by simpa using lr.1.2
    let left := mergeSortCounted cmp lr.1
    let right := mergeSortCounted cmp lr.2
    let joined := mergeCounted cmp left.1 right.1
    (joined.1, left.2 + right.2 + joined.2 + 2 * (a :: b :: as).length)
termination_by xs => xs.length

theorem mergeSortCounted_value (cmp : α → α → Bool) : ∀ xs,
    (mergeSortCounted cmp xs).1 = xs.mergeSort cmp
  | [] => by simp [mergeSortCounted, List.mergeSort]
  | [a] => by simp [mergeSortCounted, List.mergeSort]
  | a :: b :: as => by
    let lr := List.MergeSort.Internal.splitInTwo ⟨a :: b :: as, rfl⟩
    have hleft := mergeSortCounted_value cmp lr.1
    have hright := mergeSortCounted_value cmp lr.2
    simp only [mergeSortCounted, List.mergeSort, mergeCounted_value]
    exact congrArg₂ (fun x y => x.merge y cmp) hleft hright
termination_by xs => xs.length

theorem mergeSortCounted_length (cmp : α → α → Bool) (xs : List α) :
    (mergeSortCounted cmp xs).1.length = xs.length := by
  rw [mergeSortCounted_value, List.length_mergeSort]

/-- A concrete quadratic bound, stronger than what the prefix work tariff uses. -/
theorem mergeSortCounted_cost (cmp : α → α → Bool) : ∀ xs,
    (mergeSortCounted cmp xs).2 ≤ 4 * xs.length^2
  | [] => by simp [mergeSortCounted]
  | [a] => by simp [mergeSortCounted]
  | a :: b :: as => by
    let lr := List.MergeSort.Internal.splitInTwo ⟨a :: b :: as, rfl⟩
    have hl := mergeSortCounted_cost cmp lr.1
    have hr := mergeSortCounted_cost cmp lr.2
    have hm := mergeCounted_cost cmp
      (mergeSortCounted cmp lr.1).1 (mergeSortCounted cmp lr.2).1
    rw [mergeSortCounted_length, mergeSortCounted_length] at hm
    have hll := lr.1.2
    have hrl := lr.2.2
    have hsplit : lr.1.1.length + lr.2.1.length = (a :: b :: as).length := by omega
    have hposl : 1 ≤ lr.1.1.length := by simp only [List.length_cons] at *; omega
    have hposr : 1 ≤ lr.2.1.length := by simp only [List.length_cons] at *; omega
    have hcross : (a :: b :: as).length ≤ 2 * lr.1.1.length * lr.2.1.length := by
      nlinarith
    rw [mergeSortCounted]
    change (mergeSortCounted cmp lr.1).2 + (mergeSortCounted cmp lr.2).2 +
      (mergeCounted cmp (mergeSortCounted cmp lr.1).1 (mergeSortCounted cmp lr.2).1).2 +
        2 * (a :: b :: as).length ≤ _
    nlinarith
termination_by xs => xs.length

/-- Any list representation of a finite set gives the very same sorted output.
Thus the finite-set sort bound does not assume a favorable representation. -/
theorem finset_sort_refinement {α : Type*} [LinearOrder α] (A : Finset α)
    (xs : List α) (hxs : (xs : Multiset α) = A.val) :
    (mergeSortCounted (fun a b => decide (a ≤ b)) xs).1 = A.sort (· ≤ ·) ∧
      (mergeSortCounted (fun a b => decide (a ≤ b)) xs).2 ≤ 4 * A.card^2 := by
  constructor
  · rw [mergeSortCounted_value]
    change Multiset.sort (· ≤ ·) (xs : Multiset α) = _
    rw [hxs]
    rfl
  · have hlen : xs.length = A.card := by
      have := congrArg Multiset.card hxs
      simpa using this
    simpa [hlen] using mergeSortCounted_cost (fun a b => decide (a ≤ b)) xs

/-- Costed filtering performs exactly one predicate query per candidate. -/
def filterCounted (p : α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: as =>
      let r := filterCounted p as
      (if p a then a :: r.1 else r.1, r.2 + 1)

theorem filterCounted_spec (p : α → Bool) (xs : List α) :
    (filterCounted p xs).1 = xs.filter p ∧ (filterCounted p xs).2 = xs.length := by
  induction xs with
  | nil => simp [filterCounted]
  | cons a as ih => cases h : p a <;> simp [filterCounted, h, ih.1, ih.2]

/-- Costed mapping invokes its function once per input cell. -/
def mapCounted (f : α → β) : List α → List β × ℕ
  | [] => ([], 0)
  | a :: as => let r := mapCounted f as; (f a :: r.1, r.2 + 1)

theorem mapCounted_spec (f : α → β) (xs : List α) :
    (mapCounted f xs).1 = xs.map f ∧ (mapCounted f xs).2 = xs.length := by
  induction xs with
  | nil => simp [mapCounted]
  | cons a as ih => simp [mapCounted, ih.1, ih.2]

/-- Costed fold, used for prefix maxima, arithmetic sums and denominator products. -/
def foldCounted (f : β → α → β) : β → List α → β × ℕ
  | b, [] => (b, 0)
  | b, a :: as => let r := foldCounted f (f b a) as; (r.1, r.2 + 1)

theorem foldCounted_spec (f : β → α → β) (b : β) (xs : List α) :
    (foldCounted f b xs).1 = xs.foldl f b ∧ (foldCounted f b xs).2 = xs.length := by
  induction xs generalizing b with
  | nil => simp [foldCounted]
  | cons a as ih => simpa [foldCounted] using ih (f b a)

/-- Bounded take, counting exactly the inspected output cells. -/
def takeCounted : ℕ → List α → List α × ℕ
  | 0, _ => ([], 0)
  | _ + 1, [] => ([], 0)
  | n + 1, a :: as => let r := takeCounted n as; (a :: r.1, r.2 + 1)

theorem takeCounted_spec (n : ℕ) (xs : List α) :
    (takeCounted n xs).1 = xs.take n ∧ (takeCounted n xs).2 = min n xs.length := by
  induction n generalizing xs with
  | zero => simp [takeCounted]
  | succ n ih => cases xs with
    | nil => simp [takeCounted]
    | cons a as => simp [takeCounted, (ih as).1, (ih as).2, Nat.add_min_add_right]

/-- Prefix maximum uses one cost lookup and one maximum comparison per vertex. -/
def peakCounted (c : α → ℚ) (xs : List α) : ℚ × ℕ :=
  let values := mapCounted c xs
  let peak := foldCounted max 0 values.1
  (peak.1, values.2 + peak.2)

theorem peakCounted_spec (c : α → ℚ) (xs : List α) :
    (peakCounted c xs).1 = (xs.map c).foldl max 0 ∧
      (peakCounted c xs).2 = 2 * xs.length := by
  simp [peakCounted, (mapCounted_spec c xs).1, (mapCounted_spec c xs).2,
    (foldCounted_spec max 0 (xs.map c)).1, (foldCounted_spec max 0 (xs.map c)).2]
  omega

theorem prefixMax_refinement {α : Type*} [LinearOrder α] (c : α → ℚ) (A : Finset α)
    (xs : List α) (hxs : (xs : Multiset α) = A.val) :
    (peakCounted c xs).1 = IndependentSetDiscovery.prefixMax c A := by
  rw [(peakCounted_spec c xs).1]
  simp [IndependentSetDiscovery.prefixMax, Finset.fold, ← hxs, List.foldl_eq_foldr]

/-- This avoids a redundant duplicate-removal pass: the sorted prefix is
already proved duplicate-free. The proof is erased when the function runs. -/
def cheapPrefixFast {α : Type*} [LinearOrder α] (c : α → ℚ) (A : Finset α) (t : ℕ) : Finset α :=
  ⟨↑((costOrdered c A).take t), (nodup_costOrdered c A).take⟩

theorem cheapPrefixFast_eq {α : Type*} [LinearOrder α] (c : α → ℚ) (A : Finset α) (t : ℕ) :
    cheapPrefixFast c A t = cheapPrefix c A t := by
  ext v
  simp [cheapPrefixFast, cheapPrefix]

/-- Two measured sorts followed by the measured prefix traversal. -/
def prefixListCounted {α : Type*} [LinearOrder α] (c : α → ℚ) (t : ℕ) (xs : List α) : List α × ℕ :=
  let vertices := mergeSortCounted (fun a b => decide (a ≤ b)) xs
  let costs := mergeSortCounted (fun a b => decide (c a ≤ c b)) vertices.1
  let kept := takeCounted t costs.1
  (kept.1, vertices.2 + costs.2 + kept.2)

theorem prefixListCounted_refinement {α : Type*} [LinearOrder α]
    (c : α → ℚ) (A : Finset α) (t : ℕ) (xs : List α) (hxs : (xs : Multiset α) = A.val) :
    (prefixListCounted c t xs).1.toFinset = cheapPrefix c A t ∧
      (prefixListCounted c t xs).2 + (peakCounted c (prefixListCounted c t xs).1).2 ≤
        8 * (A.card + 1)^2 := by
  have hv := finset_sort_refinement A xs hxs
  have hlen : xs.length = A.card := by
    have := congrArg Multiset.card hxs
    simpa using this
  have hc := mergeSortCounted_cost (fun a b => decide (c a ≤ c b))
    (mergeSortCounted (fun a b => decide (a ≤ b)) xs).1
  rw [mergeSortCounted_length, hlen] at hc
  have ht := takeCounted_spec t
    (mergeSortCounted (fun a b => decide (c a ≤ c b))
      (mergeSortCounted (fun a b => decide (a ≤ b)) xs).1).1
  have htl : (mergeSortCounted (fun a b => decide (c a ≤ c b))
      (mergeSortCounted (fun a b => decide (a ≤ b)) xs).1).1.length = A.card := by
    rw [mergeSortCounted_length, mergeSortCounted_length, hlen]
  have hout : (prefixListCounted c t xs).1 = (costOrdered c A).take t := by
    unfold prefixListCounted
    dsimp only
    rw [ht.1, mergeSortCounted_value, hv.1]
    rfl
  constructor
  · rw [hout]; rfl
  · have hpeak := (peakCounted_spec c (prefixListCounted c t xs).1).2
    have hlenout : (prefixListCounted c t xs).1.length = min t A.card := by
      rw [hout, List.length_take, length_costOrdered]
    rw [hlenout] at hpeak
    change _ + _ + _ + _ ≤ _
    rw [ht.2, htl]
    have hmin : min t A.card ≤ A.card := Nat.min_le_right _ _
    nlinarith [hv.2]

theorem prefixListCounted_value {α : Type*} [LinearOrder α]
    (c : α → ℚ) (A : Finset α) (t : ℕ) (xs : List α) (hxs : (xs : Multiset α) = A.val) :
    (prefixListCounted c t xs).1 = (costOrdered c A).take t := by
  have hv := (finset_sort_refinement A xs hxs).1
  unfold prefixListCounted
  dsimp only
  rw [(takeCounted_spec _ _).1, mergeSortCounted_value, hv]
  rfl

/-- Executable concrete prefix and peak, carrying the primitive trace charge.
The finite-set's internal representation is first canonically enumerated; that
sort is charged by the representation-independent bound proved above. -/
def measuredPrefix {α : Type*} [LinearOrder α] (c : α → ℚ) (A : Finset α) (t : ℕ) :
    Finset α × ℚ × ℕ :=
  let listed := A.sort (· ≤ ·)
  let kept := prefixListCounted c t listed
  have hrep : (listed : Multiset α) = A.val := Finset.sort_eq _ _
  have hnd : kept.1.Nodup := by
    rw [prefixListCounted_value c A t listed hrep]
    exact (nodup_costOrdered c A).take
  let P : Finset α := ⟨↑kept.1, hnd⟩
  let maximum := peakCounted c kept.1
  (P, maximum.1, 4 * A.card^2 + kept.2 + maximum.2)

theorem measuredPrefix_spec {α : Type*} [LinearOrder α]
    (c : α → ℚ) (A : Finset α) (t : ℕ) :
    (measuredPrefix c A t).1 = cheapPrefix c A t ∧
    (measuredPrefix c A t).2.1 = prefixMax c (cheapPrefix c A t) ∧
    (measuredPrefix c A t).2.2 ≤ 12 * (A.card+1)^2 := by
  have hrep : ((A.sort (· ≤ ·)) : Multiset α) = A.val := Finset.sort_eq _ _
  have hv := prefixListCounted_value c A t (A.sort (· ≤ ·)) hrep
  have hc := (prefixListCounted_refinement c A t (A.sort (· ≤ ·)) hrep).2
  have hset : (measuredPrefix c A t).1 = cheapPrefix c A t := by
    ext v
    simp [measuredPrefix, hv, cheapPrefix]
  refine ⟨hset, ?_, ?_⟩
  · change (peakCounted c (prefixListCounted c t (A.sort (· ≤ ·))).1).1 = _
    rw [hv]
    apply prefixMax_refinement
    rw [← cheapPrefixFast_eq]
    rfl
  · change 4*A.card^2 + _ + _ ≤ _
    have hh := Nat.add_le_add_left hc (4*A.card^2)
    have hpow := Nat.pow_le_pow_left (Nat.le_succ A.card) 2
    change A.card^2 ≤ (A.card+1)^2 at hpow
    have hp : 4*A.card^2 + 8*(A.card+1)^2 ≤ 12*(A.card+1)^2 := by omega
    apply le_trans _ hp
    simpa only [Nat.add_assoc] using hh

/-- Composition of a measured element program with an explicit finite-set
fold. The sorted enumeration has the proven representation-independent cost;
the map and fold each inspect every resulting cell once. -/
def foldMapMeasured {α : Type*} [LinearOrder α] (f : α → β × ℕ)
    (op : β → β → β) (b : β) (A : Finset α) : β × ℕ :=
  let answers := (A.sort (· ≤ ·)).map f
  let result := foldCounted op b (answers.map Prod.fst)
  (result.1, 4*A.card^2 + (answers.map Prod.snd).sum + 2*A.card)

theorem foldMapMeasured_value {α : Type*} [LinearOrder α] (f : α → β × ℕ)
    (op : β → β → β) [Std.Commutative op] [Std.Associative op] (b : β) (A : Finset α) :
    (foldMapMeasured f op b A).1 = A.fold op b (fun a => (f a).1) := by
  unfold foldMapMeasured
  rw [(foldCounted_spec _ _ _).1]
  simp only [List.map_map, Function.comp_def]
  unfold Finset.fold
  rw [← Finset.sort_eq (· ≤ ·) A, Multiset.map_coe, Multiset.coe_fold_l]

theorem foldMapMeasured_cost {α : Type*} [LinearOrder α] (f : α → β × ℕ)
    (op : β → β → β) (b : β) (A : Finset α) (C : ℕ)
    (hf : ∀ a ∈ A, (f a).2 ≤ C) :
    (foldMapMeasured f op b A).2 ≤ 4*A.card^2 + A.card*C + 2*A.card := by
  unfold foldMapMeasured
  simp only [List.map_map, Function.comp_def]
  have hsum : ((A.sort (· ≤ ·)).map (fun a => (f a).2)).sum ≤ A.card*C := by
    calc
      _ ≤ ((A.sort (· ≤ ·)).map (fun _ => C)).sum :=
        List.sum_le_sum (fun a ha => hf a ((Finset.mem_sort (· ≤ ·)).mp ha))
      _ = _ := by simp
  omega

/-- Exact filter trace for any underlying list representation of a finite set.
Unlike conversion through `toFinset`, filtering preserves the existing nodup
proof and performs no duplicate-removal pass. -/
theorem finset_filter_refinement {α : Type*} (A : Finset α)
    (p : α → Prop) [DecidablePred p] (xs : List α) (hxs : (xs : Multiset α) = A.val) :
    ((filterCounted (fun a => decide (p a)) xs).1 : Multiset α) = (A.filter p).val ∧
      (filterCounted (fun a => decide (p a)) xs).2 = A.card := by
  constructor
  · rw [(filterCounted_spec _ _).1]
    simpa [Finset.filter_val, ← hxs]
  · rw [(filterCounted_spec _ _).2]
    have := congrArg Multiset.card hxs
    simpa using this

end IndependentSetDiscovery.Algorithms
