import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Finite counting for independent transversals

A direct two-vertex-forbidden-pattern specialization of the counting induction
of Wanless--Wood, rather than an assumed transversal oracle.
-/
namespace IndependentSetDiscovery.Transversal

open Finset

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]
variable (A : ι → Finset V) (R : V → V → Prop)

/-- A partial selection, normalized to `none` off its label set, and avoiding
all ordered conflicts between different labels. -/
def GoodOn (s : Finset ι) (f : ι → Option V) : Prop :=
  (∀ i ∈ s, ∃ v ∈ A i, f i = some v) ∧
  (∀ i, i ∉ s → f i = none) ∧
  (∀ i j u v, i ≠ j → f i = some u → f j = some v → ¬ R u v)

abbrev Good (s : Finset ι) := {f : ι → Option V // GoodOn A R s f}

noncomputable instance goodFintype (s : Finset ι) : Fintype (Good A R s) :=
  Fintype.ofFinite _

noncomputable def count (s : Finset ι) : ℕ := Fintype.card (Good A R s)

/-- Delete one label from a compatible partial assignment. -/
def eraseGood {s : Finset ι} (f : Good A R s) (j : ι) : Good A R (s.erase j) := by
  classical
  refine ⟨Function.update f.1 j none, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨v, hv, hfv⟩ := f.2.1 i (mem_of_mem_erase hi)
    exact ⟨v, hv, by simpa [Function.update_of_ne (ne_of_mem_erase hi)] using hfv⟩
  · intro i hi
    by_cases hij : i = j
    · subst i
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hij]
      exact f.2.2.1 i (by simpa [mem_erase, hij] using hi)
  · intro i k u v hik hi hk
    have hij : i ≠ j := by
      intro h
      subst i
      rw [Function.update_self] at hi
      contradiction
    have hkj : k ≠ j := by
      intro h
      subst k
      rw [Function.update_self] at hk
      contradiction
    exact f.2.2.2 i k u v hik (by simpa [Function.update_of_ne hij] using hi)
      (by simpa [Function.update_of_ne hkj] using hk)

/-- The finite forbidden pairs across two candidate lists. -/
noncomputable def pairs (i j : ι) : Finset (V × V) := by
  classical
  exact ((A i) ×ˢ (A j)).filter (fun p => R p.1 p.2)

@[simp] theorem mem_pairs (i j : ι) (u v : V) :
    (u,v) ∈ pairs A R i j ↔ u ∈ A i ∧ v ∈ A j ∧ R u v := by
  classical
  simp [pairs, and_assoc]

def BadExtension (s : Finset ι) (i : ι) (x : Good A R s × ↥(A i)) : Prop :=
  ∃ j ∈ s, ∃ u, x.1.1 j = some u ∧ R x.2.1 u

/-- A nonbad extension is a compatible assignment on the larger label set. -/
def extendGood (hR : Symmetric R) {s : Finset ι} {i : ι} (hi : i ∉ s)
    (x : Good A R s × ↥(A i)) (hx : ¬ BadExtension A R s i x) :
    Good A R (insert i s) := by
  classical
  refine ⟨Function.update x.1.1 i (some x.2.1), ?_, ?_, ?_⟩
  · intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact ⟨x.2.1, x.2.2, by simp⟩
    · obtain ⟨u, hu, hfu⟩ := x.1.2.1 j hj
      exact ⟨u, hu, by simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hfu⟩
  · intro j hj
    have hji : j ≠ i := by intro h; apply hj; simp [h]
    rw [Function.update_of_ne hji]
    exact x.1.2.2.1 j (fun h => hj (mem_insert_of_mem h))
  · intro j k u v hjk hj hk
    by_cases hji : j = i
    · subst j
      have hki : k ≠ i := Ne.symm hjk
      simp only [Function.update_self, Option.some.injEq] at hj
      subst u
      rw [Function.update_of_ne hki] at hk
      intro hconf
      have hks : k ∈ s := by
        by_contra hh
        rw [x.1.2.2.1 k hh] at hk
        contradiction
      exact hx ⟨k, hks, v, hk, hconf⟩
    · rw [Function.update_of_ne hji] at hj
      by_cases hki : k = i
      · subst k
        simp only [Function.update_self, Option.some.injEq] at hk
        subst v
        intro hconf
        have hjs : j ∈ s := by
          by_contra hh
          rw [x.1.2.2.1 j hh] at hj
          contradiction
        exact hx ⟨j, hjs, u, hj, hR hconf⟩
      · rw [Function.update_of_ne hki] at hk
        exact x.1.2.2.2 j k u v hjk hj hk

theorem extendGood_injective (hR : Symmetric R) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    Function.Injective (fun x : {x : Good A R s × ↥(A i) // ¬ BadExtension A R s i x} =>
      extendGood A R hR hi x.1 x.2) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      rw [x.1.1.2.2.1 i hi, y.1.1.2.2.1 i hi]
    · have hj := congrArg (fun f : Good A R (insert i s) => f.1 j) h
      simpa [extendGood, Function.update_of_ne hji] using hj
  · apply Subtype.ext
    have hj := congrArg (fun f : Good A R (insert i s) => f.1 i) h
    simpa [extendGood] using hj

/-- A bad extension is encoded by one forbidden pair and the assignment with
its second endpoint erased. -/
noncomputable def encodeBad {s : Finset ι} {i : ι}
    (x : {x : Good A R s × ↥(A i) // BadExtension A R s i x}) :
    (j : ↥s) × (↥(pairs A R i j.1) × Good A R (s.erase j.1)) := by
  classical
  let j := Classical.choose x.2
  have hj := Classical.choose_spec x.2
  let u := Classical.choose hj.2
  have hu := Classical.choose_spec hj.2
  have hua : u ∈ A j := by
    obtain ⟨v, hva, hv⟩ := x.1.1.2.1 j hj.1
    have : v = u := Option.some.inj (hv.symm.trans hu.1)
    simpa [this] using hva
  exact ⟨⟨j, hj.1⟩, ⟨⟨(x.1.2.1, u), (mem_pairs A R i j _ _).mpr
    ⟨x.1.2.2, hua, hu.2⟩⟩, eraseGood A R x.1.1 j⟩⟩

/-- Recover the original raw extension from its bad-extension code. -/
def decodeBad {s : Finset ι} {i : ι}
    (w : (j : ↥s) × (↥(pairs A R i j.1) × Good A R (s.erase j.1))) :
    (ι → Option V) × V :=
  (Function.update w.2.2.1 w.1.1 (some w.2.1.1.2), w.2.1.1.1)

theorem decode_encodeBad {s : Finset ι} {i : ι}
    (x : {x : Good A R s × ↥(A i) // BadExtension A R s i x}) :
    decodeBad A R (encodeBad A R x) = (x.1.1.1, x.1.2.1) := by
  classical
  apply Prod.ext
  · funext k
    unfold decodeBad encodeBad eraseGood
    dsimp
    rw [Function.update_idem]
    have hu := Classical.choose_spec (Classical.choose_spec x.2).2
    by_cases hk : k = Classical.choose x.2
    · subst k
      simp only [Function.update_self]
      exact hu.1.symm
    · rw [Function.update_of_ne hk]
  · rfl

theorem encodeBad_injective {s : Finset ι} {i : ι} :
    Function.Injective (@encodeBad ι V _ _ _ _ A R s i) := by
  intro x y h
  have hh := congrArg (decodeBad A R) h
  rw [decode_encodeBad, decode_encodeBad] at hh
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hh)
  · exact Subtype.ext (congrArg Prod.snd hh)

/-- The finite extension-count recurrence underlying Wanless--Wood. -/
theorem count_recurrence (hR : Symmetric R) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (A i).card * count A R s ≤ count A R (insert i s) +
      ∑ j ∈ s, (pairs A R i j).card * count A R (s.erase j) := by
  classical
  let E := Good A R s × ↥(A i)
  let bad : E → Prop := BadExtension A R s i
  have hsplit : Fintype.card E = Fintype.card {x : E // bad x} +
      Fintype.card {x : E // ¬ bad x} := by
    simpa using (Fintype.card_congr (Equiv.sumCompl bad)).symm
  have hgood := Fintype.card_le_of_injective _ (extendGood_injective A R hR hi)
  have hbad := Fintype.card_le_of_injective _ (@encodeBad_injective ι V _ _ _ _ A R s i)
  have hbad' : Fintype.card {x : E // bad x} ≤
      ∑ j ∈ s, (pairs A R i j).card * count A R (s.erase j) := by
    rw [← Finset.sum_coe_sort s]
    simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe, count] using hbad
  have hgood' : Fintype.card {x : E // ¬ bad x} ≤ count A R (insert i s) := hgood
  have hE : Fintype.card E = (A i).card * count A R s := by
    simp [E, count, Nat.mul_comm]
  omega

/-- The simultaneous multiplicative-growth induction of Wanless--Wood.
Only finite counting and ordered-field arithmetic are used. -/
theorem count_growth (hR : Symmetric R) {β : ℝ} (hβ : 0 < β)
    (hdegree : ∀ (i : ι) (s : Finset ι), i ∉ s →
      (∑ j ∈ s, ((pairs A R i j).card : ℝ)) ≤ β * ((A i).card - β)) :
    ∀ (s : Finset ι) (i : ι), i ∉ s →
      β * (count A R s : ℝ) ≤ (count A R (insert i s) : ℝ) := by
  intro s
  induction s using Finset.strongInductionOn
  rename_i s ih
  intro i hi
  have hrec : ((A i).card : ℝ) * count A R s ≤ count A R (insert i s) +
      ∑ j ∈ s, ((pairs A R i j).card : ℝ) * count A R (s.erase j) := by
    exact_mod_cast count_recurrence A R hR s i hi
  have hsum : β * (∑ j ∈ s, ((pairs A R i j).card : ℝ) *
        count A R (s.erase j)) ≤
      (∑ j ∈ s, ((pairs A R i j).card : ℝ)) * count A R s := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hh := ih (s.erase j) (Finset.erase_ssubset hj) j (by simp)
    rw [Finset.insert_erase hj] at hh
    have hh' := mul_le_mul_of_nonneg_left hh
      (show (0 : ℝ) ≤ (pairs A R i j).card by positivity)
    nlinarith
  have hdeg := mul_le_mul_of_nonneg_right (hdegree i s hi)
    (show (0 : ℝ) ≤ count A R s by positivity)
  have hrec' := mul_le_mul_of_nonneg_left hrec (le_of_lt hβ)
  have hfinish : β * (β * (count A R s : ℝ)) ≤
      β * (count A R (insert i s) : ℝ) := by nlinarith
  exact (mul_le_mul_left hβ).mp hfinish

/-- Positive growth gives a compatible selection on every label set. -/
theorem count_pos (hR : Symmetric R) {β : ℝ} (hβ : 0 < β)
    (hdegree : ∀ (i : ι) (s : Finset ι), i ∉ s →
      (∑ j ∈ s, ((pairs A R i j).card : ℝ)) ≤ β * ((A i).card - β))
    (s : Finset ι) : 0 < count A R s := by
  induction s using Finset.induction_on with
  | empty =>
      change 0 < Fintype.card (Good A R ∅)
      apply Fintype.card_pos_iff.mpr
      refine ⟨⟨fun _ => none, ?_⟩⟩
      simp [GoodOn]
  | @insert i s hi ih =>
      have h := count_growth A R hR hβ hdegree s i hi
      have hp : (0 : ℝ) < β * count A R s := mul_pos hβ (by exact_mod_cast ih)
      have : (0 : ℝ) < count A R (insert i s) := hp.trans_le h
      exact_mod_cast this

/-- General finite forbidden-pair criterion. This is the equal-coordinate-cost
specialization of the Wanless--Wood counting framework. -/
theorem exists_selection (hR : Symmetric R) {β : ℝ} (hβ : 0 < β)
    (hdegree : ∀ (i : ι) (s : Finset ι), i ∉ s →
      (∑ j ∈ s, ((pairs A R i j).card : ℝ)) ≤ β * ((A i).card - β)) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => ¬ R (x i) (x j)) := by
  classical
  obtain ⟨f⟩ := Fintype.card_pos_iff.mp (count_pos A R hR hβ hdegree univ)
  have hf : ∀ i, ∃ v ∈ A i, f.1 i = some v := fun i => f.2.1 i (mem_univ i)
  choose x hmem hx using hf
  refine ⟨x, hmem, ?_⟩
  intro i j hij
  exact f.2.2.2 i j (x i) (x j) hij (hx i) (hx j)

/-- Wanless--Wood's block-average criterion, including unequal block sizes.
The parameter must be positive; allowing `t = 0` would permit empty blocks. -/
theorem wanlessWood (hR : Symmetric R) (t : ℕ) (ht : 0 < t)
    (hsize : ∀ i, t ≤ (A i).card)
    (hcross : ∀ i, 4 * (∑ j ∈ univ.erase i, (pairs A R i j).card) ≤
      t * (A i).card) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => ¬ R (x i) (x j)) := by
  classical
  apply exists_selection A R hR (β := (t : ℝ) / 2) (by positivity)
  intro i s hi
  have hsub : s ⊆ univ.erase i := by
    intro j hj
    exact mem_erase.mpr ⟨ne_of_mem_of_not_mem hj hi, mem_univ j⟩
  have hsum : (∑ j ∈ s, (pairs A R i j).card) ≤
      ∑ j ∈ univ.erase i, (pairs A R i j).card :=
    Finset.sum_le_sum_of_subset hsub
  have hc : (4 : ℝ) * (∑ j ∈ univ.erase i, ((pairs A R i j).card : ℝ)) ≤
      (t : ℝ) * (A i).card := by exact_mod_cast hcross i
  have hs : (∑ j ∈ s, ((pairs A R i j).card : ℝ)) ≤
      ∑ j ∈ univ.erase i, ((pairs A R i j).card : ℝ) := by exact_mod_cast hsum
  have hz : (0 : ℝ) ≤ t := by positivity
  have hn : (t : ℝ) ≤ (A i).card := by exact_mod_cast hsize i
  have hp : (t : ℝ) * t ≤ (t : ℝ) * (A i).card := mul_le_mul_of_nonneg_left hn hz
  nlinarith

/-- Convenient equal-size form used by every sparse-prefix application. -/
theorem wanlessWood_equal (hR : Symmetric R) (t : ℕ) (ht : 0 < t)
    (hsize : ∀ i, (A i).card = t)
    (hcross : ∀ i, 4 * (∑ j ∈ univ.erase i, (pairs A R i j).card) ≤ t^2) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => ¬ R (x i) (x j)) := by
  apply wanlessWood A R hR t ht (fun i => (hsize i).ge)
  intro i
  simpa [hsize i, pow_two] using hcross i

end IndependentSetDiscovery.Transversal
