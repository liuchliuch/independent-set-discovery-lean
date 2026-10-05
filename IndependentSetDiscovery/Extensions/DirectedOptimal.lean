import IndependentSetDiscovery.Extensions.DirectedAssignment
import IndependentSetDiscovery.Extensions.DirectedPaths

/-! # Lexicographically optimal directed weighted discovery

This is the reconstruction half of Corollary 5.6. A globally optimal scalar
assignment gives the actual lexicographically optimal collision-free sequence.
The bounded-simple-path surrogate is used for comparisons with arbitrary long
competitor sequences, rather than assuming their slide counts are bounded.
-/

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (Gf : SimpleGraph V) (D : V → V → Prop) (w : V → V → ℕ)

def LexOptimal (S T : Finset V) (c n : ℕ) : Prop :=
  Independent Gf T ∧ DirectedSlideSequence D w S T c n ∧
    ∀ T' c' n', Independent Gf T' → DirectedSlideSequence D w S T' c' n' →
      c ≤ c' ∧ (c = c' → n ≤ n')

/-- An optimal scalarized path assignment reconstructs an optimal sequence for
the original ordered pair `(movement cost, number of slides)`. -/
theorem reconstruct_lex_optimal {S T : Finset V}
    (r : Routing D (fun u v => scalarizationBase S.card (Fintype.card V) * w u v + 1) S T)
    (hT : Independent Gf T)
    (hmin : ∀ T', Independent Gf T' →
      ∀ r' : Routing D
        (fun u v => scalarizationBase S.card (Fintype.card V) * w u v + 1) S T',
        r.total ≤ r'.total) :
    ∃ c n, LexOptimal Gf D w S T c n ∧ n ≤ S.card * (Fintype.card V - 1) ∧
      r.total = scalarizationBase S.card (Fintype.card V) * c + n := by
  let C := scalarizationBase S.card (Fintype.card V)
  let K := S.card * (Fintype.card V - 1)
  have hC : C = K + 1 := rfl
  obtain ⟨c, n, hcost, hseq⟩ := scalarized_routing_realize (w := w) C r
  obtain ⟨rs, hrs⟩ := routing_of_directedSlideSequence (hseq.scalarize C)
  have hm := hmin T hT rs
  have hscore : r.total = C * c + n := by omega
  have hlength : n ≤ K := by
    obtain ⟨ro, hro⟩ := routing_of_directedSlideSequence hseq
    obtain ⟨rb, a, b, hrb, ha, hb⟩ := ro.bounded_scalar_surrogate C
    have hminb := hmin T hT rb
    have ham : C * a ≤ C * c := Nat.mul_le_mul_left C (by omega)
    change b ≤ K at hb
    omega
  refine ⟨c, n, ⟨hT, hseq, ?_⟩, hlength, hscore⟩
  intro T' c' n' hT' hs'
  have hprimary : c ≤ c' := by
    by_contra hc
    have hclt : c' < c := by omega
    obtain ⟨ro, hro⟩ := routing_of_directedSlideSequence hs'
    obtain ⟨rb, a, b, hrb, ha, hb⟩ := ro.bounded_scalar_surrogate C
    have hminb := hmin T' hT' rb
    have halt : a < c := by omega
    have ham := Nat.mul_le_mul_left C (Nat.succ_le_of_lt halt)
    change b ≤ K at hb
    nlinarith
  refine ⟨hprimary, ?_⟩
  intro hcc
  obtain ⟨rc, hrc⟩ := routing_of_directedSlideSequence (hs'.scalarize C)
  have hminc := hmin T' hT' rc
  subst c'
  omega

/-- Every reachable independent target admits a globally lexicographically
optimal sequence. Its number of slides is at most `k(n-1)`, even when arc
weights are zero. -/
theorem exists_lex_optimal {S : Finset V}
    (h : ∃ T c n, Independent Gf T ∧ DirectedSlideSequence D w S T c n) :
    ∃ T c n, LexOptimal Gf D w S T c n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  classical
  let C := scalarizationBase S.card (Fintype.card V)
  let P : ℕ → Prop := fun b => ∃ T, Independent Gf T ∧
    ∃ r : Routing D (fun u v => C * w u v + 1) S T, r.total = b
  have hex : ∃ b, P b := by
    obtain ⟨T, c, n, hT, hs⟩ := h
    obtain ⟨r, hr⟩ := routing_of_directedSlideSequence (hs.scalarize C)
    exact ⟨r.total, T, hT, r, rfl⟩
  obtain ⟨T, hT, r, hr⟩ := Nat.find_spec hex
  have hmin : ∀ T', Independent Gf T' →
      ∀ r' : Routing D (fun u v => C * w u v + 1) S T', r.total ≤ r'.total := by
    intro T' hT' r'
    rw [hr]
    exact Nat.find_min' hex ⟨T', hT', r', rfl⟩
  obtain ⟨c, n, hopt, hlen, _⟩ := reconstruct_lex_optimal Gf D w r hT hmin
  exact ⟨T, c, n, hopt, hlen⟩

end IndependentSetDiscovery.WeightedDirected
