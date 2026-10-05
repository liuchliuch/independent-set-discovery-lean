import IndependentSetDiscovery.MeasuredDiscovery

open IndependentSetDiscovery
open IndependentSetDiscovery.ShortestPaths

namespace SmokeMeasuredDiscovery

def pathThree : MatrixGraph 3 where
  matrix := #v[#v[false, true, false], #v[true, false, true], #v[false, true, false]]
  symmetric := by decide
  diagonal := by decide

def triangle : MatrixGraph 3 where
  matrix := #v[#v[false, true, true], #v[true, false, true], #v[true, true, false]]
  symmetric := by decide
  diagonal := by decide

def emptyGraph : MatrixGraph 0 where
  matrix := #v[]
  symmetric := by intro u; exact Fin.elim0 u
  diagonal := by intro u; exact Fin.elim0 u

theorem small_biclique_free {n : ℕ} (a : MatrixGraph n) (hn : n < 4) :
    BicliqueFree a.graph 2 2 := by
  rintro ⟨X, Y, hX, hY, hd, _⟩
  have hu : (X ∪ Y).card = 4 := by rw [Finset.card_union_of_disjoint hd, hX, hY]
  have hb := Finset.card_le_univ (X ∪ Y)
  simp only [Fintype.card_fin, hu] at hb
  omega

-- Expected target [0,2], one move (1,2), and a finite actual operation count.
#eval let result := (MeasuredDiscovery.solveBinary pathThree {0,1} 2 (by decide)
    (small_biclique_free pathThree (by decide)))
  (result.1.map (fun out => (out.target.sort (· ≤ ·), out.moves)), result.2)

-- Expected true: no independent two-set exists in a triangle.
#eval (MeasuredDiscovery.solveBinary triangle {0,1} 2 (by decide)
  (small_biclique_free triangle (by decide))).1.isNone

-- Expected some (0,0): zero vertices/labels are handled by actual computation.
#eval (MeasuredDiscovery.solveBinary emptyGraph ∅ 2 (by decide)
  (small_biclique_free emptyGraph (by decide))).1.map (fun out => (out.target.card, out.moves.length))

end SmokeMeasuredDiscovery
