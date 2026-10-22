import HigherDimLQGMetric.DGZ.NondegZeroGeom

/-!
# Lattice thickening of a zero set

At mesh `ρ`, select each lattice center whose open `2ρ` box meets the zero set,
then take the union of its open `2ρ` boxes. Each selected box meets the zero set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox roundLat abs_latPt_roundLat_sub_lt mem_obox_self)

variable {d : ℕ}

/-- The lattice center `z` is selected if it lies within sup-distance `2ρ`
of the zero set for the target sphere. -/
def nd_selectedCell (rGrid r : ℝ) (j : ℕ) (s : nd_Joint d rGrid)
    (z : Zd d) : Prop :=
  ∃ x ∈ nd_zeroSet r s,
    x ∈ obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)

def nd_thickening (rGrid r : ℝ) (j : ℕ) (s : nd_Joint d rGrid) : Set (Rd d) :=
  ⋃ z : Zd d, ⋃ (_hz : nd_selectedCell rGrid r j s z),
    obox (latPt (nd_gridRadius rGrid j) z) (2 * nd_gridRadius rGrid j)

theorem nd_isOpen_thickening (rGrid r : ℝ) (j : ℕ) (s : nd_Joint d rGrid) :
    IsOpen (nd_thickening rGrid r j s) := by
  unfold nd_thickening
  exact isOpen_iUnion fun z => isOpen_iUnion fun _ =>
    HigherDimLFPP.DGZ.isOpen_obox _ _

/-- A point within one mesh of a zero-set point lies in the thickening. -/
theorem nd_mem_thickening_of_near {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (r : ℝ) (j : ℕ) (s : nd_Joint d rGrid) {x y : Rd d}
    (hy : y ∈ nd_zeroSet r s)
    (hxy : x ∈ obox y (nd_gridRadius rGrid j)) :
    x ∈ nd_thickening rGrid r j s := by
  let ρ := nd_gridRadius rGrid j
  have hρ : 0 < ρ := nd_gridRadius_pos hrGrid j
  let z := roundLat ρ x
  have hx : x ∈ obox (latPt ρ z) (2 * ρ) := by
    intro i
    have hi := abs_latPt_roundLat_sub_lt hρ x i
    rw [abs_sub_comm] at hi
    linarith
  have hyz : y ∈ obox (latPt ρ z) (2 * ρ) := by
    intro i
    have h1 := abs_latPt_roundLat_sub_lt hρ x i
    have h2 := hxy i
    have htri : |y i - latPt ρ z i| ≤ |y i - x i| + |x i - latPt ρ z i| := by
      calc
        |y i - latPt ρ z i| = |(y i - x i) + (x i - latPt ρ z i)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm] at h1 h2
    linarith
  exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨⟨y, hy, hyz⟩, hx⟩⟩

theorem nd_zeroSet_subset_thickening {rGrid : ℝ} (hrGrid : 0 < rGrid)
    (r : ℝ) (j : ℕ) (s : nd_Joint d rGrid) :
    nd_zeroSet r s ⊆ nd_thickening rGrid r j s := by
  intro x hx
  apply nd_mem_thickening_of_near hrGrid r j s hx
  exact mem_obox_self x (nd_gridRadius_pos hrGrid j)

end HigherDimLQGMetric.DGZ
