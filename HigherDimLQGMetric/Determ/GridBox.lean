import HigherDimLQGMetric.Determ.GridCI
import HigherDimLFPP.Upper.RecordCount

/-!
# A finite set of translated cubes meeting a ball

The record-counting library supplies the exact `O((R/ε)^d)` finite index set.
No bound on the translation parameter is needed because the ball centre is
translated with the grid.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

def determShiftPt (ε : ℝ) (θ : Fin d → ℝ) : Rd d :=
  WithLp.toLp 2 fun i => ε * θ i

def determIdx (ε : ℝ) (θ : Fin d → ℝ) (x : Rd d) : Fin d → ℤ :=
  HigherDimLFPP.Upper.cubeIdx ε (x - determShiftPt ε θ)

def determBox (ε R : ℝ) (θ : Fin d → ℝ) : Finset (Fin d → ℤ) :=
  HigherDimLFPP.Upper.cubeBox ε (-determShiftPt ε θ) R

/-- Every point off the grid belongs to its open indexed cell. -/
theorem determ_mem_cube_of_not_grid {ε : ℝ} (hε : 0 < ε)
    (θ : Fin d → ℝ) {x : Rd d} (hx : x ∉ determGrid ε θ) :
    x ∈ determCube ε θ (determIdx ε θ x) := by
  have hlat := HigherDimLFPP.Upper.mem_latCube_cubeIdx hε
    (x - determShiftPt ε θ)
  intro i
  have hi := hlat i
  dsimp [determIdx, determShiftPt, HigherDimLFPP.Upper.cubeIdx] at hi ⊢
  have hlo : ε * ((⌊(x i - ε * θ i) / ε⌋ : ℤ) + θ i) ≤ x i := by
    nlinarith [hi.1]
  have hne : x i ≠ ε * ((⌊(x i - ε * θ i) / ε⌋ : ℤ) + θ i) :=
    fun he => hx ⟨i, ⌊(x i - ε * θ i) / ε⌋, he⟩
  constructor
  · exact lt_of_le_of_ne hlo hne.symm
  · nlinarith [hi.2]

/-- A cell containing a point of `B̄_R(0)` belongs to the finite box. -/
theorem determ_idx_mem_box {ε R : ℝ} (hε : 0 < ε)
    (θ : Fin d → ℝ) {x : Rd d} (hx : ‖x‖ ≤ R) :
    determIdx ε θ x ∈ determBox ε R θ := by
  have he : (x - determShiftPt ε θ) - (-determShiftPt ε θ) = x := by abel
  have hn : ‖(x - determShiftPt ε θ) - (-determShiftPt ε θ)‖ ≤ R := by
    simpa only [he] using hx
  exact HigherDimLFPP.Upper.cubeIdx_mem_cubeBox hε hn

/-- The number of cells needed for `B̄_R(0)` has order `(R/ε)^d`. -/
theorem determ_card_box_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (θ : Fin d → ℝ) :
    ((determBox ε R θ).card : ℝ) ≤ (2 * R / ε + 2) ^ d :=
  HigherDimLFPP.Upper.card_cubeBox_le hε (-determShiftPt ε θ) hR

/-- The finite-box observations have a conditional product law. -/
theorem determ_box_condDistrib_pi {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Nonempty (ContMetric d)]
    {h : Ω → DistRd d} {D : Ω → ContMetric d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) (θ : Fin d → ℝ) :
    ∀ᵐ g ∂P.map h,
      (condDistrib D h P g).map
          (fun D (i : determBox ε R θ) => determ_enc (determCube ε θ i.1) D) =
        Measure.pi fun i : determBox ε R θ =>
          (condDistrib D h P g).map (determ_enc (determCube ε θ i.1)) :=
  determ_grid_condDistrib_pi hh hloc hε θ (determBox ε R θ)

end HigherDimLQGMetric
