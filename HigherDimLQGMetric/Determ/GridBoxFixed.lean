import HigherDimLQGMetric.Determ.GridProductAE

/-!
# One finite index set for all shifts in the unit cube

The half-open unit cube is a probability space for translations. For all its
shifts, a closed ball meets only the cubes in one fixed `cubeBox`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

def determUnitShift (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi univ fun _ => Ico (0 : ℝ) 1

def determShiftLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  (volume : Measure (Fin d → ℝ)).restrict (determUnitShift d)

theorem determ_volume_unitShift (d : ℕ) :
    (volume : Measure (Fin d → ℝ)) (determUnitShift d) = 1 := by
  rw [determUnitShift, Real.volume_pi_Ico]
  simp

instance determShiftLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (determShiftLaw d) := by
  apply IsProbabilityMeasure.mk
  rw [determShiftLaw, Measure.restrict_apply_univ, determ_volume_unitShift]

theorem determ_shift_norm_le {ε : ℝ} (hε : 0 < ε)
    {θ : Fin d → ℝ} (hθ : θ ∈ determUnitShift d) :
    ‖determShiftPt ε θ‖ ≤ Real.sqrt d * ε := by
  have hz : determShiftPt ε θ ∈
      HigherDimLFPP.Upper.latCube ε (fun _ : Fin d => 0) := by
    intro i
    have hi := hθ i (mem_univ i)
    simp only [determShiftPt, PiLp.toLp_apply, Int.cast_zero,
      zero_mul, zero_add, one_mul] at ⊢
    constructor <;> nlinarith [hi.1, hi.2]
  have h := HigherDimLFPP.Upper.norm_sub_corner_le hε hz
  have hcorner : HigherDimLFPP.Upper.corner ε (fun _ : Fin d => 0) = 0 := by
    ext i
    simp [HigherDimLFPP.Upper.corner]
  simpa only [hcorner, sub_zero] using h

def determFixedBox (ε R : ℝ) : Finset (Fin d → ℤ) :=
  HigherDimLFPP.Upper.cubeBox ε 0 (R + Real.sqrt d * ε)

/-- Every cell containing a point of the ball belongs to the fixed box. -/
theorem determ_idx_mem_fixedBox {ε R : ℝ} (hε : 0 < ε)
    {θ : Fin d → ℝ} (hθ : θ ∈ determUnitShift d)
    {x : Rd d} (hx : ‖x‖ ≤ R) :
    determIdx ε θ x ∈ determFixedBox ε R := by
  have hnorm : ‖x - determShiftPt ε θ‖ ≤ R + Real.sqrt d * ε := by
    calc ‖x - determShiftPt ε θ‖ ≤ ‖x‖ + ‖determShiftPt ε θ‖ := norm_sub_le _ _
      _ ≤ R + Real.sqrt d * ε := add_le_add hx (determ_shift_norm_le hε hθ)
  exact HigherDimLFPP.Upper.cubeIdx_mem_cubeBox hε (by simpa only [sub_zero] using hnorm)

theorem determ_card_fixedBox_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ((determFixedBox (d := d) ε R).card : ℝ) ≤
      (2 * (R + Real.sqrt d * ε) / ε + 2) ^ d :=
  HigherDimLFPP.Upper.card_cubeBox_le hε 0
    (add_nonneg hR (mul_nonneg (Real.sqrt_nonneg _) hε.le))

end HigherDimLQGMetric
