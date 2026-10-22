import HigherDimLQGMetric.LfppTight.CoupledHolder
import HigherDimLQGMetric.LfppTight.CenteredWN
import HigherDimLQGMetric.LfppTight.CoupledVec

/-! Uniform finite-band scalar tails for the coupled comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_uniform_sphereBand_tail_at {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | M < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|} ≤
        ENNReal.ofReal θ := by
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_sphereBand_tail hd hκ P W hW
  let M : ℝ := C / θ + 1
  have hM1 : 1 ≤ M := by
    dsimp [M]
    have hdiv := div_nonneg hC0 hθ.le
    linarith
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hCM : C / M ^ 2 ≤ θ := by
    have hCM1 : C ≤ θ * M := by
      dsimp [M]
      rw [mul_add, mul_div_cancel₀ C hθ.ne']
      linarith
    have hM2 : M ≤ M ^ 2 := by nlinarith
    apply (div_le_iff₀ (sq_pos_of_pos hM0)).2
    nlinarith [mul_le_mul_of_nonneg_left hM2 hθ.le]
  refine ⟨M, hM0, ?_⟩
  intro ε hε
  calc
    P {ω | M < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|} ≤
        P {ω | M ≤ |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|} :=
      measure_mono fun _ω hω => by
        change M < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) _ω| at hω
        exact hω.le
    _ ≤ ENNReal.ofReal (C / M ^ 2) := hC ε hε M hM0
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hCM

end HigherDimLQGMetric
