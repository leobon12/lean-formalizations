import HigherDimLQGMetric.LfppTight.SphereMeanGaussian

/-! Chebyshev reduces the A7(2) scalar tail to a uniform variance estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_uniform_sphereMean_tail_of_variance {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {C : ℝ} (hC : 0 ≤ C)
    (hVar : ∀ ε ∈ Ioo (0 : ℝ) 1,
      Var[fun ω => l6a_convSphereMean κ ε (h ω); P] ≤ C)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | L < |l6a_convSphereMean κ ε (h ω)|} ≤ ENNReal.ofReal θ := by
  let L : ℝ := C / θ + 1
  have hL1 : 1 ≤ L := by
    dsimp [L]
    have hdiv := div_nonneg hC hθ.le
    linarith
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hCL : C / L ^ 2 ≤ θ := by
    have hCL1 : C ≤ θ * L := by
      dsimp [L]
      rw [mul_add, mul_div_cancel₀ C hθ.ne']
      linarith
    have hL2 : L ≤ L ^ 2 := by nlinarith
    apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    nlinarith [mul_le_mul_of_nonneg_left hL2 hθ.le]
  refine ⟨L, hL, ?_⟩
  intro ε hε
  let X : Ω → ℝ := fun ω => l6a_convSphereMean κ ε (h ω)
  obtain ⟨hG, hmean⟩ := l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε.1
  have hcheb := meas_ge_le_variance_div_sq (hG.memLp (by simp : (2 : ℝ≥0∞) ≠ ⊤)) hL
  change P {ω | L ≤ |X ω - ∫ ω, X ω ∂P|} ≤
    ENNReal.ofReal (Var[X; P] / L ^ 2) at hcheb
  rw [hmean] at hcheb
  simp only [sub_zero] at hcheb
  calc
    P {ω | L < |X ω|} ≤ P {ω | L ≤ |X ω|} :=
      measure_mono fun ω hw => by
        change L < |X ω| at hw
        change L ≤ |X ω|
        exact hw.le
    _ ≤ ENNReal.ofReal (Var[X; P] / L ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (C / L ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hVar ε hε) (sq_nonneg L))
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hCL

end HigherDimLQGMetric
