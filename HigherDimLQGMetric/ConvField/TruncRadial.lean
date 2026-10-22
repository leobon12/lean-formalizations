import HigherDimLQGMetric.ConvField.RadialPair

/-! Radial formula for each compact truncation of the convolution kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_convTrunc_radial_about (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ) (z : Rd d) (n : ℕ) :
    ∀ x : Rd d, convTrunc κ ε z n x =
      convTrunc κ ε z n (z + ‖x - z‖ • e₁ d) := by
  intro x
  apply l2b_convTrunc_radial hd hκ ε z n
  rw [add_sub_cancel_left, norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d),
    mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem l2b_convTrunc_axis (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε r : ℝ) (z : Rd d) (n : ℕ) :
    convTrunc κ ε z n (z + r • e₁ d) =
      convKernelEps κ ε (r • e₁ d) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d)) := by
  rw [l2b_convTrunc_apply hd hκ]
  simp only [add_sub_cancel_left, sub_add_cancel_left]
  congr 1
  apply l2b_convKernelEps_radial
  simp only [norm_neg]

theorem l2b_ae_convTrunc_radial (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (ε : ℝ) (z : Rd d) (n : ℕ) :
    ∀ᵐ ω ∂P, h ω (convTrunc κ ε z n) =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          (convKernelEps κ ε (r • e₁ d) *
            radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))) *
          sphereAvg (h ω) r z := by
  filter_upwards [l2b_ae_radial_pairing hd hh (convTrunc κ ε z n) z
    (l2b_convTrunc_radial_about hd hκ ε z n)] with ω hω
  rw [hω]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [l2b_convTrunc_axis hd hκ]

end HigherDimLQGMetric
