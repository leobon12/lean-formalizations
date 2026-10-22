import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.ConvField.RadialPair
import HigherDimLQGMetric.Kernel.ConvKernelMain

/-!
# The compact radial truncation

The radial pairing of `truncTest` is an instance of the general compact radial
pairing proved for the convolution field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2c_truncTest_apply (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z w : Rd d) :
    truncTest κ ε z w = convKernelEps κ ε (z - w) *
      radBump (Real.sqrt ε / 2) (Real.sqrt ε) (z - w) := by
  have hK := convKernel_contDiff (by omega : 0 < d) hκ
  simp only [truncTest, dite_eq_left (And.intro hK hε)]
  rfl

theorem l2c_radBump_eq_one {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : Rd d} (hx : ‖x‖ ≤ a) : radBump a b x = 1 := by
  have hR : 1 < b / a := (one_lt_div ha).2 hab
  change (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun
    (b / a) (a⁻¹ • x) = 1
  apply (ContDiffBumpBase.ofInnerProductSpace (Rd d)).eq_one _ hR
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  exact (inv_mul_le_iff₀ ha).2 (by simpa using hx)

theorem l2c_radBump_mem_Icc (a b : ℝ) (x : Rd d) :
    radBump a b x ∈ Icc (0 : ℝ) 1 := by
  exact (ContDiffBumpBase.ofInnerProductSpace (Rd d)).mem_Icc _ _

theorem l2c_radBump_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : Rd d} (hx : b ≤ ‖x‖) : radBump a b x = 0 := by
  have hba : 0 < b / a - 1 := sub_pos.2 ((one_lt_div ha).2 hab)
  have hx' : b / a ≤ ‖a⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hx ha.le
  simp only [radBump, ContDiffBumpBase.ofInnerProductSpace]
  exact Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le)

theorem l2c_truncTest_radial_about (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) :
    ∀ x : Rd d, truncTest κ ε z x =
      truncTest κ ε z (z + ‖x - z‖ • e₁ d) := by
  intro x
  rw [l2c_truncTest_apply hd hκ hε, l2c_truncTest_apply hd hκ hε]
  have hn : ‖z - x‖ = ‖z - (z + ‖x - z‖ • e₁ d)‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul,
      HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_sub_rev _ _
  rw [l2b_convKernelEps_radial ε hn, radBump_radial _ _ hn]

theorem l2c_truncTest_axis (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) (r : ℝ) :
    truncTest κ ε z (z + r • e₁ d) =
      convKernelEps κ ε (r • e₁ d) *
        radBump (Real.sqrt ε / 2) (Real.sqrt ε) (r • e₁ d) := by
  rw [l2c_truncTest_apply hd hκ hε]
  simp only [sub_add_cancel_left]
  congr 1
  · apply l2b_convKernelEps_radial
    simp only [norm_neg]
  · apply radBump_radial
    simp only [norm_neg]

theorem l2c_ae_trunc_radial (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    ∀ᵐ ω ∂P, truncMollify κ ε (h ω) z =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          (convKernelEps κ ε (r • e₁ d) *
            radBump (Real.sqrt ε / 2) (Real.sqrt ε) (r • e₁ d)) *
          sphereAvg (h ω) r z := by
  filter_upwards [l2b_ae_radial_pairing hd hh (truncTest κ ε z) z
    (l2c_truncTest_radial_about hd hκ hε z)] with ω hω
  rw [truncMollify, hω]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [l2c_truncTest_axis hd hκ hε]

end HigherDimLQGMetric
