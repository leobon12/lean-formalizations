import HigherDimLQGMetric.ConvField.SphereScaleAll
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Scaling of the convolution kernel and of the LGF convolution field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_convKernelEps_scale {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (x : Rd d) :
    convKernelEps κ (ε / ρ) x = ρ ^ d * convKernelEps κ ε (ρ • x) := by
  have harg : (ε / ρ)⁻¹ • x = ε⁻¹ • (ρ • x) := by
    rw [inv_div, smul_smul]
    congr 1
    field_simp
  have hpow : (ε / ρ) ^ (-(d : ℝ)) = ρ ^ d * ε ^ (-(d : ℝ)) := by
    rw [Real.div_rpow hε.le hρ.le, Real.rpow_neg hρ.le, Real.rpow_natCast]
    rw [div_eq_mul_inv, inv_inv]
    ring
  rw [convKernelEps, convKernelEps, harg, hpow]
  ring

theorem l2b_radial_integral_scale (hd : 2 ≤ d) {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ)
    (A B : ℝ → ℝ) (hAB : ∀ r : ℝ, 0 < r → A r = B (ρ * r)) :
    (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
      convKernelEps κ (ε / ρ) (r • e₁ d) * A r) =
    ∫ s in Ioi (0 : ℝ), s ^ (d - 1) *
      convKernelEps κ ε (s • e₁ d) * B s := by
  let G : ℝ → ℝ := fun s => s ^ (d - 1) *
    convKernelEps κ ε (s • e₁ d) * B s
  have hpoint (r : ℝ) (hr : 0 < r) :
      r ^ (d - 1) * convKernelEps κ (ε / ρ) (r • e₁ d) * A r =
        ρ * G (ρ * r) := by
    rw [l2b_convKernelEps_scale hε hρ, hAB r hr]
    dsimp [G]
    rw [smul_smul]
    have hp : (ρ * r) ^ (d - 1) = ρ ^ (d - 1) * r ^ (d - 1) := mul_pow ρ r _
    rw [hp]
    have he : d = (d - 1) + 1 := by omega
    have hpowρ : ρ ^ d = ρ ^ (d - 1) * ρ := by
      calc ρ ^ d = ρ ^ ((d - 1) + 1) := congrArg (ρ ^ ·) he
        _ = ρ ^ (d - 1) * ρ := pow_succ _ _
    rw [hpowρ]
    ring
  calc
    (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ (ε / ρ) (r • e₁ d) * A r) =
      ∫ r in Ioi (0 : ℝ), ρ * G (ρ * r) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact hpoint r hr
    _ = ρ * ∫ r in Ioi (0 : ℝ), G (ρ * r) := by rw [integral_const_mul]
    _ = ∫ s in Ioi (0 : ℝ), G s := by
      simpa only [smul_eq_mul, mul_zero] using
        (integral_comp_mul_left_Ioi' G 0 hρ)
    _ = _ := rfl

theorem l2b_ae_convMollify_scale (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ (ε / ρ) (affineComp ρ 0 (h ω)) z =
        convMollify κ ε (h ω) (ρ • z) := by
  have hh' : IsWholeSpaceLGF (fun ω => affineComp ρ 0 (h ω)) P := hh.affineComp hρ 0
  filter_upwards [l2b_ae_radial_wholeSpace d hd κ hκ P h hh,
    l2b_ae_radial_wholeSpace d hd κ hκ P
      (fun ω => affineComp ρ 0 (h ω)) hh',
    l2b_ae_sphereAvg_scale_all d hd P h hh hρ]
    with ω hrad hrad' hscale
  intro ε hε z
  rw [hrad' (ε / ρ) (div_pos hε hρ) z, hrad ε hε (ρ • z)]
  congr 1
  exact l2b_radial_integral_scale hd hε hρ
    (fun r => sphereAvg (affineComp ρ 0 (h ω)) r z)
    (fun s => sphereAvg (h ω) s (ρ • z)) (fun r hr => hscale r hr z)

end HigherDimLQGMetric
