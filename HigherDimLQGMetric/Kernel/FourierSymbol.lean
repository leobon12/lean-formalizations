import HigherDimLQGMetric.Kernel.FourierFubini
import HigherDimLQGMetric.Kernel.OneVarSymbol
import HigherDimLQGMetric.Kernel.ConvKernelSymbol

/-!
# Radial scale integrals and the convolution symbol

The frequency scale integral is a radial tail.  At scale zero Plancherel and
polar coordinates identify its total mass with one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory FourierTransform Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

def kernelRadialMass (κ : Rd d → ℝ) (ρ : ℝ) : ℝ :=
  ∫ s in Ioi ρ, s ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)‖ ^ 2

theorem symbolSq_eq_sphereConst_mul_radialMass
    (hd : 0 < d) (κ : Rd d → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    symbolSq κ ρ =
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        kernelRadialMass κ ρ := by
  rw [symbolSq, kernelRadialMass]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs : 0 < s := lt_of_le_of_lt hρ hs
  have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ d)]
  rw [← hc, Real.rpow_natCast]

theorem radialMass_zero_eq_inv_sphereConst
    (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    kernelRadialMass κ 0 =
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ := by
  have hs := symbolSq_eq_sphereConst_mul_radialMass hd κ 0 le_rfl
  rw [symbolSq_zero hd hκ] at hs
  exact eq_inv_of_mul_eq_one_right hs.symm

theorem integral_scaleSpectral_eq_radialMass
    (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 ≤ ε) (ζ : Rd d) (hζ : ζ ≠ 0) :
    (∫ t in Ioi ε, t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) =
      ‖ζ‖ ^ (-(d : ℝ)) * kernelRadialMass κ (ε * ‖ζ‖) := by
  let r : ℝ := ‖ζ‖
  have hr : 0 < r := norm_pos_iff.mpr hζ
  let g : ℝ → ℝ := fun s => s ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e₁ d)‖ ^ 2
  have hp : ∀ t ∈ Ioi ε,
      t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 =
      r ^ (-((d : ℝ) - 1)) * g (r * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hε ht
    have hnorm : ‖t • ζ‖ = ‖(r * t) • e₁ d‖ := by
      rw [norm_smul, norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one,
        Real.norm_eq_abs, abs_of_pos ht0, Real.norm_eq_abs,
        abs_of_pos (mul_pos hr ht0)]
      dsimp [r]
      ring
    rw [fourier_kernel_eq_of_norm_eq hκ.radial hnorm]
    dsimp [g]
    rw [Real.mul_rpow hr.le ht0.le, Real.rpow_neg (le_of_lt hr)]
    have hne : r ^ ((d : ℝ) - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp
  calc
    (∫ t in Ioi ε, t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) =
        ∫ t in Ioi ε, r ^ (-((d : ℝ) - 1)) * g (r * t) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _ = r ^ (-((d : ℝ) - 1)) * (∫ t in Ioi ε, g (r * t)) := by
      rw [integral_const_mul]
    _ = r ^ (-(d : ℝ)) * ∫ s in Ioi (r * ε), g s := by
      rw [integral_comp_mul_left_Ioi g ε hr]
      simp only [smul_eq_mul]
      rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hr]
      congr 1
      ring_nf
    _ = _ := by
      unfold kernelRadialMass
      rw [mul_comm r ε]

/-- The scale tail is the squared Fourier symbol of the convolution kernel. -/
theorem integral_scaleSpectral_eq_kernelSymbol
    (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 ≤ ε) (ζ : Rd d) (hζ : ζ ≠ 0) :
    (∫ t in Ioi ε, t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) =
      ‖ζ‖ ^ (-(d : ℝ)) *
        (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ *
        (kernelSymbol κ (ε • ζ)) ^ 2 := by
  rw [integral_scaleSpectral_eq_radialMass hd hκ hε ζ hζ]
  have hρ : 0 ≤ ε * ‖ζ‖ := mul_nonneg hε (norm_nonneg _)
  have hs := symbolSq_eq_sphereConst_mul_radialMass hd κ (ε * ‖ζ‖) hρ
  have hconst := sphereConst_pos hd
  have hm : kernelRadialMass κ (ε * ‖ζ‖) =
      (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ *
        symbolSq κ (ε * ‖ζ‖) := by
    rw [hs]
    field_simp
  rw [hm, ← Real.sq_sqrt (le_of_lt (symbolSq_pos hd hκ _))]
  rw [kernelSymbol_eq_sqrt_symbolSq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε]
  ring

/-- The covariance above `ε` has the Fourier multiplier `|ζ|⁻ᵈ |K̂(εζ)|²`. -/
theorem scaleCov_eq_kernelSymbol_fourier
    (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hp : HigherDimLFPP.IsPairable κ (Ioi ε) μ ν)
    (hp' : HigherDimLFPP.IsPairable κ (Ioi ε) μ' ν') :
    ((HigherDimLFPP.scaleCov κ (Ioi ε) μ ν μ' ν' : ℝ) : ℂ) =
      ∫ ζ : Rd d,
        ((‖ζ‖ ^ (-(d : ℝ)) *
          (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ *
          (kernelSymbol κ (ε • ζ)) ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ζ) - conj (measureFourier ν ζ)) *
          (measureFourier μ' ζ - measureFourier ν' ζ) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [scaleCov_eq_fourier_swapped hκ measurableSet_Ioi
    (fun _ ht => lt_of_le_of_lt hε ht) μ ν μ' ν' hp hp']
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : Rd d)] with ζ hζ
  dsimp [scaleSpectralCross]
  rw [integral_mul_const, integral_mul_const, integral_complex_ofReal,
    integral_scaleSpectral_eq_kernelSymbol hd hκ hε ζ hζ]

theorem logCov_eq_universal_fourier
    (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hmass : μ.real univ = ν.real univ)
    (hmass' : μ'.real univ = ν'.real univ)
    (hlog : HigherDimLFPP.LogPairable μ ν μ' ν') :
    ((HigherDimLFPP.logCov μ ν μ' ν' : ℝ) : ℂ) =
      ∫ ζ : Rd d,
        ((‖ζ‖ ^ (-(d : ℝ)) *
          (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
          (conj (measureFourier μ ζ) - conj (measureFourier ν ζ)) *
          (measureFourier μ' ζ - measureFourier ν' ζ) := by
  obtain ⟨hp, hp', hcov⟩ := HigherDimLFPP.scaleCov_eq_logCov hκ hmass hmass' hlog
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [← hcov]
  have h := scaleCov_eq_kernelSymbol_fourier hd hκ (ε := 0) le_rfl
    μ ν μ' ν' hp hp'
  rw [h]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : Rd d)] with ζ _
  rw [zero_smul, kernelSymbol_zero hd hκ, one_pow, mul_one]

end HigherDimLQGMetric
