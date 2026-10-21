import SmallGammaGeodesics.Upper.ProbeInv
import SmallGammaGeodesics.Variance.FourKernel

/-!
# The displacement energy (5.5) (blueprint `cor:probe-energy`; BP2 detail D7; packet P-U2)

For `θ ≠ 0` with `|θ| ≤ ε_G ℓ_j`, the push-forward `μ_θ = ψ_*λ` of the uniform measure `λ` on
`[0,1]` under the inverse probe map `ψ = probeInv j a θ` is a regular probability measure with
`‖μ_θ − λ‖_G² ≤ C_G |θ|` (`energy_pushforward_probe`).

Proof (blueprint): `ψ` is Borel (`probeInv_spec`), so `ψ_*λ = pathMeasure (t ↦ ψ t)`
(`map_segMeasure_eq_pathMeasure`). The path `t ↦ ψ(t)` is continuous on `[0,1]` (`ψ` is holomorphic
on the open set `ϕ(S_j) ∋ t`), satisfies `|ψ(t) − t| ≤ C₀|θ| ≤ r := (C₀ + 1)|θ| ≤ ℓ_j ≤ 1` and
`|t − t'| ≤ (3/2)|ψ t − ψ t'|`; P-A4's `fourKernel_of_coLipschitz` with `K = 3/2`
(`max 1 (2K) = 3`) gives regularity and `‖μ_θ − λ‖_G² ≤ (7 + 16 log 5) r`.
So `ε_G = min{ε_ψ, 1/(C₀+1)}` and `C_G = (7 + 16 log 5)(C₀ + 1)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG

/-- **Corollary `cor:probe-energy`** ((5.5); BP2 D7): the displacement energy of the probe. -/
theorem energy_pushforward_probe : ∃ εG CG, 0 < εG ∧ 0 ≤ CG ∧ ∀ (j : ℕ) (a θ : ℝ), θ ≠ 0 →
    |θ| ≤ εG * ell j →
    IsProbabilityMeasure ((segMeasure 0 1).map (probeInv j a θ)) ∧
    IsRegular ((segMeasure 0 1).map (probeInv j a θ)) ∧
    energyDistSq ((segMeasure 0 1).map (probeInv j a θ)) (segMeasure 0 1) ≤ CG * |θ| := by
  obtain ⟨εψ, C₀, hεψ, hC₀, hspec⟩ := probeInv_spec
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  refine ⟨min εψ (1 / (C₀ + 1)), (7 + 16 * Real.log 5) * (C₀ + 1), lt_min hεψ (by positivity),
    by positivity, fun j a θ hθ0 hθ => ?_⟩
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  have hθψ : |θ| ≤ εψ * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)
  have hθ1 : |θ| ≤ 1 / (C₀ + 1) * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le)
  obtain ⟨-, hB, hC, hdiff, hmeas, hlow⟩ := hspec j a θ hθψ
  rw [map_segMeasure_eq_pathMeasure hmeas]
  -- the displacement scale `r = (C₀ + 1)|θ|`
  have hθpos : 0 < |θ| := abs_pos.2 hθ0
  have hr : 0 < (C₀ + 1) * |θ| := by positivity
  have hr1 : (C₀ + 1) * |θ| ≤ 1 := by
    have h1 : (C₀ + 1) * |θ| ≤ (C₀ + 1) * (1 / (C₀ + 1) * ell j) :=
      mul_le_mul_of_nonneg_left hθ1 (by positivity)
    have h2 : (C₀ + 1) * (1 / (C₀ + 1) * ell j) = ell j := by field_simp
    linarith
  -- the path `t ↦ ψ t` is continuous on `[0,1]`
  have hreal : ∀ t : ℝ, |((t : ℂ)).im| ≤ ell j / 2 := fun t => by
    rw [Complex.ofReal_im, abs_zero]; positivity
  have hd : DifferentiableOn ℂ (probeMap j a θ) (probeStrip j) := fun z _ =>
    (hasDerivAt_probeMap j a θ z).differentiableAt.differentiableWithinAt
  have hi : InjOn (probeMap j a θ) (probeStrip j) := by
    intro z hz w hw hzw
    rw [← hC z hz, ← hC w hw, hzw]
  have hopen : IsOpen (probeMap j a θ '' probeStrip j) :=
    CC.isOpen_image_conf (isOpen_probeStrip j) hd hi
  have hcont : ContinuousOn (fun t : ℝ => probeInv j a θ t) (Icc 0 1) := by
    intro t _
    obtain ⟨hm, hφ, -⟩ := hB t (hreal t)
    have hmem : (t : ℂ) ∈ probeMap j a θ '' probeStrip j := ⟨_, hm, hφ⟩
    have hca : ContinuousAt (probeInv j a θ) (t : ℂ) :=
      hdiff.continuousOn.continuousAt (hopen.mem_nhds hmem)
    exact (hca.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖probeInv j a θ t - t‖ ≤ (C₀ + 1) * |θ| := fun t _ => by
    have := (hB t (hreal t)).2.2
    nlinarith [abs_nonneg θ]
  obtain ⟨hreg, hE⟩ := fourKernel_of_coLipschitz (fun t => probeInv j a θ t) ((C₀ + 1) * |θ|)
    (3 / 2) hcont hr hr1 (by norm_num) hdisp hlow
  refine ⟨inferInstance, hreg, hE.trans (le_of_eq ?_)⟩
  rw [show max (1 : ℝ) (2 * (3 / 2)) = 3 by norm_num]
  ring

end SmallGammaGeodesics
