import SmallGammaGeodesics.Assembly.Reduction
import SmallGammaGeodesics.Assembly.Scalar
import SmallGammaGeodesics.Lower.Prop71
import SmallGammaGeodesics.CC.Master
import SmallGammaGeodesics.CC.Sigma0MC
import SmallGammaGeodesics.CC.MasterLE
import SmallGammaGeodesics.Upper.Lemma42Holds
import SmallGammaGeodesics.Upper.Main

/-!
# Provider: `SmallGammaGeodesics.Assembly/Deviation`

`implementation.module` of the frozen anchor `deviation_scale` (Theorem 1.1, (1.4)–(1.9); manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`). `deviation_scale_impl` has exactly the frozen statement.

Proof: the reduction to the coordinate space (`deviation_scale_of_internal`), the scalar consequences
(`devConcl_of_bounds`, §8) of the upper bounds (`upperBoundsXi_of_interfaces`, §5) and of the lower bound
(`lowerBound71_of_MC`, §7). The interface inputs are discharged: the one-sided conformal covariance by
`CC.masterCCLE_holds` (track CC), the Möbius export by `CC.mcInput_of_masterCC` (via
`CC.masterCC_of_masterCCLE`), and the probe coupling by `lemma42_holds`. This module must never import the
frozen anchors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics
open LQGMetric

/-- **Theorem 1.1** (the two-thirds deviation scale), (1.4)–(1.9): the frozen statement of
`deviation_scale`, proved. -/
theorem deviation_scale_impl :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    ∃ C γ₀ : ℝ, 0 < γ₀ ∧
      -- (1.4)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂P ≤ ENNReal.ofReal (C * γ ^ (2 / 3 : ℝ))) ∧
      -- (1.5)
      (∀ A : ℝ, 1 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | A * γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} ≤
          ENNReal.ofReal (C * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε)) ∧
      -- (1.6)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀, ∀ a ∈ Ioc (0 : ℝ) 1,
        P {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} ≤ ENNReal.ofReal (C * a ^ (3 / 5 : ℝ))) ∧
      -- (1.7)
      (∀ ε : ℝ, 0 < ε → ∃ a A : ℝ, 0 < a ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
          maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ A)} ≤ ENNReal.ofReal ε) ∧
      -- (1.8)
      (∀ r ∈ Ioo (0 : ℝ) (3 / 5), ∃ K : ℝ, ∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω) / γ ^ (2 / 3 : ℝ)) ^ (-r) ∂P ≤ ENNReal.ofReal K) ∧
      -- (1.9)
      (∀ ε : ℝ, 0 < ε → Tendsto (fun γ : ℝ => P {ω | ¬ (γ ^ (2 / 3 + ε) ≤ maxDev (η γ ω) ∧
          maxDev (η γ ω) ≤ γ ^ (2 / 3 - ε))}) (𝓝[>] 0) (𝓝 0)) :=
  deviation_scale_of_internal (fun G η₀ hm hη =>
    devConcl_of_bounds (fun γ _ _ => (hm γ).aemeasurable)
      (upperBoundsXi_of_interfaces G
        (fun γ h0 h2 => CC.masterCCLE_holds γ h0 h2 _ (G.hD γ h0 h2)) lemma42_holds η₀ hm hη)
      (lowerBound71_of_MC G.Dfam G.hD
        (fun γ h0 h2 =>
          CC.mcInput_of_masterCC (CC.masterCC_of_masterCCLE CC.masterCCLE_holds) h0 h2 (G.hD γ h0 h2))
        GaussianLQG.stdP G.h₀ G.normalized η₀ hη))

end SmallGammaGeodesics
