-- FROZEN_ANCHOR_PREFIX_BEGIN
import SmallGammaGeodesics.Frozen.MaxDev
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Statement.LQGMetric
import LQGMetric.Statement.GFF
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import SmallGammaGeodesics.Assembly.Deviation

/-!
# Frozen theorem: `deviation_scale`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, Theorem 1.1, (1.4)–(1.9), with no hypotheses beyond the definitions of the objects (ruling G1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics
open LQGMetric

/-- **Theorem 1.1** (the two-thirds deviation scale), (1.4)–(1.9). `M_γ = maxDev (η γ ω)` for any
family `η` that is a.s. the constant-speed geodesic from 0 to 1. -/
theorem deviation_scale :
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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact SmallGammaGeodesics.deviation_scale_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end SmallGammaGeodesics
-- FROZEN_ANCHOR_SUFFIX_END
