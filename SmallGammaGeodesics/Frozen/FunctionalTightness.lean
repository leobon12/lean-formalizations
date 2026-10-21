-- FROZEN_ANCHOR_PREFIX_BEGIN
import SmallGammaGeodesics.Frozen.RescaledPath
import SmallGammaGeodesics.Frozen.HorizDev
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Statement.LQGMetric
import LQGMetric.Statement.GFF
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SmallGammaGeodesics.Assembly.Tightness

/-!
# Frozen theorem: `functional_tightness`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, Theorem 1.2, (1.10)–(1.11): tightness in `C([0,1], ℝ²)` as γ ↓ 0 over the continuum (ruling
G12), and the horizontal component tends to 0 in probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics
open LQGMetric

/-- **Theorem 1.2** (functional tightness). For any family `η` that is a.s. the constant-speed
geodesic from 0 to 1: each `X_γ` is a.e.-measurable; for every `ε > 0` there is a compact set of paths
that `X_γ` leaves with probability at most `ε` for all small `γ`; and (1.11) holds. -/
theorem functional_tightness :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    (∀ γ, 0 < γ → γ < 2 →
      AEMeasurable (fun ω => rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω)) P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      P {ω | rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε) ∧
    TendstoInMeasure P (fun γ ω => horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) (𝓝[>] 0) (fun _ => 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact SmallGammaGeodesics.functional_tightness_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end SmallGammaGeodesics
-- FROZEN_ANCHOR_SUFFIX_END
