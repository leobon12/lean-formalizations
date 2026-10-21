-- FROZEN_ANCHOR_PREFIX_BEGIN
import LQGMetric.Meas.Geod
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Statement.LQGMetric
import LQGMetric.Statement.GFF
import SmallGammaGeodesics.Geodesic.Provider

/-!
# Frozen theorem: `geodesic_ae_unique`

Anchor of the statement surface of the small-parameter LQG geodesics formalization (manifest
`SmallGammaGeodesics/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, G1, G11, G12, G14).
Source: `source/small-parameter-lqg-geodesics.pdf`, (1.3): the a.s. unique geodesic `P_γ` from 0 to 1 at constant metric speed. Non-vacuity of
the main statements: a.s. existence and uniqueness, and a measurable choice (ruling G11).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics
open LQGMetric

/-- **(1.3).** For every strong γ-LQG metric family and the normalized whole-plane GFF: for each
`γ ∈ (0,2)`, a.s. there is a unique constant-speed `D_h^γ`-geodesic from `0` to `1`; and there is a
family of measurable choices that are a.s. such geodesics. -/
theorem geodesic_ae_unique :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P),
    (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ∃! η, Blueprint.IsGeod01 (D γ (h ω)) 0 1 η) ∧
    ∃ η : ℝ → Ω → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact SmallGammaGeodesics.geodesic_ae_unique_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end SmallGammaGeodesics
-- FROZEN_ANCHOR_SUFFIX_END
