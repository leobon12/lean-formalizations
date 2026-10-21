import SmallGammaGeodesics.Geodesic.Basic

/-!
# Provider of the frozen anchor `geodesic_ae_unique` (source (1.3))

`implementation.module` of `SmallGammaGeodesics/Frozen/GeodesicAeUnique.lean` (manifest
`frozen-anchors.json`). It must not import the anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace SmallGammaGeodesics

open LQGMetric

/-- **(1.3)**: for each `γ ∈ (0,2)`, a.s. the constant-speed geodesic from `0` to `1` exists and is
unique, and there is a family of measurable choices of it. -/
theorem geodesic_ae_unique_impl :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P),
    (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ∃! η, Blueprint.IsGeod01 (D γ (h ω)) 0 1 η) ∧
    ∃ η : ℝ → Ω → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω) := by
  intro D hD Ω _ P _ h hh
  refine ⟨fun γ hγ hγ2 => ae_existsUnique_geod01 hγ hγ2 (hD γ hγ hγ2) P h hh.1 0 1, ?_⟩
  have hex : ∀ γ : ℝ, ∃ η : Ω → C(unitInterval, ℂ), Measurable η ∧
      (0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η ω)) := by
    intro γ
    by_cases hγ : 0 < γ ∧ γ < 2
    · obtain ⟨η, hηm, hη⟩ := exists_measurable_geod01 hγ.1 hγ.2 (hD γ hγ.1 hγ.2) P h hh.1 0 1
      exact ⟨η, hηm, fun _ _ => hη⟩
    · exact ⟨fun _ => ContinuousMap.const _ 0, measurable_const,
        fun h1 h2 => absurd ⟨h1, h2⟩ hγ⟩
  choose η hηm hη using hex
  exact ⟨η, hηm, hη⟩

end SmallGammaGeodesics
