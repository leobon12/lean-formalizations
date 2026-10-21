import SmallGammaGeodesics.Assembly.Transfer
import LQGMetric.Papers.GM.S1.FieldAux

/-!
# Reduction of the frozen theorems to internal statements on the coordinate space (packet F1)

`deviation_scale_of_internal` and `functional_tightness_of_internal` derive the frozen Theorems 1.1
and 1.2, for every strong γ-LQG metric family and every realization of the normalized whole-plane
GFF, from the corresponding statements for a canonical family on GaussianLQG's coordinate space
(`GSetup`) with a measurable family of a.s. geodesics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric GaussianLQG

/-- On the coordinate space, the canonical family admits a measurable family of a.s. constant-speed
geodesics from `0` to `1`. -/
theorem GSetup.exists_geodFamily (G : GSetup) :
    ∃ η₀ : ℝ → Coord → C(unitInterval, ℂ), (∀ γ, Measurable (η₀ γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, Blueprint.IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η₀ γ ω) := by
  have hex : ∀ γ : ℝ, ∃ η : Coord → C(unitInterval, ℂ), Measurable η ∧
      (0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, Blueprint.IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) := by
    intro γ
    by_cases hγ : 0 < γ ∧ γ < 2
    · obtain ⟨η, hηm, hη⟩ := exists_measurable_geod01 hγ.1 hγ.2 (G.hD γ hγ.1 hγ.2).1 stdP G.h₀
        G.normalized.1 0 1
      exact ⟨η, hηm, fun _ _ => hη⟩
    · exact ⟨fun _ => ContinuousMap.const _ 0, measurable_const,
        fun h1 h2 => absurd ⟨h1, h2⟩ hγ⟩
  choose η hηm hη using hex
  exact ⟨η, hηm, hη⟩

/-- Common reduction step: a strong-family geodesic on any realization has, for each `γ`, the law
of a canonical-family geodesic on the coordinate space. -/
theorem exists_coord_geodFamily_map_eq (D : ℝ → DistC → ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) (η : ℝ → Ω → C(unitInterval, ℂ))
    (hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)) :
    ∃ (G : GSetup) (η₀ : ℝ → Coord → C(unitInterval, ℂ)), (∀ γ, Measurable (η₀ γ)) ∧
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, Blueprint.IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η₀ γ ω)) ∧
      (∀ γ, 0 < γ → γ < 2 → AEMeasurable (η γ) P) ∧
      ∀ γ, 0 < γ → γ < 2 → P.map (η γ) = stdP.map (η₀ γ) := by
  obtain ⟨D', hD', hequiv⟩ := exists_canonical_family D hD
  obtain ⟨G, rfl⟩ := GSetup.exists_of D' hD'
  obtain ⟨η₀, hη₀m, hη₀⟩ := G.exists_geodFamily
  have hη' : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (G.Dfam γ (h ω)) 0 1 (η γ ω) := by
    intro γ h0 h2
    filter_upwards [hη γ h0 h2, hequiv γ h0 h2 P h (GM.isGFFPlusCont_of_normalized hh)]
      with ω h1 h2'
    exact (h2' 0 1 (η γ ω)).1 h1
  refine ⟨G, η₀, hη₀m, hη₀, fun γ h0 h2 => ?_, fun γ h0 h2 => ?_⟩
  · exact aemeasurable_of_ae_geod01 h0 h2 (G.hD γ h0 h2).1 P h hh.1 (hη' γ h0 h2)
  · exact map_geod_eq h0 h2 (G.hD γ h0 h2).1 hh G.normalized (hη' γ h0 h2) (hη₀ γ h0 h2)

/-- **Reduction of Theorem 1.1** to the coordinate space. -/
theorem deviation_scale_of_internal
    (hint : ∀ (G : GSetup) (η₀ : ℝ → Coord → C(unitInterval, ℂ)), (∀ γ, Measurable (η₀ γ)) →
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, Blueprint.IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η₀ γ ω)) →
      DevConcl stdP η₀) :
    ∀ (D : ℝ → DistC → ContMetric) (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    DevConcl P η := by
  intro D hD Ω _ P _ h hh η hη
  obtain ⟨G, η₀, hη₀m, hη₀, hηm, hmap⟩ := exists_coord_geodFamily_map_eq D hD P h hh η hη
  exact devConcl_of_map_eq hηm (fun γ _ _ => (hη₀m γ).aemeasurable) hmap (hint G η₀ hη₀m hη₀)

/-- **Reduction of Theorem 1.2** to the coordinate space. -/
theorem functional_tightness_of_internal
    (hint : ∀ (G : GSetup) (η₀ : ℝ → Coord → C(unitInterval, ℂ)), (∀ γ, Measurable (η₀ γ)) →
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂stdP, Blueprint.IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η₀ γ ω)) →
      TightConcl stdP η₀) :
    ∀ (D : ℝ → DistC → ContMetric) (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    TightConcl P η := by
  intro D hD Ω _ P _ h hh η hη
  obtain ⟨G, η₀, hη₀m, hη₀, hηm, hmap⟩ := exists_coord_geodFamily_map_eq D hD P h hh η hη
  exact tightConcl_of_map_eq hηm (fun γ _ _ => (hη₀m γ).aemeasurable) hmap (hint G η₀ hη₀m hη₀)

end SmallGammaGeodesics
