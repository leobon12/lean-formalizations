import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.Imports




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness

theorem blockShape_compact (T : Objects.CorrectedEvent.TubeData)
    (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r) :
    IsCompact (closure (Objects.Excursions.blockShape T)) := by
  exact (isCompact_closedBall (0 : ℂ) (T.rho * T.r)).closure_of_subset
    (Objects.Excursions.blockShape_subset hn hρr)

theorem block_geodesic_iff_code (T : Objects.CorrectedEvent.TubeData)
    (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r)
    (E : LSCMetric) (u v : ℂ) :
    (∃ (P : ℝ → ℂ) (a b : ℝ), E.IsCurve P a b ∧ P a = u ∧ P b = v ∧
      (∀ t ∈ Icc a b, P t ∈ closure (Objects.Excursions.blockShape T)) ∧
      E.len P a b = E (u, v)) ∧ E (u, v) < ⊤ ↔
    ∃ Q : Measurability.GeodesicCodes.Path,
      Measurability.GeodesicCodes.GeoCode (E, (Q, (u, v))) ∧
      ∀ t, Q t ∈ closure (Objects.Excursions.blockShape T) := by
  rw [← Measurability.AttainedEvents.compact_geodesic_iff_geoCode E
    (closure (Objects.Excursions.blockShape T)) (blockShape_compact T hn hρr) u v]
  simp only [OptimalConstants.Ratios.Geodesic]
  constructor
  · rintro ⟨⟨P, a, b, hcurve, hPa, hPb, htrace, hlen⟩, hfin⟩
    exact ⟨P, a, b, ⟨hcurve, hPa, hPb, hlen, hfin⟩,
      (by rintro x ⟨t, ht, hx⟩; rw [← hx]; exact htrace t ht)⟩
  · rintro ⟨P, a, b, ⟨hcurve, hPa, hPb, hlen, hfin⟩, htrace⟩
    exact ⟨⟨P, a, b, hcurve, hPa, hPb,
      (fun t ht => htrace ⟨t, ht, rfl⟩), hlen⟩, hfin⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness
