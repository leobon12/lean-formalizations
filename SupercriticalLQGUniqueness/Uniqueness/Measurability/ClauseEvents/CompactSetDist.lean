import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.OpenClosedSetDist




set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

 
theorem measurable_setDist_compact (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    Measurable (fun D : LSCMetric => OptimalConstants.Ratios.setDist D K₁ K₂) := by
  have hK : IsCompact (K₁ ×ˢ K₂) := hK₁.prod hK₂
  simpa only [OptimalConstants.Ratios.setDist_eq_iInf_prod] using
    LSCMetric.measurable_iInf_of_isCompact hK

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
