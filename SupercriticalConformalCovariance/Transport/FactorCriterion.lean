import SupercriticalConformalCovariance.Transport.ConfinedIndependence
import LQGMetric.Prob.CondCopies
import SupercriticalLQGUniqueness.B2.LscTop.Compact
import LQGMetric.Field.StandardBorelRange

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace

namespace SupercriticalConformalCovariance.Transport

/-- A measurable statistic of realization data is field-determined when its conditional copy
agrees a.s. with the original. -/
theorem ae_determined_of_data_copy_eq {Ω α β γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → α) (Y : Ω → β) (Z : β → γ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (heq : (fun p : Ω × β => Z (Y p.1)) =ᵐ[LQGMetric.condCopyMeasure Y X P hX]
      (fun p => Z p.2)) : LQGMetric.AEDeterminedBy (fun ω => Z (Y ω)) X P := by
  let ν := LQGMetric.condCopyMeasure Y X P hX
  have hind : LQGMetric.CondIndepEv
      ((inferInstance : MeasurableSpace α).comap (fun p : Ω × β => X p.1))
      ((inferInstance : MeasurableSpace γ).comap (fun p : Ω × β => Z (Y p.1)))
      ((inferInstance : MeasurableSpace γ).comap (fun p : Ω × β => Z p.2)) ν := by
    refine (LQGMetric.condIndepEv_condCopy hX hY).mono ?_ ?_
    · rw [show (fun p : Ω × β => Z (Y p.1)) = Z ∘ (fun p => Y p.1) from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hZ.comap_le
    · rw [show (fun p : Ω × β => Z p.2) = Z ∘ Prod.snd from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hZ.comap_le
  obtain ⟨F, hF, hFae⟩ := LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq
    (hX.comp measurable_fst) ((hZ.comp hY).comp measurable_fst) hind heq
  refine ⟨F, hF, ?_⟩
  change (Z ∘ Y) =ᵐ[P] F ∘ X
  rw [Filter.EventuallyEq, ← LQGMetric.condCopyMeasure_fst (Y := Y) (μ := P) hX,
    ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun (hZ.comp hY) (hF.comp hX))]
  exact hFae

end SupercriticalConformalCovariance.Transport
