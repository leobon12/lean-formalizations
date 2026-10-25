import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.FubiniBumpCode
import LQGMetric.Papers.GM.S1.FieldAux




 
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

theorem measure_preimage_eq_zero_of_sigma0_um
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → LQGMetric.DistC}
    (hXm : Measurable X) (hYm : Measurable Y)
    {R : LQGMetric.DistC → LQGMetric.DistC}
    (hR : Measurable[LQGMetric.GFFLaw.sigma0] R)
    (hac : μ.map (fun ω => LQGMetric.pair0 (Y ω)) ≪
      μ.map (fun ω => LQGMetric.pair0 (X ω)))
    (hRX : ∀ᵐ ω ∂μ, R (X ω) = X ω)
    (hRY : ∀ᵐ ω ∂μ, R (Y ω) = Y ω)
    {E : Set LQGMetric.DistC} (hE : LQGMetric.UMeasurableSet E)
    (h0 : μ (X ⁻¹' E) = 0) : μ (Y ⁻¹' E) = 0 := by
  let ν := μ.map X + μ.map Y
  have hEnull : NullMeasurableSet E ν := hE ν inferInstance
  let A : Set LQGMetric.DistC := toMeasurable ν E
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAE : A =ᵐ[ν] E := hEnull.toMeasurable_ae_eq
  have hAEX : A =ᵐ[μ.map X] E :=
    (ae_add_measure_iff.mp hAE).1
  have hAEY : A =ᵐ[μ.map Y] E :=
    (ae_add_measure_iff.mp hAE).2
  have hpreX : X ⁻¹' A =ᵐ[μ] X ⁻¹' E :=
    ae_of_ae_map hXm.aemeasurable hAEX
  have hpreY : Y ⁻¹' A =ᵐ[μ] Y ⁻¹' E :=
    ae_of_ae_map hYm.aemeasurable hAEY
  have h0A : μ (X ⁻¹' A) = 0 := by
    rw [measure_congr hpreX]
    exact h0
  have hYA : μ (Y ⁻¹' A) = 0 :=
    LQGMetric.GM.measure_preimage_eq_zero_of_sigma0 hR
      (LQGMetric.measurable_pair0.comp hXm)
      (LQGMetric.measurable_pair0.comp hYm)
      hac hRX hRY hAm h0A
  rw [← measure_congr hpreY]
  exact hYA

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
