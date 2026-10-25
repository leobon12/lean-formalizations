import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.TailFinite




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem lintegral_rpow_eq_tail_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X μ)
    (hfin : ∀ᵐ ω ∂μ, X ω < ∞) (p : ℝ) (hp : 0 < p) :
    (∫⁻ ω, X ω ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        μ {ω | ENNReal.ofReal t < X ω} * ENNReal.ofReal (t ^ (p - 1)) := by
  let f : Ω → ℝ := fun ω => (X ω).toReal
  have hfmeas : AEMeasurable f μ := hX.ennreal_toReal
  have hfnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
  have hreal := lintegral_rpow_eq_lintegral_meas_lt_mul μ hfnn hfmeas hp
  have hleft : (∫⁻ ω, X ω ^ p ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with ω hω
    change X ω ^ p = ENNReal.ofReal ((X ω).toReal ^ p)
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hω.ne]
  rw [hleft, hreal]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  have ht0 : 0 ≤ t := ht.le
  have hsets : {ω | t < f ω} =ᵐ[μ] {ω | ENNReal.ofReal t < X ω} :=
    hfin.mono fun ω hω => by
      change (t < (X ω).toReal) = (ENNReal.ofReal t < X ω)
      exact propext (ENNReal.ofReal_lt_iff_lt_toReal ht0 hω.ne).symm
  rw [measure_congr hsets]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
