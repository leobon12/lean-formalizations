import SupercriticalLQGUniqueness.B2.Strong.Tight

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem isTwoSidedTight_const_of_ae_pos_finite
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    (hZ : AEMeasurable Z P)
    (hpos : ∀ᵐ ω ∂P, 0 < Z ω)
    (hfin : ∀ᵐ ω ∂P, Z ω < ∞) :
    IsTwoSidedTight P (fun (_ : ι) => Z) := by
  refine ⟨fun _ => hZ, fun ε hε => ?_⟩
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have e₁ := (tendsto_order.1
    (B2.Strong.tendsto_measure_lt_natCast P Z hZ hfin)).2 _ hε'
  have e₂ := (tendsto_order.1
    (B2.Strong.tendsto_measure_lt_inv_natCast P Z hZ hpos)).2 _ hε'
  obtain ⟨n, ⟨hn₁, hn₂⟩, hnpos⟩ :=
    ((e₁.and e₂).and (eventually_ge_atTop 1)).exists
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  refine ⟨n, hnreal, fun _ => ⟨?_, ?_⟩⟩
  · simpa [ENNReal.ofReal_natCast] using hn₁.le
  · have heq : ENNReal.ofReal (n : ℝ)⁻¹ = (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hnreal, ENNReal.ofReal_natCast]
    simpa only [heq] using hn₂.le

end SupercriticalLQGUniqueness.B2.PfeAxioms
