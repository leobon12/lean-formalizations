import SupercriticalLQGUniqueness.B2.DG20Lim.SmallEndpointProbability

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_exists_large_endpoint_of_arbitrarily_small_bad_prob
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ι → ℝ≥0∞) (valid : ι → Prop)
    (δ : ℝ≥0∞)
    (hnear : ∀ η : ℝ, 0 < η →
      ∃ i : ι, valid i ∧
        P {ω | f ω i < δ} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∃ i : ι, valid i ∧ δ ≤ f ω i := by
  rw [ae_iff]
  have hzero : P {ω | ¬ ∃ i : ι, valid i ∧ δ ≤ f ω i} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    obtain ⟨i, hi, hbound⟩ := hnear (η : ℝ) hη
    have hsub : {ω | ¬ ∃ j : ι, valid j ∧ δ ≤ f ω j} ⊆
        {ω | f ω i < δ} := by
      intro ω hω
      exact lt_of_not_ge (fun hge => hω ⟨i, hi, hge⟩)
    simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans hbound
  exact le_antisymm hzero zero_le

end SupercriticalLQGUniqueness.B2.DG20Lim
