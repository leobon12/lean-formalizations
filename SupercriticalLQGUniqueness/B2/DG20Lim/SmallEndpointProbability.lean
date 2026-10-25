import SupercriticalLQGUniqueness.B2.DG20Lim.PointCircleVanishing

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_exists_small_endpoint_of_arbitrarily_small_bad_prob
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ι → ℝ≥0∞) (valid : ι → Prop)
    (δ : ℝ≥0∞)
    (hnear : ∀ η : ℝ, 0 < η →
      ∃ i : ι, valid i ∧
        P {ω | δ ≤ f ω i} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∃ i : ι, valid i ∧ f ω i < δ := by
  rw [ae_iff]
  have hzero : P {ω | ¬ ∃ i : ι, valid i ∧ f ω i < δ} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    obtain ⟨i, hi, hbound⟩ := hnear (η : ℝ) hη
    have hsub : {ω | ¬ ∃ j : ι, valid j ∧ f ω j < δ} ⊆
        {ω | δ ≤ f ω i} := by
      intro ω hω
      exact le_of_not_gt (fun hlt => hω ⟨i, hi, hlt⟩)
    simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans hbound
  exact le_antisymm hzero zero_le

theorem ae_arbitrarily_small_endpoints_of_prob
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ι → ℝ≥0∞) (valid : ι → Prop)
    (hnear : ∀ δ : ℝ≥0∞, 0 < δ → ∀ η : ℝ, 0 < η →
      ∃ i : ι, valid i ∧
        P {ω | δ ≤ f ω i} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ i : ι, valid i ∧ f ω i < δ := by
  let δn : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hδn : Tendsto δn atTop (𝓝 0) := by
    simpa only [δn, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hδpos (n : ℕ) : 0 < δn n := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∃ i : ι, valid i ∧ f ω i < δn n := by
    apply ae_all_iff.mpr
    intro n
    exact ae_exists_small_endpoint_of_arbitrarily_small_bad_prob
      P f valid (δn n) (hnear (δn n) (hδpos n))
  filter_upwards [hae] with ω hω δ hδ
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hδn).2 δ hδ).exists
  obtain ⟨i, hi, hsmall⟩ := hω n
  exact ⟨i, hi, hsmall.trans hn⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
