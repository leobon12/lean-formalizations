import SupercriticalLQGUniqueness.B2.Median.BarrierLimit

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

theorem exists_lfpp_path_of_scaled_setDistance_lt
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (O₁ O₂ : Set ℂ) {L : ℝ≥0∞}
    (hL : ENNReal.ofReal ((a : ℝ)⁻¹) *
      B2.Iface.setDistance (lfppDistance ξ φ) O₁ O₂ < L) :
    ∃ z ∈ O₁, ∃ w ∈ O₂, ∃ P : ℝ → ℂ,
      LQGMetric.IsPiecewiseC1Path P z w ∧
      ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.lfppLen ξ φ P < L := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  change c * B2.Iface.setDistance (lfppDistance ξ φ) O₁ O₂ < L at hL
  unfold B2.Iface.setDistance at hL
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop, iInf_lt_iff] at hL
  obtain ⟨z, hz, w, hw, hzw⟩ := hL
  rw [B2.LscTop.lfppDistance_eq_lfppD] at hzw
  change c * LQGMetric.LFPP.lfppDOn ξ φ univ z w < L at hzw
  unfold LQGMetric.LFPP.lfppDOn at hzw
  rw [ENNReal.mul_iInf_of_ne hc0 hcTop] at hzw
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp hzw
  exact ⟨z, hz, w, hw, P.1, P.2.1, hP⟩

 



theorem eventually_crossing_lt_of_barrier
    (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ))
    (φ F : ℕ → C(ℂ, ℝ)) (O₁ O₂ : Set ℂ)
    (T W L : ℝ≥0∞)
    (hbar : ∀ᶠ n in atTop, ∀ (P : ℝ → ℂ) (z w : ℂ),
      LQGMetric.IsPiecewiseC1Path P z w → z ∈ O₁ → w ∈ O₂ →
      ENNReal.ofReal ((a n : ℝ)⁻¹) * LQGMetric.lfppLen ξ (F n) P < T →
      ENNReal.ofReal ((a n : ℝ)⁻¹) * lfppCrossingLength ξ (φ n) ≤
        ENNReal.ofReal ((a n : ℝ)⁻¹) * LQGMetric.lfppLen ξ (F n) P)
    (hlim : Tendsto (fun n => ENNReal.ofReal ((a n : ℝ)⁻¹) *
      B2.Iface.setDistance (lfppDistance ξ (F n)) O₁ O₂) atTop (𝓝 W))
    (hWL : W < L) (hLT : L ≤ T) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal ((a n : ℝ)⁻¹) * lfppCrossingLength ξ (φ n) < L := by
  have hnear : ∀ᶠ n in atTop,
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        B2.Iface.setDistance (lfppDistance ξ (F n)) O₁ O₂ < L :=
    hlim.eventually (isOpen_Iio.mem_nhds hWL)
  filter_upwards [hbar, hnear] with n hn hnear_n
  obtain ⟨z, hz, w, hw, P, hP, hcost⟩ :=
    exists_lfpp_path_of_scaled_setDistance_lt ξ (a n) (F n) O₁ O₂ hnear_n
  exact (hn P z w hP hz hw (hcost.trans_le hLT)).trans_lt hcost

end SupercriticalLQGUniqueness.B2.Median
