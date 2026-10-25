import LQGMetric.Topo.Disconnect

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric

theorem laneC_exists_around_witness_of_lt
    (D : ContMetric) (A E F : Set ℂ) {M : ℝ≥0∞}
    (hM : D.aroundDist A E F < M) :
    ∃ a b : ℝ, ∃ P : ℝ → ℂ,
      a ≤ b ∧ ContinuousOn P (Icc a b) ∧
      P '' Icc a b ⊆ A ∧ Disconnects (P '' Icc a b) E F ∧
        D.len P a b < M := by
  unfold ContMetric.aroundDist at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨a, b, P, hab, hcont, hcar, hsep, hlen⟩ := hM
  exact ⟨a, b, P, hab, hcont, hcar, hsep, hlen⟩

theorem laneC_exists_around_witness_with_slack
    (D : ContMetric) (A E F : Set ℂ)
    (hfin : D.aroundDist A E F ≠ ⊤)
    {η : ℝ} (hη : 0 < η) :
    ∃ a b : ℝ, ∃ P : ℝ → ℂ,
      a ≤ b ∧ ContinuousOn P (Icc a b) ∧
      P '' Icc a b ⊆ A ∧ Disconnects (P '' Icc a b) E F ∧
        D.len P a b < D.aroundDist A E F + ENNReal.ofReal η := by
  exact laneC_exists_around_witness_of_lt D A E F
    (ENNReal.lt_add_right hfin (by simpa using hη))

end SupercriticalLQGUniqueness.B2.DG20Conc
