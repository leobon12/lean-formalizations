import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPNeighborhood
import LQGMetric.LFPP.WeylUpper

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_near_minimal_lfpp_path_in_ball
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {x y : ℂ} {r m δ : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m)
    (hmE : ∀ u ∈ Metric.closedBall x r, m ≤ Real.exp (ξ * φ u))
    (hδ : 0 < δ)
    (hsmall : lfppD ξ φ x y + ENNReal.ofReal δ ≤
      ENNReal.ofReal (m * r)) :
    ∃ P : ℝ → ℂ, IsPiecewiseC1Path P x y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Metric.closedBall x r) ∧
      lfppLen ξ φ P < lfppD ξ φ x y + ENNReal.ofReal δ := by
  have hlt : lfppD ξ φ x y < lfppD ξ φ x y + ENNReal.ofReal δ :=
    ENNReal.lt_add_right (lfppD_ne_top hφ x y) (by simpa using hδ)
  obtain ⟨P', hPlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, hP, _⟩ := P'
  change lfppLen ξ φ P < _ at hPlt
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Metric.closedBall x r := by
    intro t ht
    by_contra hout
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hout
    have ht0 : 0 < t := by
      rcases ht.1.lt_or_eq with h | h
      · exact h
      · rw [← h, hP.source, sub_self, norm_zero] at hout
        linarith
    have h1 := le_lfppLen_of_path (ξ := ξ) (φ := φ)
      (isPiecewiseC1Path_subPath hP le_rfl ht0 ht.2) hr hm
      (by rw [hP.source]; exact hmE)
    rw [lfppLen_subPath P ht0, hP.source, min_eq_left hout.le] at h1
    have h2 : ∫⁻ s in Icc 0 t, lenDens ξ φ P s ≤ lfppLen ξ φ P :=
      lintegral_mono_set (Icc_subset_Icc le_rfl ht.2)
    exact absurd ((h1.trans h2).trans_lt (hPlt.trans_le hsmall))
      (lt_irrefl _)
  exact ⟨P, hP, hin, hPlt⟩

theorem lfppDOn_lt_global_add_of_ball
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {U : Set ℂ} {x y : ℂ} {r m δ : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m)
    (hmE : ∀ u ∈ Metric.closedBall x r, m ≤ Real.exp (ξ * φ u))
    (hball : Metric.closedBall x r ⊆ U)
    (hδ : 0 < δ)
    (hsmall : lfppD ξ φ x y + ENNReal.ofReal δ ≤
      ENNReal.ofReal (m * r)) :
    lfppDOn ξ φ U x y < lfppD ξ φ x y + ENNReal.ofReal δ := by
  obtain ⟨P, hP, hin, hcost⟩ :=
    exists_near_minimal_lfpp_path_in_ball hφ hr hm hmE hδ hsmall
  exact (lfppDOn_le hP (fun t ht => hball (hin t ht))).trans_lt hcost

end SupercriticalLQGUniqueness.B2.PfeAxioms
