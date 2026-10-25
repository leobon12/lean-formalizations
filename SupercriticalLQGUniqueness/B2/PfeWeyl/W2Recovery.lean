import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Segment
import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Chain
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1GammaLiminf
import SupercriticalLQGUniqueness.B2.PfeWeyl.AroundWeylBound
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSkeleton
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaBudgetFin
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSelect
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open PfeAxioms

 
theorem smallAnnulusCosts_mono_right {G : ℕ → LSCMetric} {D : LSCMetric}
    {K' K'' K''' : Set ℂ} (h : SmallAnnulusCosts G D K' K'') (hK : K'' ⊆ K''') :
    SmallAnnulusCosts G D K' K''' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := h z hz hns δ hδ ρ hρ
  exact ⟨A, h1, h2, h3, h4.trans hK, h5⟩

 
theorem ofReal_exp_shift3 (ξ a θ : ℝ) :
    ENNReal.ofReal (Real.exp (ξ * (a + θ + θ))) =
      ENNReal.ofReal (Real.exp (3 * ξ * θ)) * ENNReal.ofReal (Real.exp (ξ * (a - θ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

 


theorem select_eventual_traces {E : ℕ → LSCMetric} {V : Set ℂ} {ι : Type*}
    (good : (n : ℕ) → ι → BufferedMetricTrace (E n) V → Prop)
    (dflt : (n : ℕ) → ι → BufferedMetricTrace (E n) V)
    (h : ∀ i, ∀ᶠ n in atTop, ∃ T, good n i T) :
    ∃ P : (n : ℕ) → ι → BufferedMetricTrace (E n) V,
      ∀ i, ∀ᶠ n in atTop, good n i (P n i) := by
  classical
  refine ⟨fun n i => if hT : ∃ T, good n i T then hT.choose else dflt n i,
    fun i => ?_⟩
  filter_upwards [h i] with n hn
  split
  · next hT => exact hT.choose_spec
  · next hT => exact absurd hn hT

 


theorem exists_recovery_scales (D : LSCMetric) (f : C(ℂ, ℝ)) {K₀ : Set ℂ}
    (hK₀ : IsCompact K₀) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ≥0∞, 0 < c ∧
      (∀ a ∈ K₀, ∀ x ∈ Metric.closedBall a ρ, f x ≤ f a + θ) ∧
      ∀ a ∈ K₀, ∀ hρ : 0 < ρ, c ≤ acrossDist D (halfAnnulus a ρ hρ) := by
  have hK₁ : IsCompact (Metric.cthickening 1 K₀) := hK₀.cthickening
  obtain ⟨ρ₀, hρ₀, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK₁.uniformContinuousOn_of_continuous f.continuous.continuousOn) θ hθ
  set ρ : ℝ := min (ρ₀ / 2) 1 with hρdef
  have hρ : 0 < ρ := lt_min (half_pos hρ₀) one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρρ₀ : ρ < ρ₀ := (min_le_left _ _).trans_lt (half_lt_self hρ₀)
  let C : Set ℂ := Metric.cthickening ρ K₀
  let S : Set (ℂ × ℂ) := (C ×ˢ C) ∩ {p | ρ / 2 ≤ dist p.1 p.2}
  have hS : IsCompact S := by
    have hc : IsCompact C := hK₀.cthickening
    exact (hc.prod hc).inter_right
      (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  have hoff : ∀ p ∈ S, p.1 ≠ p.2 := by
    intro p hp heq
    have h2 : ρ / 2 ≤ dist p.1 p.2 := hp.2
    rw [heq, dist_self] at h2
    linarith
  refine ⟨ρ, hρ, ⨅ p ∈ S, D p, compact_offDiag_pos D hS hoff, ?_, ?_⟩
  · intro a ha x hx
    have hxK : x ∈ Metric.cthickening 1 K₀ :=
      Metric.mem_cthickening_of_dist_le x a 1 K₀ ha ((Metric.mem_closedBall.1 hx).trans hρ1)
    have haK : a ∈ Metric.cthickening 1 K₀ := Metric.self_subset_cthickening K₀ ha
    have h := hunif x hxK a haK ((Metric.mem_closedBall.1 hx).trans_lt hρρ₀)
    rw [Real.dist_eq] at h
    linarith [(abs_lt.1 h).2]
  · intro a ha hρ'
    rw [acrossDist_eq_iInf_prod]
    refine le_iInf₂ fun p hp => iInf₂_le p ⟨⟨?_, ?_⟩, ?_⟩
    · exact Metric.mem_cthickening_of_dist_le _ a ρ K₀ ha (by
        have : dist p.1 a = ρ / 2 := hp.1
        linarith)
    · exact Metric.mem_cthickening_of_dist_le _ a ρ K₀ ha (le_of_eq hp.2)
    · show ρ / 2 ≤ dist p.1 p.2
      have h1 : dist p.1 a = ρ / 2 := hp.1
      have h2 : dist p.2 a = ρ := hp.2
      have := dist_triangle p.2 p.1 a
      rw [dist_comm p.2 p.1] at this
      linarith

end SupercriticalLQGUniqueness.B2.PfeWeyl
