import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPolygonApprox
import Mathlib.Topology.MetricSpace.Thickening

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP
open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 


theorem laneC_polygon_mem_of_segments
    {A : Set ℂ} {v : ℕ → ℂ} {N : ℕ} (hv0 : v 0 ∈ A)
    (hseg : ∀ i < N, ∀ u ∈ Icc (0 : ℝ) 1,
      segPath (v i) (v (i + 1)) u ∈ A) :
    ∀ u ∈ Icc (0 : ℝ) 1, polygonPath v N u ∈ A := by
  induction N with
  | zero =>
    intro u hu
    simpa [polygonPath] using hv0
  | succ N ih =>
    have hsegN : ∀ i < N, ∀ u ∈ Icc (0 : ℝ) 1,
        segPath (v i) (v (i + 1)) u ∈ A := by
      intro i hi
      exact hseg i (hi.trans (Nat.lt_succ_self N))
    have hsegLast := hseg N (Nat.lt_succ_self N)
    intro u hu
    change concatPath (polygonPath v N) (segPath (v N) (v (N + 1))) u ∈ A
    unfold concatPath
    split_ifs with h
    · simpa only [add_zero] using
        ih hsegN (2 * u) ⟨by linarith [hu.1], by linarith⟩
    · exact hsegLast (2 * u - 1)
        ⟨by linarith [not_le.mp h], by linarith [hu.2]⟩

 


theorem laneC_exists_polygon_in_open_cost_le
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {A : Set ℂ} (hA : IsOpen A)
    (hPA : ∀ u ∈ Icc (0 : ℝ) 1, P u ∈ A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ → ℂ,
      IsPiecewiseC1Path γ (P 0) (P 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ A) ∧
      lfppLen ξ φ γ ≤
        ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P 0 1 := by
  let K : Set ℂ := P '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hP
  have hKA : K ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hPA u hu
  obtain ⟨d, hd, hdA⟩ := hK.exists_cthickening_subset_open hA hKA
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR : 0 ≤ R := by
    have h0 := hKR (show P 0 ∈ K from ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
    exact (dist_nonneg : 0 ≤ dist (P 0) (0 : ℂ)).trans h0
  obtain ⟨N, t, ht0, ht1, htmono, htmem, hstep, hpoly, hcost⟩ :=
    laneC_exists_polygon_cost_le_continuous_length
      (ξ := ξ) hφ hP hR hδ hd (fun u hu => hKR ⟨u, hu, rfl⟩)
  let γ := polygonPath (fun i => P (t i)) N
  refine ⟨γ, hpoly, ?_, hcost⟩
  apply laneC_polygon_mem_of_segments
  · simpa only [ht0] using hPA 0 ⟨le_rfl, zero_le_one⟩
  · intro i hi u hu
    have hcenter : P (t i) ∈ K := ⟨t i, htmem i hi.le, rfl⟩
    have hdist : dist (segPath (P (t i)) (P (t (i + 1))) u) (P (t i)) ≤ d := by
      exact (segPath_mem_closedBall _ _ hu).trans (by
        simpa [dist_eq_norm] using hstep i hi)
    exact hdA (Metric.mem_cthickening_of_dist_le _ _ d K hcenter hdist)

end SupercriticalLQGUniqueness.B2.DG20Conc
