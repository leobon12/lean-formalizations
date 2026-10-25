import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.AroundFinite
import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.FiniteTraceChain




 





set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

open LQGMetric (DistC)

private def annulusAt (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : EuclideanAnnulus :=
  ⟨(z, ρ, 2 * ρ), hρ, by linarith⟩

 
theorem ae_finite_around_chain
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (c : ℕ → ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂μ, ∀ i : ℕ, aroundDist (D (h ω))
      (annulusAt (c i) ρ hρ) < ⊤ := by
  rw [ae_all_iff]
  intro i
  exact ae_aroundDist_lt_top hD μ h hh (annulusAt (c i) ρ hρ)

 
theorem trace_pathConnected (d : LSCMetric) (A : EuclideanAnnulus)
    (P : ℝ → ℂ) (a b : ℝ) (hP : d.IsCurve P a b)
    (hA : ∀ t ∈ Icc a b, P t ∈ A.toSet) :
    IsPathConnected (P '' Icc a b) := by
  have hbounded : Bornology.IsBounded (P '' Icc a b) := by
    apply (Metric.isBounded_ball (x := A.center) (r := A.outerRadius)).subset
    rintro x ⟨t, ht, rfl⟩
    exact (hA t ht).1
  have hcont := Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded d P hP hbounded
  exact (convex_Icc a b).isPathConnected
    ⟨a, left_mem_Icc.mpr hP.1⟩ |>.image' hcont

 

theorem setDist_closedBalls_lt_top_of_annular_chain
    (d : LSCMetric) (n : ℕ) (c : ℕ → ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℂ) (hu : ‖u‖ = 1)
    (hstep : ∀ i < n, c (i + 1) = c i + (3 / 2 * ρ) • u)
    (r₁ r₂ : ℝ) (hr₁ : 2 * ρ < r₁) (hr₂ : 2 * ρ < r₂)
    (hfinite : ∀ i, aroundDist d (annulusAt (c i) ρ hρ) < ⊤) :
    OptimalConstants.Ratios.setDist d (Metric.closedBall (c 0) r₁)
      (Metric.closedBall (c n) r₂) < ⊤ := by
  have hwitness (i : ℕ) : ∃ (P : ℝ → ℂ) (a b : ℝ),
      d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ (annulusAt (c i) ρ hρ).toSet) ∧
      Disconnects (P '' Icc a b)
        (annulusAt (c i) ρ hρ).innerBoundary
        (annulusAt (c i) ρ hρ).outerBoundary ∧
      d.len P a b < ⊤ := by
    exact aroundDist_exists_finite_trace d _ (hfinite i)
  choose P a b hP hA hdisc hlen using hwitness
  have hmeet (i : ℕ) (hi : i < n) :
      ((P i '' Icc (a i) (b i)) ∩
       (P (i + 1) '' Icc (a (i + 1)) (b (i + 1)))).Nonempty := by
    have hdc : LQGMetric.Disconnects (P i '' Icc (a i) (b i))
        (Metric.sphere (c i) ρ) (Metric.sphere (c i) (2 * ρ)) := by
      exact Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit (by
        simpa [annulusAt, EuclideanAnnulus.innerBoundary,
          EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
          EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]
          using hdisc i)
    have hdc' : LQGMetric.Disconnects
        (P (i + 1) '' Icc (a (i + 1)) (b (i + 1)))
        (Metric.sphere (c i + (3 / 2 * ρ) • u) ρ)
        (Metric.sphere (c i + (3 / 2 * ρ) • u) (2 * ρ)) := by
      rw [← hstep i hi]
      exact Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit (by
        simpa [annulusAt, EuclideanAnnulus.innerBoundary,
          EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
          EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]
          using hdisc (i + 1))
    exact neighboring_separators_intersect hρ hu hdc hdc'
      (trace_pathConnected d _ (P (i + 1)) (a (i + 1)) (b (i + 1))
        (hP (i + 1)) (hA (i + 1)))
  have hfirst : (Metric.closedBall (c 0) r₁ ∩
      (P 0 '' Icc (a 0) (b 0))).Nonempty := by
    refine ⟨P 0 (a 0), ?_, ⟨a 0, left_mem_Icc.mpr (hP 0).1, rfl⟩⟩
    have hrad := ((hA 0 (a 0) (left_mem_Icc.mpr (hP 0).1)).1)
    exact (Metric.mem_closedBall).2 (le_of_lt (lt_trans hrad hr₁))
  have hlast : (Metric.closedBall (c n) r₂ ∩
      (P n '' Icc (a n) (b n))).Nonempty := by
    refine ⟨P n (a n), ?_, ⟨a n, left_mem_Icc.mpr (hP n).1, rfl⟩⟩
    have hrad := ((hA n (a n) (left_mem_Icc.mpr (hP n).1)).1)
    exact (Metric.mem_closedBall).2 (le_of_lt (lt_trans hrad hr₂))
  exact setDist_lt_top_of_finite_trace_chain d n P a b
    (fun i hi => hlen i) hmeet _ _ hfirst hlast

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls
