import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet
import LQGMetric.Papers.DDDF.LenBasic
import LQGMetric.LFPP.PathOps

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_annulus_cross_le_point (ξ : ℝ) (f : ℂ → ℝ)
    (z w : ℂ) (hzw : z ≠ w) :
    let d : ℝ := dist z w
    crossLenIn ξ f (ball z d) (sphere z (d / 4)) (sphere z (d / 2)) ≤
      lfppDOn ξ f univ z w := by
  dsimp
  have hd : 0 < dist z w := dist_pos.mpr hzw
  change crossLenIn ξ f (ball z (dist z w))
      (sphere z (dist z w / 4)) (sphere z (dist z w / 2)) ≤
    ⨅ p : {p : ℝ → ℂ // IsPiecewiseC1Path p z w ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ univ}, lfppLen ξ f p.1
  apply le_iInf
  intro p
  obtain ⟨σ, τ, hσ, hστ, hτ, hσrad, hτrad, hbetween⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.crossing_extract
      (show (0 : ℝ) ≤ 1 by norm_num) p.2.1.continuousOn
      (show dist z w / 4 < dist z w / 2 by linarith)
      (by rw [p.2.1.source, dist_self]; linarith)
      (by
        rw [p.2.1.target]
        rw [dist_comm w z]
        linarith)
  have hpath : IsPiecewiseC1Path (subPath p.1 σ τ) (p.1 σ) (p.1 τ) :=
    isPiecewiseC1Path_subPath p.2.1 hσ hστ hτ
  have hadm : AdmPath (ball z (dist z w))
      (sphere z (dist z w / 4)) (sphere z (dist z w / 2))
      (subPath p.1 σ τ) := by
    refine ⟨p.1 σ, mem_sphere.mpr (by simpa only [dist_comm z (p.1 σ)] using hσrad),
      p.1 τ, mem_sphere.mpr (by simpa only [dist_comm z (p.1 τ)] using hτrad), hpath, ?_⟩
    intro u hu
    have hv : (τ - σ) * u + σ ∈ Icc σ τ := by
      constructor <;> nlinarith [hu.1, hu.2, hστ]
    have hr := (hbetween _ hv).2
    change dist (p.1 ((τ - σ) * u + σ)) z ≤ dist z w / 2 at hr
    simp only [subPath]
    apply mem_ball.mpr
    have hr' : dist z (p.1 ((τ - σ) * u + σ)) ≤ dist z w / 2 := by
      simpa only [dist_comm] using hr
    linarith
  calc
    crossLenIn ξ f (ball z (dist z w))
      (sphere z (dist z w / 4)) (sphere z (dist z w / 2)) ≤
        lfppLen ξ f (subPath p.1 σ τ) := crossLenIn_le_lfppLen hadm
    _ ≤ lfppLen ξ f p.1 := by
      rw [lfppLen_subPath p.1 hστ, lfppLen_eq]
      exact lintegral_mono_set (Icc_subset_Icc hσ hτ)

end SupercriticalLQGUniqueness.B2.DG20Pt
