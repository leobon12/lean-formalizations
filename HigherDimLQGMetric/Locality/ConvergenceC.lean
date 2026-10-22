import HigherDimLQGMetric.Locality.StageScaled
import HigherDimLQGMetric.Metric.WeylMetric

/-! Compact-ball convergence of truncated LFPP distances as convergence
of continuous metric coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_tendsto_truncScaledMetric_of_balls {d : ℕ}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : ℕ → DistRd d) (D : ContMetric d)
    (hballs : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (g n)) p)
        ⇑D.1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) :
    Tendsto (fun n => (l7a_truncScaledMetric hd κ hκ ξ (hεs n) (g n)).1)
      atTop (𝓝 D.1) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall
    (0 : Rd d × Rd d)
  let R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : K ⊆ closedBall (0 : Rd d) R' ×ˢ
      closedBall (0 : Rd d) R' := by
    intro p hp
    have hp' := hKR hp
    rw [mem_closedBall, dist_zero_right] at hp'
    have hcoord := max_le_iff.mp (show max ‖p.1‖ ‖p.2‖ ≤ R by
      simpa only [Prod.norm_def] using hp')
    refine ⟨mem_closedBall.mpr ?_, mem_closedBall.mpr ?_⟩
    · simpa only [dist_zero_right] using
        hcoord.1.trans (le_max_left R 1)
    · simpa only [dist_zero_right] using
        hcoord.2.trans (le_max_left R 1)
  have ht := (hballs R' hR').mono hsub
  convert ht using 1
  ext n p
  exact l7a_truncScaledMetric_apply hd κ hκ ξ (hεs n) (g n) p

theorem l7a_tendsto_truncScaledMetric_weyl_of_balls {d : ℕ}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : ℕ → DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (f : C(Rd d, ℝ))
    (hballs : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (g n)) p)
        (fun p => (weylScale ξ f D p.1 p.2).toReal) atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) :
    Tendsto (fun n => (l7a_truncScaledMetric hd κ hκ ξ (hεs n) (g n)).1)
      atTop (𝓝 (weylMetric ξ f D hD).1) := by
  apply l7a_tendsto_truncScaledMetric_of_balls hd κ hκ ξ εs hεs g
    (weylMetric ξ f D hD)
  intro R hR
  convert hballs R hR using 1
  ext p
  exact (weylMetric_apply hD p).symm

end HigherDimLQGMetric
