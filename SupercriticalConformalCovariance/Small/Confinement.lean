import SupercriticalConformalCovariance.Regular.Measurability
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FirstExit.FirstExit
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.Boundary
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LoopBorel

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness
open Uniqueness.OptimalConstants.FirstExit
open Uniqueness.Toolkit.MovingEndpoints

/-- The point-to-sphere distance is already realized by paths inside its
own closed ball. -/
theorem pointSphereDist_eq_boundaryBallInf
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (u : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    TwoScale.S36Events.pointSphereDist D u ρ =
      boundaryBallInf D u ρ u := by
  rw [← TwoScale.S36.setDist_singleton_eq_pointSphereDist]
  have hu : u ∈ Metric.ball u ρ := by simpa using hρ
  have hbd := boundaryDist_eq_internalClosedBall D hL hC hu
  have hbi := boundaryBallInf_eq_internal D u ρ
    (Metric.ball_subset_closedBall hu)
  rw [hbi]
  simp only [OptimalConstants.Ratios.setDist, iInf_singleton]
  change boundaryDist D u ρ u =
    boundaryInternal D u ρ u (Metric.ball_subset_closedBall hu)
  exact hbd

/-- Every small-ball path is admissible in a larger confinement disk. -/
theorem closedBallPathInf_mono_disk (D : LSCMetric) (c : ℂ) (R : ℝ)
    (u : ℂ) (ρ : ℝ)
    (hsub : Metric.closedBall u ρ ⊆ Metric.closedBall c R) (y : ℂ) :
    closedBallPathInf D c R u y ≤ closedBallPathInf D u ρ u y := by
  unfold closedBallPathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hsmall =>
    le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le (fun t ht => hsub (hsmall t ht)) <|
      iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

/-- Point-to-sphere costs in (8) are unchanged by any confinement disk
containing the small endpoint ball. -/
theorem pointSphereDist_eq_confined_boundaryBallInf
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (c : ℂ) (R : ℝ) (u : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall u ρ ⊆ Metric.closedBall c R) :
    TwoScale.S36Events.pointSphereDist D u ρ =
      ⨅ y ∈ Metric.sphere u ρ, closedBallPathInf D c R u y := by
  rw [pointSphereDist_eq_boundaryBallInf D hL hC u hρ]
  unfold boundaryBallInf
  refine le_antisymm ?_ ?_
  · refine le_iInf fun y => le_iInf fun hy => ?_
    have hle : D (u, y) ≤ closedBallPathInf D c R u y := by
      unfold closedBallPathInf
      refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
        le_iInf fun hP => le_iInf fun _ => le_iInf fun ha =>
        le_iInf fun hb => ?_
      rw [← ha, ← hb]
      exact D.apply_le_len P hP.1
    have hamb : boundaryBallInf D u ρ u ≤ D (u, y) := by
      rw [← pointSphereDist_eq_boundaryBallInf D hL hC u hρ,
        ← TwoScale.S36.setDist_singleton_eq_pointSphereDist]
      simp only [OptimalConstants.Ratios.setDist, iInf_singleton]
      exact iInf₂_le y hy
    exact hamb.trans hle
  · refine le_iInf fun y => le_iInf fun hy => ?_
    exact (iInf₂_le y hy).trans (closedBallPathInf_mono_disk D c R u ρ hsub y)


end SupercriticalConformalCovariance.Small
