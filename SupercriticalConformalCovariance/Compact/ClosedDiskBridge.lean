import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.MovingBall

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
namespace SupercriticalConformalCovariance.Compact
open SupercriticalLQGUniqueness

/-- The intrinsic distance in a fixed closed disk, extended by infinity outside,
is lower semicontinuous on the full plane squared. -/
theorem closed_disk_intrinsic_lsc (D : LSCMetric) (c : ℂ) (R : ℝ) :
    LowerSemicontinuous (fun p : ℂ × ℂ =>
      Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf D c R p.1 p.2) := by
  have h := Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf_joint_lsc
  have hc : Continuous (fun p : ℂ × ℂ => (D, (c, (R, p)))) :=
    continuous_const.prodMk
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  change LowerSemicontinuous
    ((fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
      Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
      (fun p : ℂ × ℂ => (D, (c, (R, p)))))
  exact h.comp hc

end SupercriticalConformalCovariance.Compact
