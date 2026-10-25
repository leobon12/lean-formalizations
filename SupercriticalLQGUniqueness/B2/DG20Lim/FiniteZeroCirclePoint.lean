import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordEmbedding

 


set_option autoImplicit false
noncomputable section

open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finiteCircleCoords_zero_zero (D : ContMetric)
    (Z W : RatCircle) (hZ : Z.radius = 0) (hW : W.radius = 0) :
    finiteCircleCoords D (Z, W) = edist (D.pt Z.center) (D.pt W.center) := by
  rw [finiteCircleCoords, Z.toSet_eq_singleton_of_radius_zero hZ,
    W.toSet_eq_singleton_of_radius_zero hW, LQGMetric.GM.setDist_eq_iInf]
  simp only [iInf_singleton]
  rw [ContMetric.edist_pt]

end SupercriticalLQGUniqueness.B2.DG20Lim
