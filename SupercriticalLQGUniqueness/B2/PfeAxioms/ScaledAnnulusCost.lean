import SupercriticalLQGUniqueness.B2.LscTop.Dilate
import SupercriticalLQGUniqueness.B2.Strong.Dilate
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem acrossDist_smul_dilate
    (D : LSCMetric) (a r : Ioi (0 : ℝ)) (A : EuclideanAnnulus) :
    acrossDist (B2.LscTop.smulMetric a (B2.LscTop.dilate r D)) A =
      ENNReal.ofReal (a : ℝ) * acrossDist D (A.dilate r r.property) := by
  rw [Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale
    (B2.LscTop.dilate r D)
    (B2.LscTop.smulMetric a (B2.LscTop.dilate r D))
    (ENNReal.ofReal (a : ℝ))
    (ENNReal.ofReal_pos.mpr a.property).ne' ENNReal.ofReal_ne_top
    (fun x y => rfl) A]
  congr 1
  exact B2.Strong.acrossDist_eq_of_dilate
    (B2.LscTop.dilate r D) D r.property (fun _ _ => rfl) A

theorem aroundDist_smul_dilate
    (D : LSCMetric) (a r : Ioi (0 : ℝ)) (A : EuclideanAnnulus) :
    aroundDist (B2.LscTop.smulMetric a (B2.LscTop.dilate r D)) A =
      ENNReal.ofReal (a : ℝ) * aroundDist D (A.dilate r r.property) := by
  rw [Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale
    (B2.LscTop.dilate r D)
    (B2.LscTop.smulMetric a (B2.LscTop.dilate r D))
    (ENNReal.ofReal (a : ℝ))
    (ENNReal.ofReal_pos.mpr a.property).ne' ENNReal.ofReal_ne_top
    (fun x y => rfl) A]
  exact congrArg (ENNReal.ofReal (a : ℝ) * ·) (B2.Strong.aroundDist_eq_of_dilate
    (B2.LscTop.dilate r D) D r.property (fun _ _ => rfl) A)

end SupercriticalLQGUniqueness.B2.PfeAxioms
