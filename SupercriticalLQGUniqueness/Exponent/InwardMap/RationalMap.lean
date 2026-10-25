import SupercriticalLQGUniqueness.Exponent.InwardMap.Separation




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def latticeCoordRat (a t : ℚ) : ℚ :=
  max (min (max (min (t+32*a) ((1-64*a)*t-64*a)) ((1+64*a)*t))
      ((1-64*a)*t+64*a))
    (t-32*a)

theorem latticeCoordRat_cast (a t : ℚ) :
    ((latticeCoordRat a t : ℚ) : ℝ) = latticeCoord (a:ℝ) (t:ℝ) := by
  unfold latticeCoordRat latticeCoord
  norm_cast

theorem inwardAxis_rational (a t : ℚ) (ha : 0 ≤ a) :
    inwardAxis (a:ℝ) (t:ℝ) =
      ((1/2 + latticeCoordRat a (t-1/2) : ℚ) : ℝ) := by
  have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  rw [inwardAxis, ← latticeCoord_eq_inwardCoord (a:ℝ) ((t:ℝ)-1/2) haR]
  push_cast
  rw [latticeCoordRat_cast]
  congr 1
  push_cast
  ring

theorem inwardMap_gaussRat (a : ℚ) (ha : 0 ≤ a) {z : ℂ}
    (hz : z ∈ LQGMetric.LFPP.gaussRat) :
    inwardMap (a:ℝ) z ∈ LQGMetric.LFPP.gaussRat := by
  rcases hz with ⟨q, rfl⟩
  let r : ℚ × ℚ :=
    (1/2 + latticeCoordRat a (q.1-1/2),
      1/2 + latticeCoordRat a (q.2-1/2))
  refine ⟨r, ?_⟩
  apply Complex.ext
  · simpa [r, inwardMap_re, Complex.add_re, Complex.mul_re] using
      (inwardAxis_rational a q.1 ha).symm
  · simpa [r, inwardMap_im, Complex.add_im, Complex.mul_im] using
      (inwardAxis_rational a q.2 ha).symm


end SupercriticalLQGUniqueness.Exponent.InwardMap
