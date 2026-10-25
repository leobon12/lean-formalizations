import SupercriticalLQGUniqueness.Exponent.PolygonalCost.Basic




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def inwardCoord (a t : ℝ) : ℝ :=
  if t ≤ -(3/2 : ℝ) then t + 32*a
  else if t ≤ -(1/2 : ℝ) then -(1/2 : ℝ) - 32*a + (1-64*a)*(t+1/2)
  else if t ≤ (1/2 : ℝ) then (1+64*a)*t
  else if t ≤ (3/2 : ℝ) then (1/2 : ℝ)+32*a+(1-64*a)*(t-1/2)
  else t-32*a

 
def inwardMap (a : ℝ) (z : ℂ) : ℂ :=
  Complex.mk (1/2 + inwardCoord a (z.re-1/2))
    (1/2 + inwardCoord a (z.im-1/2))

theorem inwardCoord_neg_three_halves (a : ℝ) :
    inwardCoord a (-(3/2 : ℝ)) = -(3/2 : ℝ) + 32*a := by
  simp [inwardCoord]

theorem inwardCoord_neg_half (a : ℝ) :
    inwardCoord a (-(1/2 : ℝ)) = -(1/2 : ℝ) - 32*a := by
  norm_num [inwardCoord]

theorem inwardCoord_half (a : ℝ) :
    inwardCoord a (1/2 : ℝ) = (1/2 : ℝ) + 32*a := by
  norm_num [inwardCoord]
  ring

theorem inwardCoord_three_halves (a : ℝ) :
    inwardCoord a (3/2 : ℝ) = (3/2 : ℝ) - 32*a := by
  norm_num [inwardCoord]
  ring


end SupercriticalLQGUniqueness.Exponent.InwardMap
